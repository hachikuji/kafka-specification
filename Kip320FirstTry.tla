--------------------------- MODULE Kip320FirstTry ---------------------------

EXTENDS Kip279

(***************************************************************************)
(* We failed to fence fetch requests properly, which led to KIP-320. 
 *)

(**
 * A follower is considered caught up to a particular offset if the epoch of 
 * the record at the previous offset is the same as what the leader has for
 * the same offset.
 *) 
IsFollowerCaughtUpToLeaderEpoch(leader, follower, endOffset) ==
    /\ ReplicaPresumesLeadership(leader)
    /\ ReplicaIsFollowing(follower, leader) 
    /\  \/ endOffset = 0
        \/  /\ endOffset > 0 
            /\ LET offset == endOffset - 1 IN \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(leader, record, offset)
                /\ ReplicaLog!HasOffset(follower, offset)
                /\ ReplicaLog!GetRecordAtOffset(follower, offset).epoch = record.epoch 

(**
 * A follower needs truncation if its end offset is ahead of the leader, or if the
 * epoch of the latest record does not match the record with the same offset on the
 * leader.
 *)
FollowerNeedsTruncation(follower, leader) ==
    \/ ReplicaLog!GetEndOffset(follower) > ReplicaLog!GetEndOffset(leader)
    \/ \E record \in LogRecords, offset \in ReplicaLog!Offsets : 
       /\ ReplicaLog!IsLatestEntry(follower, record, offset)
       /\ ReplicaLog!HasOffset(leader, offset)
       /\ ReplicaLog!GetRecordAtOffset(leader, offset).epoch # record.epoch

(**
 * Following KIP-320, truncation is possible at any time if the follower finds that
 * the epoch of its last appended entry does not match the same entry on the leader.
 *)
FollowerTruncate == \E leader, follower \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ ReplicaIsFollowing(follower, leader)
    /\ FollowerNeedsTruncation(follower, leader)
    /\ LET truncationOffset == FirstNonMatchingOffsetFromTail(leader, follower) 
       IN  /\ ReplicaLog!TruncateTo(follower, truncationOffset)
           /\ replicaState' = [replicaState EXCEPT ![follower].hw = Min({truncationOffset, @})]
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * Following KIP-320, we are smarter about incrementing the high watermark. If
 * all replicas in the ISR acknowledge the leader and have matching epochs for 
 * the entry at the current high watermark, then we can increment. The leader
 * is able to verify the epoch of this record when the replica sends a fetch.
 *)
ImprovedLeaderIncHighWatermark == \E leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ LET leaderHw == replicaState[leader].hw 
       IN \E record \in LogRecords : 
        /\ ReplicaLog!HasEntry(leader, record, leaderHw)
        /\ \A follower \in replicaState[leader].isr : IsFollowerCaughtUpToLeaderEpoch(leader, follower, leaderHw + 1)      
    /\ replicaState' = [replicaState EXCEPT ![leader].hw = @ + 1]
    /\ UNCHANGED <<nextRecordId, replicaLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * This is KIP-320 fetch behavior. Note the stronger fencing. We can only replicate
 * if the epoch at the end of the log is correct.
 *)
FollowerFetch == \E follower, leader \in Replicas :
    LET followerEndOffset == ReplicaLog!GetEndOffset(follower)
    IN  /\ IsFollowerCaughtUpToLeaderEpoch(leader, follower, followerEndOffset)
        /\ ReplicaLog!ReplicateTo(leader, follower)
        /\ LET  newEndOffset == followerEndOffset + 1
                leaderHw == replicaState[leader].hw
                followerHw == Min({leaderHw, newEndOffset}) 
           IN   replicaState' = [replicaState EXCEPT ![follower].hw = followerHw]
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * This is a bug that was found while checking this model. When a follower
 * becomes leader, its high watermark is typically behind the leader. Since 
 * it does not know what the true high watermark was at the time the leader
 * failed (or shutdown), it must be conservative when adding new members to
 * the ISR. We can be assured that all members of the current ISR have 
 * replicated up to whatever the leader's high watermark was, but it is not 
 * safe to assume the same for new replicas until they have replicated ALL
 * of the messages from the previous leader. In other words, we need to wait
 * until it has at least replicated up to the start of the its own leader epoch.
 *)
HasFollowerReachedLeaderEpoch(leader, follower, followerEndOffset) ==
    \/ followerEndOffset = ReplicaLog!GetEndOffset(leader)
    \/ \E endRecord \in LogRecords :
        /\ ReplicaLog!HasEntry(leader, endRecord, followerEndOffset)
        /\ ReplicaLog!GetRecordAtOffset(leader, followerEndOffset).epoch = replicaState[leader].leaderEpoch

LeaderShrinkIsrBetterFencing == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           endOffset == ReplicaLog!GetEndOffset(leader) 
       IN  \E replica \in isr \ {leader} :
           /\ ~ IsFollowerCaughtUpToLeaderEpoch(leader, replica, endOffset) 
           /\ QuorumUpdateLeaderAndIsr(leader, isr \ {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>
    
LeaderExpandIsrBetterFencing == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           leaderHw == replicaState[leader].hw
       IN  \E replica \in Replicas \ isr :
           /\ IsFollowerCaughtUpToLeaderEpoch(leader, replica, leaderHw)
           /\ HasFollowerReachedLeaderEpoch(leader, replica, leaderHw)
           /\ QuorumUpdateLeaderAndIsr(leader, isr \union {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>

BecomeFollower == \E leader, replica \in Replicas, leaderAndIsrRequest \in leaderAndIsrRequests :
    /\ leader # replica
    /\ leaderAndIsrRequest.leader = leader
    /\ leaderAndIsrRequest.leaderEpoch > replicaState[replica].leaderEpoch
    /\ replicaState' = [replicaState EXCEPT ![replica] = 
        [leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,                                                          
         leader |-> leader,
         isr |-> leaderAndIsrRequest.isr,                                                        
         hw |-> @.hw]]
    /\ UNCHANGED <<nextRecordId, replicaLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>
    
Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ LeaderExpandIsrBetterFencing
    \/ LeaderShrinkIsrBetterFencing
    \/ LeaderWrite
    \/ ImprovedLeaderIncHighWatermark 
    \/ BecomeFollower
    \/ FollowerFetch
    \/ FollowerTruncate

Spec == Init /\ [][Next]_vars 
             /\ SF_vars(ImprovedLeaderIncHighWatermark)
             /\ SF_vars(LeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(BecomeFollower)
             /\ WF_vars(BecomeLeader)


=============================================================================
\* Modification History
\* Last modified Sun Jul 08 00:48:20 PDT 2018 by jason
\* Created Sun Jul 08 00:45:59 PDT 2018 by jason
