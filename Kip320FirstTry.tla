(*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements. See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

--------------------------- MODULE Kip320FirstTry ---------------------------

(**
 * This was a first attempt at the improved fencing logic in KIP-320. The basic
 * idea was to have the followers send an expected epoch in the fetch request and
 * do the truncation upon receiving a LOG_TRUNCATION error. Rather than only doing
 * the truncation upon becoming a follower, we would simply begin fetching and only 
 * truncate when needed.
 *  
 * However, this model fails to guarantee the StrongIsr property because the leader
 * cannot guarantee that followers are on the same epoch when bumping the high watermark 
 * or expanding the ISR. You can run the model to find an example of this, but 
 * one case involves several fast leader elections and  a leader bumping the high 
 * watermark due to a follower on an older epoch. As the follower catches up to the 
 * current epoch, it may truncate the committed data, which results in a window during 
 * which it could be elected as leader and cause data loss.
 * 
 * Fixing the problem seems to be a simple matter of adding the current epoch to
 * the Fetch request, but then the existing logic of truncating only on leader epoch
 * changes makes more sense. For a given epoch, the follower only needs to truncate
 * once upon observing the new epoch and it should not need truncation again until
 * the next leader change.
 *)

EXTENDS Kip279

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


LeaderShrinkIsrBetterFencing == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           endOffset == ReplicaLog!GetEndOffset(leader) 
       IN  \E replica \in isr \ {leader} :
           /\ ~ IsFollowerCaughtUpToLeaderEpoch(leader, replica, endOffset) 
           /\ QuorumUpdateLeaderAndIsr(leader, isr \ {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>

LOCAL HasHighWatermarkReachedCurrentEpoch(leader) ==
    LET hw == replicaState[leader].hw
    IN  \/ hw = ReplicaLog!GetEndOffset(leader)
        \/ \E record \in LogRecords :
            /\ ReplicaLog!HasEntry(leader, record, hw)
            /\ record.epoch = replicaState[leader].leaderEpoch

(**
 * Note this version includes a bug fix in the ISR expansion logic following a leader election.
 * Basically the leader should not admit any new replicas into the ISR until they have at least
 * caught up to the start of the current epoch. 
 *)   
LeaderExpandIsrBetterFencing == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           leaderHw == replicaState[leader].hw
       IN  \E replica \in Replicas \ isr :
           /\ IsFollowerCaughtUpToLeaderEpoch(leader, replica, leaderHw)
           /\ HasHighWatermarkReachedCurrentEpoch(leader)
           /\ QuorumUpdateLeaderAndIsr(leader, isr \union {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * In this model, the replica does not truncate upon becoming follower. It simply begins
 * fetching and relies on receiving a truncation error in order to indicate when truncation 
 * is necessary.
 *)
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
\* Last modified Tue Jul 10 08:09:55 PDT 2018 by jason
\* Created Sun Jul 08 00:45:59 PDT 2018 by jason
