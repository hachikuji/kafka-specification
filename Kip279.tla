------------------------------- MODULE Kip279 -------------------------------

EXTENDS KafkaReplication


(***************************************************************************)
(* There was still a hole in the truncation logic which led to log divergence
 * when there were consecutive fast leader changes. 
 *)

MatchingOffsets(replica1, replica2) ==
    {entry.offset : entry \in
        {entry \in ReplicaLog!GetAllEntries(replica1) : 
          ReplicaLog!HasEntry(replica2, entry.record, entry.offset)}}

(**
 * To find the offset to truncate to, we verify offset and epoch going backwards 
 * from the end of the follower's log. The truncation offset is one more than the 
 * first offset that matches.
 *
 * TODO: Does this match the implementation?
 *)
FirstNonMatchingOffsetFromTail(leader, follower) ==
    IF ReplicaLog!IsEmpty(leader)
    THEN 0
    ELSE LET matchingOffsets == MatchingOffsets(follower, leader)
         IN IF matchingOffsets = {} 
            THEN 0
            ELSE Max(matchingOffsets) + 1 

BecomeFollowerTruncateKip279 == \E leader, replica \in Replicas :
    \/  /\ ReplicaLog!IsEmpty(replica) 
        /\ BecomeFollowerAndTruncateTo(leader, replica, 0)
    \/  /\ LET offset == FirstNonMatchingOffsetFromTail(leader, replica)
           IN  BecomeFollowerAndTruncateTo(leader, replica, offset)

LOCAL Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ LeaderExpandIsr
    \/ LeaderShrinkIsr
    \/ LeaderWrite
    \/ LeaderIncHighWatermark 
    \/ BecomeFollowerTruncateKip279
    \/ FollowerReplicate
    
LOCAL Spec == Init /\ [][Next]_vars 
             /\ SF_vars(LeaderIncHighWatermark)
             /\ SF_vars(LeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(BecomeFollowerTruncateKip279)
             /\ WF_vars(BecomeLeader)    
    
=============================================================================
\* Modification History
\* Last modified Sat Jul 07 00:00:35 PDT 2018 by jason
\* Created Thu Jul 05 23:41:29 PDT 2018 by jason
