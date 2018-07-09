-------------------- MODULE KafkaTruncateToHighWatermark --------------------

EXTENDS KafkaReplication

(***************************************************************************)
(* In older versions of Kafka, upon becoming a follower, a replica simply
 * truncated to its local high watermark. We were aware of edge cases in which
 * a replica could be elected as leader immediately following this truncation,
 * while resulted in the loss of committed data.  
 *)

BecomeFollowerTruncateToHighWatermark == \E leader, replica \in Replicas :
    LET replicaHw == replicaState[replica].hw
    IN BecomeFollowerAndTruncateTo(leader, replica, replicaHw)

Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ LeaderExpandIsr
    \/ LeaderShrinkIsr
    \/ LeaderWrite
    \/ LeaderIncHighWatermark 
    \/ BecomeFollowerTruncateToHighWatermark
    \/ FollowerReplicate

Spec == Init /\ [][Next]_vars 
             /\ SF_vars(LeaderIncHighWatermark)
             /\ SF_vars(LeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(BecomeFollowerTruncateToHighWatermark)
             /\ WF_vars(BecomeLeader)
             
=============================================================================
\* Modification History
\* Last modified Fri Jul 06 00:24:16 PDT 2018 by jason
\* Created Sun Jun 17 11:33:02 PDT 2018 by jason
