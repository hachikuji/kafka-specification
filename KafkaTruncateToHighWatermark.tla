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
