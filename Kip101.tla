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

------------------------------- MODULE Kip101 -------------------------------

(**
 * With KIP-101, we used leader epoch information in the records to find a
 * more accurate offset for truncation.
 *)

EXTENDS KafkaReplication
 
OffsetsWithLargerEpochs(replica, epoch) ==
    {entry.offset : entry \in 
        {entry \in ReplicaLog!GetAllEntries(replica) : entry.record.epoch > epoch}}

LookupOffsetForEpoch(leader, follower, epoch) == 
    IF ReplicaLog!IsEmpty(leader)
    THEN replicaState[follower].hw
    ELSE IF ReplicaLog!GetLatestRecord(leader).epoch = epoch
    THEN ReplicaLog!GetEndOffset(leader)
    ELSE LET offsetWithLargerEpochs == OffsetsWithLargerEpochs(leader, epoch)
         IN IF offsetWithLargerEpochs = {} 
            THEN replicaState[follower].hw 
            ELSE Min(offsetWithLargerEpochs) 

BecomeFollowerTruncateKip101 == \E leader, replica \in Replicas :
    \/  /\ ReplicaLog!IsEmpty(replica) 
        /\ BecomeFollowerAndTruncateTo(leader, replica, 0)
    \/ \E record \in LogRecords :
        /\ ReplicaLog!IsLatestRecord(replica, record)
        /\ LET offset == LookupOffsetForEpoch(leader, replica, record.epoch)
           IN  BecomeFollowerAndTruncateTo(leader, replica, offset)

LOCAL Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ LeaderExpandIsr
    \/ LeaderShrinkIsr
    \/ LeaderWrite
    \/ LeaderIncHighWatermark 
    \/ BecomeFollowerTruncateKip101
    \/ FollowerReplicate
    
LOCAL Spec == Init /\ [][Next]_vars 
             /\ SF_vars(LeaderIncHighWatermark)
             /\ SF_vars(LeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(BecomeFollowerTruncateKip101)
             /\ WF_vars(BecomeLeader)

=============================================================================
\* Modification History
\* Last modified Mon Jul 09 00:16:30 PDT 2018 by jason
\* Created Thu Jul 05 23:39:35 PDT 2018 by jason
