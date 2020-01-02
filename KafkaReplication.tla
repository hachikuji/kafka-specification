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
 
-------------------------- MODULE KafkaReplication --------------------------

(**
 * This module contains the core Kafka replication state and its basic oeprators.
 * We model a single partition with a constant replication factor. A replica in this
 * model has its own state and can be either a leader or a follower at any given time.
 *
 * The controller in this model does not have its own state, but is able to influence
 * the behavior by directly modify a quorum state (i.e. zookeeper) and by propagating
 * LeaderAndIsr requests to the replicas.
 *)

EXTENDS Integers, Util

CONSTANTS 
    Replicas, 
    LogSize, 
    MaxRecords, 
    MaxLeaderEpoch

None == "NONE"
Nil == -1

ASSUME 
    /\ None \notin Replicas
    /\ MaxLeaderEpoch \in Nat

VARIABLES
    \* This is a function from the replicas to their local logs.  
    replicaLog,

    \* This is a function from the replicas to their local state. The replica state contains 
    \* leader/ISR information and the all-important high watermark.
    replicaState,
    
    \* Unique id generator for new records. Every producer write to a leader gets a new id
    \* so that we can ensure records are unique. 
    nextRecordId,

    \* This is a simple id sequence which is used to generate monotonically increasing
    \* leader epochs.
    nextLeaderEpoch,

    \* The LeaderAndIsr request is crucial in Kafka, so we want to model edge cases around 
    \* delivery of the request (e.g. lost requests and duplicates). We use a simple set of
    \* all LeaderAndIsr requests to enable this. Replicas choose arbitrarily from the set 
    \* which request to observe at any time, but generally they will ignore requests which
    \* contain a lower leader epoch than they expect.
    leaderAndIsrRequests,

    \* This is the model's equivalent of the state in Zookeeper, but generally we ignore 
    \* the complexity of Zookeeper itself. Instead we allow simple atomic operation to the 
    \* state directly within individual actions. We also elide details about propagation
    \* of quorum state, which enables ISR update fencing in Kafka. We assume unrealistically
    \* that quorum modifications are instantaneous and observed by all interested parties.
    quorumState
    
vars == <<replicaLog, replicaState, nextLeaderEpoch, nextRecordId, leaderAndIsrRequests, quorumState>> 

LeaderEpochSeq == INSTANCE IdSequence WITH MaxId <- MaxLeaderEpoch, nextId <- nextLeaderEpoch
RecordSeq == INSTANCE IdSequence WITH MaxId <- MaxRecords - 1, nextId <- nextRecordId

\* All records get an id and a leader epoch. To model the behavior of Kafka prior to the 
\* addition of the leader epoch in the message format, we simply ignore the epoch in the message.
LogRecords == [id : RecordSeq!IdSet, epoch : LeaderEpochSeq!IdSet] 

ReplicaLog == INSTANCE FiniteReplicatedLog WITH logs <- replicaLog
ReplicaOpt == Replicas \union {None}
LeaderEpochOpt == LeaderEpochSeq!IdSet \union {Nil}
QuorumState == [leaderEpoch: LeaderEpochOpt,
                leader : ReplicaOpt, 
                isr: SUBSET Replicas]
                
(**
 * Each replica has a cached copy of the quorum state and a local high watermark. These
 * get updated in accordance with the Kafka replication protocol. For example, the leader
 * epoch is updated when a LeaderAndIsr request is received. 
 *)                
ReplicaState == [hw : ReplicaLog!Offsets \union {LogSize}, 
                 leaderEpoch: LeaderEpochOpt,
                 leader : ReplicaOpt, 
                 isr: SUBSET Replicas]

TypeOk ==
    /\ LeaderEpochSeq!TypeOk
    /\ RecordSeq!TypeOk
    /\ ReplicaLog!TypeOk
    /\ replicaState \in [Replicas -> ReplicaState]
    /\ quorumState \in QuorumState
    /\ leaderAndIsrRequests \subseteq QuorumState

Init ==
    /\ LeaderEpochSeq!Init
    /\ RecordSeq!Init
    /\ ReplicaLog!Init
    /\ replicaState = [replica \in Replicas |-> [hw |-> ReplicaLog!StartOffset, 
                                                 leaderEpoch |-> Nil, 
                                                 leader |-> None, 
                                                 isr |-> {}]]
    /\ quorumState = [leaderEpoch |-> Nil,
                      leader |-> None, 
                      isr |-> Replicas]
    /\ leaderAndIsrRequests = {}

(**
 * Check whether a broker believes itself to be the leader. The presumed leader will accept
 * writes, so we depend on replication fencing for correct behavior.
 *)
ReplicaPresumesLeadership(replica) == replicaState[replica].leader = replica
ReplicaIsFollowing(follower, leader) == replicaState[follower].leader = leader
IsTrueLeader(leader) ==
    /\ quorumState.leader = leader 
    /\ ReplicaPresumesLeadership(leader)
    /\ replicaState[leader].leaderEpoch = quorumState.leaderEpoch


(**
 * Helper function to "send" a new LeaderAndIsr request. The leader epoch is bumped,
 * the quorum state is updatd, and the new request is added to the LeaderAndIsr request set.
 *)
ControllerUpdateIsr(newLeader, newIsr) == \E newLeaderEpoch \in LeaderEpochSeq!IdSet :
    /\ LeaderEpochSeq!NextId(newLeaderEpoch)
    /\  LET newControllerState == [
            leader |-> newLeader,
            leaderEpoch |-> newLeaderEpoch, 
            isr |-> newIsr] 
        IN  /\ quorumState' = newControllerState 
            /\ leaderAndIsrRequests' = leaderAndIsrRequests \union {newControllerState} 
(**
 * The controller shrinks the ISR upon broker failure. We do not represent node failures
 * explicitly in this model. A broker can be taken out of the ISR and immediately begin
 * fetching, or it can wait some time and fetch later. One way to look at this is that 
 * we do not distinguish between a properly shutdown broker which ceases fetching and 
 * a zombie which may continue to make progres. All states are checked.
 * 
 * Note that the leader can fail or do a controlled shutdown just like any other broker.
 * The leader is set to None in this case and removed from the ISR (as long as there is
 * at least one other replica in the ISR). Election of a new leader is done in a separate
 * step.
 *)
ControllerShrinkIsr == \E replica \in Replicas :
    /\  \/  /\ quorumState.leader = replica
            /\ quorumState.isr = {replica}
            /\ ControllerUpdateIsr(None, quorumState.isr)
        \/  /\ quorumState.leader = replica
            /\ quorumState.isr # {replica}
            /\ ControllerUpdateIsr(None, quorumState.isr \ {replica})
        \/  /\ quorumState.leader # replica
            /\ replica \in quorumState.isr
            /\ ControllerUpdateIsr(quorumState.leader, quorumState.isr \ {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, replicaState>>

(**
 * Leader election by the controller is triggered by the failure of a broker or the need 
 * to balance leaders. For clean leader election, we choose a member of the ISR and we 
 * bump the leader epoch. In this model, the coice to elect a new leader can be made 
 * arbitarily by the controller. 
 *)
ControllerElectLeader == \E newLeader \in quorumState.isr :
    /\ quorumState.leader # newLeader 
    /\ ControllerUpdateIsr(newLeader, quorumState.isr)
    /\ UNCHANGED <<nextRecordId, replicaLog, replicaState>>

(**
 * A replica will become a leader if it receives a LeaderAndIsr request with a higher
 * epoch than is in its local state. Significantly, the high watermark upon becoming
 * a leader is typically behind the "true" high watermark from the previous leader. 
 *)
BecomeLeader == \E leaderAndIsrRequest \in leaderAndIsrRequests :
    LET leader == leaderAndIsrRequest.leader
    IN  /\ leader # None
        /\ leaderAndIsrRequest.leaderEpoch > replicaState[leader].leaderEpoch
        /\ replicaState' = [replicaState EXCEPT ![leader] = [
                hw |-> @.hw,
                leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,
                leader |-> leader,
                isr |-> leaderAndIsrRequest.isr]]
        /\ UNCHANGED <<nextRecordId, replicaLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * A leader will accept a write from a producer as long as it presumes to be the leader.
 * In the event that it is wrong, we expect replication to fail, which will ultimately
 * result in an ISR shrink. Kafka's primary fencing of zombies comes in ISR shrinks.
 *)
LeaderWrite == \E replica \in Replicas, id \in RecordSeq!IdSet, offset \in ReplicaLog!Offsets :
    /\ ReplicaPresumesLeadership(replica)
    /\ RecordSeq!NextId(id)
    /\ LET record == [id |-> id, epoch |-> replicaState[replica].leaderEpoch]
       IN ReplicaLog!Append(replica, record, offset)
    /\ UNCHANGED <<replicaState, nextLeaderEpoch, quorumState, leaderAndIsrRequests>>

(**
 * Only the true leader (that is, the one currently designated in the quorum as the leader)
 * is allowed to update the ISR directly.
 *)
QuorumUpdateLeaderAndIsr(leader, newIsr) ==
    /\ IsTrueLeader(leader)
    /\ quorumState.leader = leader
    /\ quorumState' = [quorumState EXCEPT !.isr = newIsr]
    /\ replicaState' = [replicaState EXCEPT ![leader].isr = newIsr]

IsFollowerCaughtUp(leader, follower, endOffset) ==
    /\ ReplicaIsFollowing(follower, leader) 
    /\  \/ endOffset = 0
        \/  /\ endOffset > 0 
            /\ LET offset == endOffset - 1 IN \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(leader, record, offset)
                /\ ReplicaLog!HasOffset(follower, offset)

(**
 * ISR changes are fenced by the write to the quorum. There is some trickiness to make this
 * work in practice (i.e. propagation of the zkVersion), but this model ignores the details. 
 * We assume this logic is correct and simply allow the write if and only if the leader is 
 * the true leader in the quorum and has the current epoch.   
 *)
LeaderShrinkIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           endOffset == ReplicaLog!GetEndOffset(leader) 
       IN  \E replica \in isr \ {leader} :
           /\ ~ IsFollowerCaughtUp(leader, replica, endOffset) 
           /\ QuorumUpdateLeaderAndIsr(leader, isr \ {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * We can add a replica to the ISR if it has caught up to the current high watermark.
 * We depend on writes to the quorum to fence zombie leaders. In practice this requires
 * propagation of zk version in order to be able to do a CAS operation on the partition
 * state. We do not validate this propagation logic in this model and simply allow the
 * ISR expansion iff the leader and quorum state matches.
 *)
LeaderExpandIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           leaderHw == replicaState[leader].hw
       IN  \E replica \in Replicas \ isr :
           /\ IsFollowerCaughtUp(leader, replica, leaderHw)
           /\ QuorumUpdateLeaderAndIsr(leader, isr \union {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * This is the old logic for incrementing the high watermark. As long as each
 * member of the ISR ackowledges the presumed leader and has replicated up to
 * the current offset (no leader epoch verification), then we increment the
 * high watermark. Note that we do not model the fetch behavior directly. As long
 * as the replicas have acknowledged the leader, they /could/ all send a fetch
 * to advance the high watermark. What we model here is the transition in this case.
 *)
LeaderIncHighWatermark == \E offset \in ReplicaLog!Offsets, leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ offset = replicaState[leader].hw
    /\ \A follower \in replicaState[leader].isr : 
        /\ ReplicaIsFollowing(follower, leader)
        /\ ReplicaLog!HasOffset(follower, offset)
    /\ replicaState' = [replicaState EXCEPT ![leader].hw = @ + 1]
    /\ UNCHANGED <<nextRecordId, replicaLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * This is a helper for the follower state change. All that changed with the addition of 
 * KIP-101 and KIP-279 were improvements to the truncation logic upon becoming follower.
 * It is crucial that we do the truncation step on leader epoch changes, not just on 
 * leader changes.
 *
 * TODO: Is this what we actually do in the code?   
 *) 
BecomeFollowerAndTruncateTo(leader, replica, truncationOffset) == \E leaderAndIsrRequest \in leaderAndIsrRequests :
    /\ leader # replica
    /\ leaderAndIsrRequest.leader = leader
    /\ leaderAndIsrRequest.leaderEpoch > replicaState[replica].leaderEpoch
    /\  \/  /\ leader = None
            /\ UNCHANGED replicaLog
        \/  /\ leader # None
            /\ ReplicaLog!TruncateTo(replica, truncationOffset)
    /\ replicaState' = [replicaState EXCEPT ![replica] = 
        [leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,                                                          
         leader |-> leader,
         isr |-> leaderAndIsrRequest.isr,                                                        
         hw |-> Min({truncationOffset, @.hw})]] 
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * As long as a presumed leader and follower agree on the leader status, we will replicate 
 * the next record if possible. The main thing to note is the lack of proper fencing. 
 * We do not verify either the current leader epoch or the epoch of the most recent fetched
 * data. 
 *)
FollowerReplicate == \E follower, leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ ReplicaIsFollowing(follower, leader)
    /\ ReplicaLog!ReplicateTo(leader, follower) 
    /\ LET  newEndOffset == ReplicaLog!GetEndOffset(follower) + 1
            leaderHw == replicaState[leader].hw
            followerHw == Min({leaderHw, newEndOffset}) 
       IN   replicaState' = [replicaState EXCEPT ![follower].hw = followerHw]
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * The weak ISR property says that for any presumed leader, the replicas in its current
 * assumed ISR have replicated logs precisely up to the high watermark. This is a weak
 * property because the leaders are actually elected from the quorum ISR. Disagreement about
 * the true ISR can lead to the loss of committed data. In spite of its weakness, we 
 * intuitively expect it to be true, and it is illustrative to understand the cases in which
 * it doesn't
 *)
WeakIsr == \A r1 \in Replicas :
    \/ ~ ReplicaPresumesLeadership(r1)
    \/ LET  hw == replicaState[r1].hw
       IN   \/ hw = 0
            \/ \A r2 \in replicaState[r1].isr, offset \in 0 .. (hw - 1) : \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(r1, record, offset)        
                /\ ReplicaLog!HasEntry(r2, record, offset)  

(**
 * The strong ISR property says that if any replica presumes leadership, then all data below
 * its high watermark must be consistently replicated to all members of the true ISR. This 
 * ensures that any data which has been exposed to consumers will be present on any broker 
 * that becomes leader.
 *)
StrongIsr == \A r1 \in Replicas :
    \/ ~ ReplicaPresumesLeadership(r1)
    \/ LET  hw == replicaState[r1].hw
       IN   \/ hw = 0
            \/ \A r2 \in quorumState.isr, offset \in 0 .. (hw - 1) : \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(r1, record, offset)        
                /\ ReplicaLog!HasEntry(r2, record, offset) 

(**
 * The leader should always in the ISR, because even if all brokers failed, we still keep the leader in ISR
 *)
LeaderInIsr == quorumState.leader \in quorumState.isr

=============================================================================
\* Modification History
\* Last modified Thu Jan 02 14:37:55 PST 2020 by guozhang
\* Last modified Mon Jul 09 14:24:02 PDT 2018 by jason
\* Created Sun Jun 10 16:16:51 PDT 2018 by jason
