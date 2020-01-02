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
 
------------------------------- MODULE Kip320 -------------------------------

(** 
 * We failed to fence fetch requests properly, which led to KIP-320. Here is a summary
 * of the basic replication rules that we found while verifying this model.
 *
 * 1) Whenever a follower bumps its epoch, it is required to use the OffsetForLeaderEpoch
 *    API to initialize its log. It must not begin fetching until its log matches the 
 *    leader's log up to the follower's end offset.
 * 2) The truncation phase when a replica is becoming a follower must also be fenced. It is
 *    not safe to use the state of a leader in another epoch to find the truncation point
 *    because that state may change.
 * 3) The leader will only bump the high watermark if followers in the ISR have acknowledged
 *    the leader and its epoch.
 * 4) Shrinking the ISR is generally safe, but expanding it requires caution. In particular,
 *    followers must have at least replicated up to the start of the leader's epoch to
 *    ensure that committed data from a previous epoch cannot be lost.
 *)

EXTENDS Kip279

LOCAL IsFollowingLeaderEpoch(leader, follower) == 
    /\ ReplicaPresumesLeadership(leader)
    /\ replicaState[follower].leader = leader
    /\ replicaState[follower].leaderEpoch = replicaState[leader].leaderEpoch

(**
 * Followers can fetch as long as they have the same epoch as the leader. Prior to fetching,
 * followers are responsible for truncating the log so that it matches the leader's. The
 * local high watermark is updated at the time of fetching.
 *)
FencedFollowerFetch == \E follower, leader \in Replicas :
    /\ IsFollowingLeaderEpoch(leader, follower)
    /\ ReplicaLog!ReplicateTo(leader, follower)
    /\ LET  newEndOffset == ReplicaLog!GetEndOffset(follower) + 1
            leaderHw == replicaState[leader].hw
            followerHw == Min({leaderHw, newEndOffset}) 
       IN   replicaState' = [replicaState EXCEPT ![follower].hw = followerHw]
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * The high watermark is advanced if all members of the ISR are following the leader's
 * epoch and have replicated up to the current high watermark. Note that we depend only
 * on the leader's local ISR and not the quorum.
 *)
FencedLeaderIncHighWatermark == \E leader \in Replicas :
    /\ LET leaderHw == replicaState[leader].hw 
       IN  /\ ReplicaLog!HasOffset(leader, leaderHw)
           /\ \A follower \in replicaState[leader].isr : 
              /\ IsFollowingLeaderEpoch(leader, follower)
              /\ ReplicaLog!HasOffset(follower, leaderHw)
    /\ replicaState' = [replicaState EXCEPT ![leader].hw = @ + 1]
    /\ UNCHANGED <<nextRecordId, replicaLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * A replica is taken out of the ISR by the leader if it is not following the right epoch 
 * or if its end offset is lagging. In this model, the decision to shrink the ISR is made 
 * arbitrarily by the leader if either of these conditions is met. It can choose to shrink 
 * the ISR immediately after becoming leader or it can wait indefinitely before doing so.
 *)
FencedLeaderShrinkIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           leaderEndOffset == ReplicaLog!GetEndOffset(leader) 
       IN  \E follower \in isr \ {leader} :
           /\ \/ ~ IsFollowingLeaderEpoch(leader, follower)
              \/ ReplicaLog!GetEndOffset(follower) < leaderEndOffset
           /\ QuorumUpdateLeaderAndIsr(leader, isr \ {follower})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>

LOCAL HasHighWatermarkReachedCurrentEpoch(leader) ==
    LET hw == replicaState[leader].hw
    IN  \/ hw = ReplicaLog!GetEndOffset(leader)
        \/ \E record \in LogRecords :
            /\ ReplicaLog!HasEntry(leader, record, hw)
            /\ record.epoch = replicaState[leader].leaderEpoch

LOCAL HasFollowerReachedHighWatermark(leader, follower) == 
    LET hw == replicaState[leader].hw
    IN  \/ hw = 0
        \/ /\ hw > 0
           /\ ReplicaLog!HasOffset(follower, hw - 1)
(**
 * Generally speaking, a replica which has caught up to the high watermark is eligible
 * to join the ISR, but there is one subtlety. When a follower becomes leader, 
 * its high watermark is typically behind the leader. Since it does not know what the true
 * high watermark was at the time the leader failed (or shutdown), it must be conservative 
 * when adding new members to the ISR. We can be assured that all members of the current 
 * ISR have replicated up to whatever the leader's high watermark was, but it is not safe 
 * to assume the same for new replicas until they have replicated ALL of the messages from 
 * the previous leader. In other words, we need to wait until it has at least replicated up
 * to the start of the its own leader epoch.
 *)
FencedLeaderExpandIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
       IN  \E follower \in Replicas \ isr :
           /\ IsFollowingLeaderEpoch(leader, follower)
           /\ HasFollowerReachedHighWatermark(leader, follower)
           /\ HasHighWatermarkReachedCurrentEpoch(leader)
           /\ QuorumUpdateLeaderAndIsr(leader, isr \union {follower})
    /\ UNCHANGED <<nextRecordId, replicaLog, nextLeaderEpoch, leaderAndIsrRequests>>

LOCAL BecomeFollower(replica, leaderAndIsrRequest, newHighWatermark) ==
    replicaState' = [replicaState EXCEPT ![replica] = 
                         [leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,                                                          
                          leader |-> leaderAndIsrRequest.leader,
                          isr |-> leaderAndIsrRequest.isr,                                                        
                          hw |-> newHighWatermark]]

(**
 * The only improvement here over the KIP-279 truncation logic is that we ensure that the
 * leader and follower have the same epoch. Without it, we violate the strong ISR property
 * when a follower uses a leader with stale state to find the truncation offset. Later
 * the stale leader may do some truncation of its own before catching up to the follower's
 * epoch. You can verify this failure by replacing this action with `BecomeFollowerTruncateKip279`
 * in the spec below.
 *)
FencedBecomeFollowerAndTruncate == \E leader, replica \in Replicas, leaderAndIsrRequest \in leaderAndIsrRequests :
    /\ leader # replica
    /\ leaderAndIsrRequest.leader = leader
    /\ leaderAndIsrRequest.leaderEpoch > replicaState[replica].leaderEpoch
    /\  \/  /\ leader = None
            /\ BecomeFollower(replica, leaderAndIsrRequest, replicaState[replica].hw)
            /\ UNCHANGED replicaLog
        \/  /\ leader # None
            /\ ReplicaPresumesLeadership(leader)
            /\ replicaState[leader].leaderEpoch = leaderAndIsrRequest.leaderEpoch
            /\ LET truncationOffset == FirstNonMatchingOffsetFromTail(leader, replica)
                   newHighWatermark == Min({truncationOffset, replicaState[replica].hw})
               IN  /\ ReplicaLog!TruncateTo(replica, truncationOffset)
                   /\ BecomeFollower(replica, leaderAndIsrRequest, newHighWatermark)
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ FencedLeaderExpandIsr
    \/ FencedLeaderShrinkIsr
    \/ LeaderWrite
    \/ FencedLeaderIncHighWatermark 
    \/ FencedBecomeFollowerAndTruncate
    \/ FencedFollowerFetch

Spec == Init /\ [][Next]_vars 
             /\ SF_vars(FencedLeaderIncHighWatermark)
             /\ SF_vars(FencedLeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(FencedBecomeFollowerAndTruncate)
             /\ WF_vars(BecomeLeader)

THEOREM Spec => []TypeOk
THEOREM Spec => []LeaderInIsr
THEOREM Spec => []WeakIsr
THEOREM Spec => []StrongIsr
=============================================================================
\* Modification History
\* Last modified Thu Jan 02 14:37:06 PST 2020 by guozhang
\* Last modified Tue Jul 10 08:05:35 PDT 2018 by jason
\* Created Thu Jul 05 23:45:04 PDT 2018 by jason
