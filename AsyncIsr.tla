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
 
------------------------------ MODULE AsyncIsr ------------------------------

EXTENDS Integers, Util

CONSTANTS 
    Replicas,
    Leader,
    MaxOffset 

ASSUME 
    /\ MaxOffset > 0
    /\ Leader \in Replicas

VARIABLES
    controllerState,
    leaderState,
    requests,
    updates

Offsets == 0 .. MaxOffset
Nil == -1

LeaderState == [
    isr: SUBSET Replicas,
    version: Nat,
    pendingIsr: SUBSET Replicas,
    pendingVersion: Nat,
    offsets: [Replicas -> Nat]
]

ControllerState == [
    isr: SUBSET Replicas,
    version: Nat
] 

Message == [
    isr: SUBSET Replicas,
    version: Nat            
]

HighWatermark ==
  LET potentialIsr == leaderState.isr \union leaderState.pendingIsr
  IN  Min({leaderState.offsets[replica]: replica \in potentialIsr})
    
TypeOk ==
    /\ controllerState \in ControllerState
    /\ leaderState \in LeaderState
    /\ requests \subseteq Message
    /\ updates \subseteq Message

ControllerWriteIsr(isr, version) == 
    /\ version = controllerState.version + 1
    /\ controllerState' = [isr |-> isr, version |-> version]
  
ControllerShrinkIsr == \E replica \in Replicas:
    /\ replica # Leader
    /\ replica \in controllerState.isr
    /\ LET version == controllerState.version + 1
           isr == controllerState.isr \ {replica}
       IN  /\ ControllerWriteIsr(isr, version)
           /\ updates' = updates \union {[isr |-> isr, version |-> version]}
           /\ UNCHANGED <<leaderState, requests>> 

ControllerHandleRequest == \E message \in requests:
    /\ message.version = controllerState.version 
    /\ LET version == controllerState.version + 1
       IN  /\ ControllerWriteIsr(message.isr, version)
           /\ updates' = updates \union {[isr |-> message.isr, version |-> version]}
           /\ UNCHANGED <<leaderState, requests>>

LeaderRequestShrinkIsr == \E replica \in leaderState.isr:
    /\ replica # Leader
    /\ LET isr == leaderState.isr \ {replica}
           version == leaderState.version
       IN  /\  requests' = requests \union {[
                 isr |-> isr,
                 version |-> version
               ]}
           /\ leaderState' = [leaderState EXCEPT 
                !.pendingIsr = @ \union isr, 
                !.pendingVersion = version
              ]        
           /\ UNCHANGED <<controllerState, updates>> 

LeaderRequestExpandIsr == \E replica \in Replicas:
    /\ replica \notin leaderState.isr
    /\ leaderState.offsets[replica] \geq HighWatermark
    /\ LET isr == leaderState.isr \union {replica}
           version == leaderState.version
       IN  /\ requests' = requests \union {[
                isr |-> isr,
                version |-> version
              ]}
           /\ leaderState' = [leaderState EXCEPT 
                !.pendingIsr = @ \union isr, 
                !.pendingVersion = version
              ] 
    /\ UNCHANGED <<controllerState, updates>> 

LeaderWrite == 
    /\ leaderState' = [leaderState EXCEPT !.offsets[Leader] = @ + 1]
    /\ UNCHANGED <<controllerState, requests, updates>>

LeaderHandleUpdate == \E update \in updates:
    /\ update.version > leaderState.version
    /\ leaderState' = [leaderState EXCEPT 
         !.isr = update.isr, 
         !.version = update.version,
         !.pendingIsr = {},
         !.pendingVersion = Nil
       ]
    /\ UNCHANGED <<controllerState, requests, updates>>

FollowerReplicate == \E replica \in Replicas:
    /\ replica # Leader
    /\ leaderState.offsets[replica] < leaderState.offsets[Leader]
    /\ leaderState' = [leaderState EXCEPT !.offsets[replica] = @ + 1]
    /\ UNCHANGED <<controllerState, requests, updates>>

Init ==
    /\ controllerState = [
         isr |-> Replicas, 
         version |-> 0
       ]
    /\ leaderState = [
         isr |-> Replicas, 
         version |-> 0,
         pendingIsr |-> {},
         pendingVersion |-> Nil, 
         offsets |-> [replica \in Replicas |-> 0]
       ] 
    /\ requests = {}
    /\ updates = {}

Next ==
    \/ ControllerShrinkIsr
    \/ ControllerHandleRequest
    \/ LeaderRequestShrinkIsr
    \/ LeaderRequestExpandIsr
    \/ LeaderWrite
    \/ LeaderHandleUpdate
    \/ FollowerReplicate
    
ValidHighWatermark == \A replica \in controllerState.isr:
    leaderState.offsets[replica] \geq HighWatermark


=============================================================================
\* Modification History
\* Last modified Mon Jul 01 19:50:44 PDT 2019 by jason
\* Created Fri Jun 28 23:42:14 PDT 2019 by jason
