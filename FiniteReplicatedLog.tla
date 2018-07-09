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
 
------------------------ MODULE FiniteReplicatedLog ------------------------

EXTENDS Integers

CONSTANTS 
    Replicas, 
    LogRecords, 
    Nil, 
    LogSize

(*
ASSUME
    /\ LogSize \in Nat
    /\ Nil \notin LogRecords
*)
VARIABLE logs

MaxOffset == LogSize - 1

Offsets == 0 .. MaxOffset

StartOffset == 0

LOCAL LogType == [endOffset : Offsets \union {LogSize}, 
                  records : [Offsets -> LogRecords \union {Nil}]]
LOCAL EmptyLog == [endOffset |-> 0, 
                   records |-> [offset \in Offsets |-> Nil]]

IsEmpty(replica) == logs[replica].endOffset = 0

IsFull(replica) == logs[replica].endOffset = LogSize

HasEntry(replica, record, offset) == LET log == logs[replica] IN
    /\ offset < log.endOffset
    /\ log.records[offset] = record

IsLatestEntry(replica, record, offset) == LET log == logs[replica] IN
    /\ ~ IsEmpty(replica)
    /\ offset = log.endOffset - 1
    /\ record = log.records[offset]

GetLatestRecord(replica) == LET log == logs[replica] IN 
    IF IsEmpty(replica) 
    THEN Nil 
    ELSE log.records[log.endOffset - 1]

IsLatestRecord(replica, record) == \E offset \in Offsets : IsLatestEntry(replica, record, offset)

GetEndOffset(replica) == logs[replica].endOffset 

IsEndOffset(replica, offset) == logs[replica].endOffset = offset 

GetRecordAtOffset(replica, offset) == logs[replica].records[offset]

GetAllEntries(replica) == LET log == logs[replica] IN
    IF log.endOffset = 0
    THEN {}
    ELSE {[offset |-> offset, 
           record |-> GetRecordAtOffset(replica, offset)] : offset \in 0 .. (log.endOffset - 1)}

HasOffset(replica, offset) == offset < logs[replica].endOffset

LOCAL GetWrittenOffsets(replica) == 
    IF IsEmpty(replica)
    THEN {}
    ELSE 0 .. (logs[replica].endOffset - 1)

LOCAL GetUnwrittenOffsets(replica) ==
    IF IsFull(replica)
    THEN {}
    ELSE logs[replica].endOffset .. MaxOffset
    
LOCAL ReplicaLogTypeOk(replica) == LET log == logs[replica] IN
    /\ log \in LogType
    /\ \A offset \in GetWrittenOffsets(replica) : log.records[offset] \in LogRecords
    /\ \A offset \in GetUnwrittenOffsets(replica) : log.records[offset] = Nil

TypeOk == \A replica \in Replicas : ReplicaLogTypeOk(replica)

Init == logs = [replica \in Replicas |-> EmptyLog]

Append(replica, record, offset) == LET log == logs[replica] IN
    /\ ~ IsFull(replica)
    /\ offset = log.endOffset
    /\ logs' = [logs EXCEPT ![replica].records[offset] = record, 
                            ![replica].endOffset = @ + 1] 

TruncateTo(replica, newEndOffset) == LET log == logs[replica] IN
    /\ newEndOffset \leq log.endOffset
    /\ logs' = [logs EXCEPT 
        ![replica].records = [offset \in Offsets |-> IF offset < newEndOffset THEN @[offset] ELSE Nil], 
        ![replica].endOffset = newEndOffset]

ReplicateTo(fromReplica, toReplica) == \E offset \in Offsets, record \in LogRecords :
    /\ HasEntry(fromReplica, record, offset)
    /\ Append(toReplica, record, offset)

Next == \E replica \in Replicas :
    \/ \E record \in LogRecords, offset \in Offsets : Append(replica, record, offset)
    \/ \E offset \in Offsets : TruncateTo(replica, offset)
    \/ \E otherReplica \in Replicas \ {replica} : ReplicateTo(replica, otherReplica)
        
Spec == Init /\ [][Next]_logs

THEOREM Spec => []TypeOk
=============================================================================
\* Modification History
\* Last modified Mon Jul 09 14:23:51 PDT 2018 by jason
\* Created Sat Jun 23 13:24:52 PDT 2018 by jason
