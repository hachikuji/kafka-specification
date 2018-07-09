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
 
----------------------------- MODULE IdSequence -----------------------------

EXTENDS Integers

CONSTANT MaxId

ASSUME MaxId \in Nat

VARIABLES nextId

IdSet == 0 .. MaxId

NextId(id) ==
    /\ id \leq MaxId
    /\ id = nextId
    /\ nextId' = nextId + 1

GetNextId == CHOOSE id \in IdSet : NextId(id)

Init == nextId = 0

Next == \E id \in IdSet : NextId(id)

Spec == Init /\ [][Next]_nextId    

TypeOk == nextId \in IdSet \union {MaxId + 1}

THEOREM Spec => TypeOk
=============================================================================
\* Modification History
\* Last modified Mon Jul 09 14:22:21 PDT 2018 by jason
\* Created Sun Jun 10 15:39:08 PDT 2018 by jason
