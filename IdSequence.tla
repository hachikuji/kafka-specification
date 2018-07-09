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
\* Last modified Sat Jun 23 13:00:36 PDT 2018 by jason
\* Created Sun Jun 10 15:39:08 PDT 2018 by jason
