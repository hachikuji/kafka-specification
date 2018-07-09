-------------------------------- MODULE Util --------------------------------

EXTENDS Integers

Max(set) == CHOOSE max \in set : \A val \in set : max \geq val
Min(set) == CHOOSE min \in set : \A val \in set : min \leq val

=============================================================================
\* Modification History
\* Last modified Sat Jun 23 12:53:08 PDT 2018 by jason
\* Created Sat Jun 23 12:52:05 PDT 2018 by jason
