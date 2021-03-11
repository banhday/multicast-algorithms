---- MODULE MC_Skeen_P3Msg3 ----
EXTENDS Skeen, TLC

\* CONSTANT definitions @modelParameterConstants:0McastMsg
const_1615400453796317000 == 
{ [groupDest |-> {{1}, {2}}, data |-> [type |-> Multicast, id |-> (N * 20 + 1)]],
              [groupDest |-> {{2}, {3}}, data |-> [type |-> Multicast, id |-> (N * 20 + 2)]],
              [groupDest |-> {{3}, {1}}, data |-> [type |-> Multicast, id |-> (N * 20 + 3)]]  }
----

\* CONSTANT definitions @modelParameterConstants:1N
const_1615400453796318000 == 
3
----

=============================================================================
\* Modification History
\* Created Wed Mar 10 19:20:53 CET 2021 by tran
