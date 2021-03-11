---------------------------- MODULE domain_test ----------------------------


EXTENDS Integers, Sequences

MySeq == << 1, 2, 3 >>

VARIABLE s

Init == s = << >>

Next == 
  /\ \A k \in DOMAIN MySeq : MySeq[k] < 4
  /\ s' = << 3 >>
  
Spec == Init /\ [][Next]_s

Inv == Len(s) < 2  

=============================================================================
\* Modification History
\* Last modified Tue Mar 09 15:52:04 CET 2021 by tran
\* Created Tue Mar 09 15:49:30 CET 2021 by tran
