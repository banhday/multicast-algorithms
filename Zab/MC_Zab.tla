---- MODULE MC_Zab ----
EXTENDS Zab, TLC

\* CONSTANT definitions @modelParameterConstants:0AcceptAck
const_1615273897124275000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Follower
const_1615273897124276000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:2NewLeader
const_1615273897124277000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3N
const_1615273897124278000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4Leader
const_1615273897124279000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:5BcastMsg
const_1615273897124280000 == 
{1, 2}
----

\* CONSTANT definitions @modelParameterConstants:6NewState
const_1615273897124281000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:7Accept
const_1615273897124282000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:8BallotMax
const_1615273897124283000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:9Commit
const_1615273897124284000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:10Recovering
const_1615273897124285000 == 
-1
----

\* CONSTANT definitions @modelParameterConstants:11NewLeaderAck
const_1615273897124286000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:12Server
const_1615273897124287000 == 
{1, 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:13NewStateAck
const_1615273897124288000 == 
7
----

\* CONSTANT definitions @modelParameterConstants:14ServerSeq
const_1615273897124289000 == 
<<1, 2, 3>>
----

\* CONSTANT definitions @modelParameterConstants:15BcastMsgInSeq
const_1615273897124290000 == 
<<1, 2>>
----

\* CONSTANT definitions @modelParameterConstants:16BcastMsgInSeqLen
const_1615273897124291000 == 
2
----

=============================================================================
\* Modification History
\* Created Tue Mar 09 08:11:37 CET 2021 by tran
