-------------------------------- MODULE Zab_Types --------------------------------

EXTENDS Integers,  FiniteSets, Sequences, Naturals, TLC

 
a <: b == a
 
CONSTANT N, Server, ServerSeq                    
ASSUME N = Cardinality(Server)                
MajorGuard == (N \div 2) + 1  

CONSTANT BallotMax           
VARIABLE ballot, cballot     
BallotRange == 0..BallotMax
BallotNull == -1

IsLeader == [b \in 1..BallotMax |-> ServerSeq[(b % N) + 1]]      
CONSTANT BcastMsg, BcastMsgInSeq, BcastMsgInSeqLen
BcastMsgNull == -1 
ASSUME BcastMsgNull \notin BcastMsg

VARIABLE bcastMsgLog
SlotMax == Len(BcastMsgInSeq)                              
SlotRange == 1..SlotMax  
SlotValue == {BcastMsgNull} \cup BcastMsg
EmptyLog == << >> <: Seq(Int)
LogInstance == ( UNION { [(1..maxSlot) -> SlotValue] : maxSlot \in SlotRange } ) \cup {EmptyLog}


CONSTANT Accept, AcceptAck, Commit, NewLeader, NewLeaderAck, 
                  NewState, NewStateAck
                  
MsgStatus == { Accept, AcceptAck, Commit, NewLeader, NewLeaderAck, 
                  NewState, NewStateAck }   
MsgStatus_NormalCase == { Accept, AcceptAck, Commit }
MsgStatus_RecoveringCase == { NewLeader, NewLeaderAck, NewState, NewStateAck }                        
                                                                       
AcceptInfo == [type : {Accept}, bcast : BcastMsg, ballot : BallotRange, 
                  slot : SlotRange]

AcceptAckInfo == [type : {AcceptAck}, ballot : BallotRange, slot : SlotRange]

CommitInfo == [type : {Commit}, ballot : BallotRange, slot : SlotRange, 
                  bcast : BcastMsg]

NewLeaderInfo == [type : {NewLeader}, ballot : BallotRange]

NewLeaderAckInfo == [type : {NewLeaderAck}, ballot : BallotRange, 
                          cballot : BallotRange, log : LogInstance]                    
                  
NewStateInfo == [type : {NewState}, ballot : BallotRange, log : LogInstance]

NewStateAckInfo == [type : {NewStateAck}, ballot : BallotRange]

Message_NormalCase == [source : Server, dest : Server, data : AcceptInfo \cup AcceptAckInfo \cup CommitInfo]                        

Message_RecoveringCase == [source : Server, dest : Server, data : NewLeaderInfo \cup NewLeaderAckInfo \cup NewStateInfo \cup NewStateAckInfo]


Message == Message_NormalCase \cup Message_RecoveringCase
                         
VARIABLE status
CONSTANT Leader, Follower, Recovering
Status == { Leader, Follower, Recovering }

Max(x, y) == IF x > y THEN x ELSE y                         

VARIABLE lastDelivered, rcvdMsg_NormalCase, rcvdMsg_RecoveringCase, inTransit, front, delivered, bcasted                      

vars == << bcastMsgLog, ballot, cballot, status, lastDelivered, rcvdMsg_NormalCase, rcvdMsg_RecoveringCase, inTransit, front,   
              delivered, bcasted >> 

TypeInv == 
  /\ \A s \in Server : \A k \in DOMAIN bcastMsgLog[s] : 
        \/ bcastMsgLog[s][k] \in bcasted
        \/ bcastMsgLog[s][k] = BcastMsgNull  
  /\ ballot \in [Server -> BallotRange]
  /\ cballot \in [Server -> BallotRange]
  /\ status \in [Server -> Status]
  /\ lastDelivered \in [Server -> {0} \cup SlotRange]  
  /\ \A s \in Server : rcvdMsg_NormalCase[s] \subseteq Message_NormalCase 
  /\ \A s \in Server : rcvdMsg_RecoveringCase[s] \subseteq Message_RecoveringCase
  /\ \A s \in Server, t \in Server : \A k \in DOMAIN inTransit[s][t] : 
        inTransit[s][t][k] \in Message  
  /\ \A snder, rcver \in Server : 0 <= front[snder][rcver] /\ front[snder][rcver] <= Len(inTransit[snder][rcver])
  /\ \A s \in Server : \A k \in DOMAIN delivered[s]: delivered[s][k] \in bcasted    
  /\ bcasted \subseteq BcastMsg

Integrity ==
  \A s \in Server : \A k1, k2 \in DOMAIN delivered[s] : delivered[s][k1] = delivered[s][k2] => k1 = k2   

Validity == 
  \A s \in Server : \A k \in DOMAIN delivered[s] : delivered[s][k] \in bcasted     
     
DeliverBefore(m1, m2) ==
  \E s \in Server : \E k1 \in DOMAIN delivered[s] : /\ delivered[s][k1] = m1
                                                    /\ \A k2 \in 1..(k1 - 1) : delivered[s][k2] # m2
GlobalTotalDeliveryOrder == 
  \A m1, m2 \in BcastMsg: m1 # m2 => ~(DeliverBefore(m1, m2) /\ DeliverBefore(m2, m1))
  
OneMsgCtor(snder, rcver, info) == [source |-> snder, dest |-> rcver, data |-> info]

ManyMsgsCtor(snder, rcver, infoSeq) ==
  [ index \in DOMAIN infoSeq |-> OneMsgCtor(snder, rcver, infoSeq[index])] 

SendOneMsgToRcvers(source, destList, info) ==   
  inTransit' = [inTransit EXCEPT ![source] = [dest \in Server |->  
                  IF dest \in destList 
                  THEN Append(inTransit[source][dest], OneMsgCtor(source, dest, info))
                  ELSE inTransit[source][dest]]]

SendOneMsgToAll(source, info) ==   
  inTransit' = [inTransit EXCEPT ![source] = [dest \in Server |->  
                  Append(inTransit[source][dest], OneMsgCtor(source, dest, info))]]
                                                        
SendOneMsgToOne(source, dest, info) ==               
  inTransit' = [inTransit EXCEPT ![source][dest] = Append(inTransit[source][dest], 
                                                        OneMsgCtor(source, dest, info))]                               
                                                              
SendManyMsgsToAll(source, infoSeq) ==  
  inTransit' = [inTransit EXCEPT ![source] = [dest \in Server |->                    
                  inTransit[source][dest] \circ ManyMsgsCtor(source, dest, infoSeq)]] 
                      
Receive(rcver, snder, m) ==
  /\ front' = [front EXCEPT ![snder][rcver] = front[snder][rcver] + 1]
  /\ IF m.data.type \in MsgStatus_NormalCase
     THEN /\ rcvdMsg_NormalCase' = [rcvdMsg_NormalCase EXCEPT ![rcver] = rcvdMsg_NormalCase[rcver] \cup {m}]
          /\ UNCHANGED rcvdMsg_RecoveringCase 
     ELSE /\ rcvdMsg_RecoveringCase' = [rcvdMsg_RecoveringCase EXCEPT ![rcver] = rcvdMsg_RecoveringCase[rcver] \cup {m}]
          /\ UNCHANGED rcvdMsg_NormalCase

Init1 ==  
  /\ status = [s \in Server |-> Follower]  
  (*
  /\ bcastMsgLog = [s \in Server |-> (<<>> <: Seq(Int))] 
  /\ ballot = [s \in Server |-> 0]
  /\ cballot = [s \in Server |-> 0]
  /\ lastDelivered = [s \in Server |-> 0]
  /\ delivered = [s \in Server |-> (<<>> <: Seq(Int)) ]  
*)
  /\ bcastMsgLog = 0
  /\ ballot = 0
  /\ cballot = 0
  /\ lastDelivered = 0
  /\ delivered = 0
  /\ rcvdMsg_NormalCase = 0
  /\ rcvdMsg_RecoveringCase = 0
  /\ inTransit = 0
  /\ front = 0
  /\ bcasted = 0

(*
Init2 ==  
  /\ rcvdMsg_NormalCase = [s \in Server |-> 
                    ({} <: { [data |-> [type |-> Int, 
                                        ballot |-> Int,
                                        slot |-> Int,
                                        bcast |-> Int,
                                        log |-> Seq(Int) ],
                              source |-> Int,
                              dest |-> Int] }) ]
  /\ rcvdMsg_RecoveringCase = [s \in Server |-> 
                    ({} <: {[data |-> [type |-> Int, 
                                       ballot |-> Int,
                                       slot |-> Int,
                                       bcast |-> Int,
                                       log |-> Seq(Int) ],
                             source |-> Int,
                             dest |-> Int]}) ]
  /\ inTransit = [s \in Server |-> [q \in Server |-> 
                    (<<>> <: Seq([data |-> [type |-> Int, 
                                            ballot |-> Int,
                                            slot |-> Int,
                                            bcast |-> Int,
                                            log |-> Seq(Int) ],
                                  source |-> Int,
                                  dest |-> Int]))  ]]
  /\ front = [s \in Server |-> [q \in Server |-> 0]]    
  /\ bcasted = {} <: {Int}
                      *)
Init == Init1 

HandleBcastMsg(self, msg) ==
  /\ status[self] = Leader  
  /\ UNCHANGED << status, ballot, cballot, lastDelivered, front, delivered, rcvdMsg_RecoveringCase, rcvdMsg_NormalCase >>
  /\ LET index == Len(bcastMsgLog[self]) + 1         
         info == [type |-> Accept, ballot |-> ballot'[self], slot |-> index, bcast |-> msg]               
     IN /\ bcastMsgLog' = [bcastMsgLog EXCEPT ![self] = Append(bcastMsgLog[self], msg)]                                     
        /\ SendOneMsgToAll(self, info) 
        

HandleAcceptMsg(self, snder, msg) ==  
  IF /\ ballot[self] = msg.data.ballot
     /\ status[self] \in { Leader, Follower }     
  THEN LET slot == msg.data.slot
           dom == 1..Max(Len(bcastMsgLog[self]), slot)
           source == self
           dest == snder
           info == [type |-> AcceptAck, ballot |-> msg.data.ballot, slot |-> msg.data.slot]
       IN /\ bcastMsgLog' = [bcastMsgLog EXCEPT ![self] = [k \in dom |-> 
                            IF k \in DOMAIN bcastMsgLog[self] /\ k # slot THEN bcastMsgLog[self][k]
                            ELSE IF k = slot THEN msg.data.bcast
                                 ELSE BcastMsgNull]]
          /\ UNCHANGED << ballot, cballot, status, lastDelivered, delivered, bcasted >> 
          /\ SendOneMsgToOne(source, dest, info)
  ELSE UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered,  
                    inTransit, delivered, bcasted >>       

HandleAcceptAckMsg(self, msg) == 
  IF /\ status[self] = Leader
     /\ ballot[self] = msg.data.ballot
  THEN LET similarMsg == {elem \in rcvdMsg_NormalCase'[self] : 
                                /\ elem.data.type = AcceptAck
                                /\ elem.data.ballot = msg.data.ballot 
                                /\ elem.data.slot = msg.data.slot}
           snderList == {elem.source : elem \in similarMsg}
           bcastMsg == bcastMsgLog[self][msg.data.slot]
           info == [type |-> Commit, ballot |-> msg.data.ballot, slot |-> msg.data.slot, 
                       bcast |-> bcastMsg] 
       IN IF Cardinality(snderList) = MajorGuard
          THEN /\ UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered, delivered, bcasted >>
               /\ SendOneMsgToAll(self, info)
          ELSE UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered, inTransit, 
                              delivered, bcasted >>   
  ELSE UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered,  
                      inTransit, delivered, bcasted >>          
        
HandleCommitMsg(self, msg) == 
  IF /\ status[self] \in { Leader, Follower }
     /\ ballot[self] = msg.data.ballot
     /\ lastDelivered[self] < msg.data.slot
  THEN LET slot == msg.data.slot
           dom == 1..Max(Len(bcastMsgLog[self]), slot)
       IN /\ lastDelivered' = [lastDelivered EXCEPT ![self] = msg.data.slot]
          /\ bcastMsgLog' = [bcastMsgLog EXCEPT ![self] = [k \in dom |-> 
                        IF k \in DOMAIN bcastMsgLog[self] /\ k # slot THEN bcastMsgLog[self][k]
                        ELSE IF k = slot THEN msg.data.bcast
                             ELSE BcastMsgNull]]                                                   
          /\ delivered' = [delivered EXCEPT ![self] = Append(delivered[self], msg.data.bcast)]
          /\ UNCHANGED << ballot, cballot, status, inTransit, bcasted >>     
  ELSE UNCHANGED << lastDelivered, delivered, bcastMsgLog, ballot, cballot, status, inTransit, bcasted >>
     
Recover(self) == 
  \E newBallot \in (ballot[self] + 1)..BallotMax:
    /\ status[self] = Follower
    /\ IsLeader[newBallot] = self
    /\ UNCHANGED << bcastMsgLog, cballot, lastDelivered, rcvdMsg_NormalCase, rcvdMsg_RecoveringCase, front, delivered, bcasted >>
    /\ LET info == [type |-> NewLeader, ballot |-> newBallot]
       IN /\ status' = [status EXCEPT ![self] = Recovering]
          /\ ballot' = [ballot EXCEPT ![self] = newBallot]
          /\ SendOneMsgToRcvers(self, Server \ {self}, info)

HandleNewLeaderMsg(self, LeaderCand, msg) == 
  IF ballot[self] < msg.data.ballot 
  THEN /\ status' = [status EXCEPT ![self] = Recovering]
       /\ ballot' = [ballot EXCEPT ![self] = msg.data.ballot]
       /\ UNCHANGED << bcastMsgLog, cballot, lastDelivered, delivered, bcasted >>
       /\ LET info == [type |-> NewLeaderAck, ballot |-> ballot'[self], cballot |-> cballot'[self], 
                         log |-> bcastMsgLog'[self]]
          IN SendOneMsgToOne(self, LeaderCand, info)
  ELSE UNCHANGED << lastDelivered, delivered, bcastMsgLog, ballot, cballot, status, inTransit, bcasted >>                      
  
PickGreaterLog(log1, log2)  ==
  IF \/ log1.data.cballot < log2.data.cballot
     \/ /\ log1.data.cballot = log2.data.cballot
        /\ Len(log1.data.log) <= Len(log2.data.log)
  THEN log2
  ELSE log1
  
 
UNROLL_DEFAULT_PickGreatestLog == 0 
UNROLL_TIMES_PickGreatestLog == 2 
  
RECURSIVE PickGreatestLog(_) 

PickGreatestLog(setLog) ==
 IF Cardinality(setLog) = 1 
 THEN CHOOSE elem \in setLog : TRUE
 ELSE LET log1 == CHOOSE x \in setLog : TRUE
          log2 == PickGreatestLog(setLog \ {log1})
      IN PickGreaterLog(log1, log2)
             

HandleNewLeaderAckMsg(self, msg) ==
  IF /\ status[self] = Recovering  
     /\ ballot[self] = msg.data.ballot
       
  THEN LET info0 == [type |-> NewLeaderAck, ballot |-> ballot[self], cballot |-> cballot[self], 
                    log |-> bcastMsgLog[self]]
           selfMsg == OneMsgCtor(self, self, info0)                      
           similarMsg == {elem \in rcvdMsg_RecoveringCase'[self] : 
                                  /\ elem.data.type = NewLeaderAck
                                  /\ elem.data.ballot = msg.data.ballot }
                           \cup {selfMsg}                                                
           snderList == {elem.source : elem \in similarMsg}        
       IN IF  Cardinality(snderList) = MajorGuard                   
          THEN LET msg0 == PickGreatestLog(similarMsg)                   
                   currLog == msg0.data.log
                   currBallot == msg0.data.ballot
                   info == [type |-> NewState, ballot |-> currBallot, log |-> currLog]
               IN /\ bcastMsgLog' = [bcastMsgLog EXCEPT ![self] = currLog]                   
                  /\ cballot' = [cballot EXCEPT ![self] = currBallot]                      
                  /\ UNCHANGED << ballot, status, lastDelivered, delivered, bcasted >>                          
                  /\ SendOneMsgToRcvers(self, Server \ {self}, info)
          ELSE UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered, delivered, 
                            inTransit, bcasted >>               
  ELSE UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered, delivered, 
                            inTransit, bcasted >>                                                           
                        

HandleNewStateMsg(self, LeaderCand, msg) ==   
  IF ballot[self] <= msg.data.ballot
  THEN /\ ballot'= [ballot EXCEPT ![self] = msg.data.ballot]
       /\ cballot'= [cballot EXCEPT ![self] = msg.data.ballot]
       /\ bcastMsgLog' = [bcastMsgLog EXCEPT ![self] = msg.data.log]
       /\ status' = [status EXCEPT ![self] = Follower]
       /\ UNCHANGED << lastDelivered, delivered, bcasted >>
       /\ LET info == [type |-> NewStateAck, ballot |-> ballot'[self]]
          IN SendOneMsgToOne(self, LeaderCand, info)
  ELSE UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered,  
                    inTransit, delivered, bcasted >>

HandleNewStateAckMsg(self, msg) == 
  IF /\ status[self] = Recovering
     /\ ballot[self] = msg.data.ballot  
  THEN LET similarMsg == {elem \in rcvdMsg_RecoveringCase'[self] : 
                                /\ elem.data.type = NewStateAck
                                /\ elem.data.ballot = msg.data.ballot}
           snderList == {elem.source : elem \in similarMsg}        
       IN IF Cardinality(snderList) + 1 = MajorGuard
          THEN /\ status' = [status EXCEPT ![self] = Leader]
               /\ UNCHANGED << bcastMsgLog, ballot, cballot, lastDelivered, delivered, bcasted >>        
               /\ LET CommitInfoSeq == [k \in DOMAIN bcastMsgLog[self] |-> 
                                         [type |-> Commit, ballot |-> ballot'[self], slot |-> k,  
                                            bcast |-> bcastMsgLog[self][k]]]                
                  IN SendManyMsgsToAll(self, CommitInfoSeq)
          ELSE /\ UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered,  
                          inTransit,  delivered, bcasted >>
  ELSE UNCHANGED << bcastMsgLog, ballot, cballot, status, lastDelivered,  
                    inTransit, delivered, bcasted >>                           
  
ReachBounds ==
  /\ Cardinality(bcasted) = Cardinality(BcastMsg)
  /\ \A snder, rcver \in Server : front[snder][rcver] = Len(inTransit[snder][rcver])
  /\ UNCHANGED vars                   
  
HandleMsg(snder, rcver, msg) ==
  \/ /\ msg.data.type = Accept 
     /\ HandleAcceptMsg(rcver, snder, msg)       
  \/ /\ msg.data.type = AcceptAck
     /\ HandleAcceptAckMsg(rcver, msg)
  \/ /\ msg.data.type = Commit
     /\ HandleCommitMsg(rcver, msg)     
  \/ /\ msg.data.type = NewLeader
     /\ HandleNewLeaderMsg(rcver, snder, msg)
  \/ /\ msg.data.type = NewLeaderAck
     /\ HandleNewLeaderAckMsg(rcver, msg)     
  \/ /\ msg.data.type = NewState
     /\ HandleNewStateMsg(rcver, snder, msg)
  \/ /\ msg.data.type = NewStateAck        
     /\ HandleNewStateAckMsg(rcver, msg)
 
Next ==       UNCHANGED vars
(*   
  \/ /\ Cardinality(bcasted) < Cardinality(BcastMsg)
     /\ LET k == Cardinality(bcasted) + 1
            msg == BcastMsgInSeq[k]
        IN \E s \in Server :  
              /\ status[s] = Leader
              /\ HandleBcastMsg(s, msg)
              /\ bcasted' = bcasted \cup { msg }  
              
  \/ \E rcver, snder \in Server :
        /\ front[snder][rcver] < Len(inTransit[snder][rcver])
        /\ LET slot == front[snder][rcver] + 1
               msg == inTransit[snder][rcver][slot]
           IN /\ Receive(rcver, snder, msg)
              /\ HandleMsg(snder, rcver, msg)
  \/ \E s \in Server : Recover(s)    
         
  \/ ReachBounds
  *)     
  
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue Mar 09 08:32:07 CET 2021 by tran
\* Last modified Thu Nov 29 12:24:38 CET 2018 by tthai
\* Created Wed Nov 28 13:22:35 CET 2018 by tthai
