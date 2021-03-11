------------------------- MODULE white-box-atomic-multicast -------------------------


EXTENDS Integers,  FiniteSets, Sequences, TLC


(*
 *) 
VARIABLE clock, phase, localTS, globalTS, status, ballot, cballot, 
  Delivered, deliver, max_delivered_gts,
  mcasted, chan, outBuf, mcastLess, flag,
  accFrom, aackCter, lackCter, sackCter, cbTemp, gtsTemp, 
  BalVec, mcastStream
  
vars == << clock, phase, localTS, globalTS, status, ballot, cballot, 
  Delivered, deliver, max_delivered_gts,  
  mcasted, chan, outBuf, mcastLess, flag, cbTemp, gtsTemp, 
  accFrom, aackCter, lackCter, sackCter, BalVec, mcastStream >>

  
(*
 *)
CONSTANT N, Proc, GroupSet
CONSTANT LEADER, FOLLOWER, RECOVERING

\* CONSTANT P1, P2, P3, M1, M2

GroupNull == {}
ProcStatus == {LEADER, FOLLOWER, RECOVERING}

ASSUME \A g \in GroupSet : \A p \in g : p \in Nat 

ASSUME N = Cardinality(Proc) /\ N = Cardinality(UNION GroupSet)

ASSUME \A g \in GroupSet : g \subseteq Proc

ASSUME \A g1, g2 \in GroupSet : g1 \cap g2 # {} => g1 = g2

GroupCard == [g \in GroupSet |-> Cardinality(g)]

QuorumGuard == [g \in GroupSet |-> (GroupCard[g] \div 2) + 1]

RECURSIVE NatSum(_)

NatSum(set) ==
  IF set = {} THEN 0
  ELSE LET x == CHOOSE elem \in set : \A e \in set : e <= elem
       IN x + NatSum(set \ {x}) 

QuorumGuardTotal == 
  LET guard == {QuorumGuard[g] : g \in GroupSet}
  IN NatSum(guard)
  
AcceptAckGuard == QuorumGuardTotal + Cardinality(GroupSet)  

IsGroup(g) == \E g0 \in GroupSet : g = g0
       
       

groupLess(g1, g2) ==
  LET max1 == CHOOSE e1 \in g1 : \A e \in (g1 \ {e1}) : e < e1
      max2 == CHOOSE e2 \in g2 : \A e \in (g2 \ {e2}) : e < e2
  IN max1 < max2  

GroupOrder == [g1 \in GroupSet |-> [g2 \in GroupSet |-> groupLess(g1, g2)]]


\* The group to which process self belongs 
GetGroup == [p \in Proc |-> CHOOSE group \in GroupSet : p \in group]


(*
 *) 
TimeNull == -1
TimestampNull == [time |-> TimeNull, group |-> GroupNull]
ValidTimestamp == [time : Nat \ {TimeNull}, group : GroupSet]
Timestamp == ValidTimestamp \cup {TimestampNull}

IsTimestamp(ts) == ts \in Timestamp

IsValidTimestamp(ts) == ts \in ValidTimestamp


(*
 *)
CONSTANT BalMax
BallotNull == 0
ValidBallot == 1..BalMax

LeaderIn == [g \in GroupSet |-> [bal \in 1..BalMax |-> 
              LET k == (bal % GroupCard[g]) + 1
                  leaderCand == CHOOSE p \in g : (p % GroupCard[g]) + 1 = k 
              IN leaderCand]]

(*
 *)
CONSTANT McastMsg, McastMsgID

CONSTANT MULTICAST, ACCEPT, ACCEPT_ACK, DELIVER, NEW_LEADER, NEW_LEADER_ACK,
  NEW_STATE, NEW_STATE_ACK, MSG_NULL
                  
CONSTANT PROPOSED, START, ACCEPTED, COMMITTED

ASSUME START \in Nat /\ PROPOSED \in Nat /\ ACCEPTED \in Nat /\ COMMITTED \in Nat

ASSUME PROPOSED < START /\ START < ACCEPTED /\ ACCEPTED < COMMITTED  

MsgType == { MULTICAST, ACCEPT, ACCEPT_ACK, DELIVER, NEW_LEADER, NEW_LEADER_ACK,
  NEW_STATE, NEW_STATE_ACK }
  
ProcMsgStatus == {START, PROPOSED, ACCEPTED, COMMITTED}

ClientMsgStatus == {MULTICAST}

MsgStatus == ProcMsgStatus \cup ClientMsgStatus

MsgNull == [type |-> MSG_NULL]

ASSUME \A id \in McastMsgID : id \in Nat

ASSUME \A msg \in McastMsg : msg \in [groupDest : SUBSET GroupSet,  
  type : ClientMsgStatus, id : McastMsgID]
  
ASSUME /\ \A msg \in McastMsg : \E id \in McastMsgID : msg.id = id
       /\ \A id \in McastMsgID : \E msg \in McastMsg : msg.id = id
       
ASSUME \A m1, m2 \in McastMsg : m1.id = m2.id => m1 = m2

GetMcastMsg == [id \in McastMsgID |-> CHOOSE m \in McastMsg : m.id = id]

IsMcastMsg(msg) == \E m \in McastMsg : m = msg

IsACCEPT(msg) == 
  /\ msg.mid \in McastMsgID
  /\ msg.group \in GroupSet
  /\ msg.cballot \in ValidBallot
  /\ msg.lts \in ValidTimestamp
  
  
IsACCEPT_ACK(msg) ==
  LET mcast == GetMcastMsg[msg.mid]
  IN /\ msg.mid \in McastMsgID
     /\ msg.group \in GroupSet
     /\ \A g \in GroupSet : g \in mcast.groupDest    => msg.balVec[g] \in ValidBallot
     /\ \A g \in GroupSet : g \notin mcast.groupDest => msg.balVec[g] = BallotNull
  
(* TODO: Refine the upper bound of bal *)  
IsDELIVER(msg) ==
  /\ msg.mid \in McastMsgID
  /\ msg.cballot \in Nat   
  /\ msg.lts \in ValidTimestamp
  /\ msg.gts \in ValidTimestamp
  
IsNEW_LEADER(msg) ==  
  /\ msg.ballot \in Nat   
  
IsNEW_LEADER_ACK(msg) ==
  /\ msg.ballot \in Nat
  /\ msg.cballot \in Nat
  /\ msg.clock \in Nat
  /\ \A mid \in McastMsgID : /\ msg.phase[mid] \in ProcMsgStatus
                             /\ msg.localTS[mid] \in Timestamp
                             /\ msg.globalTS[mid] \in Timestamp
                         
IsNEW_STATE(msg) ==                         
  /\ msg.ballot \in Nat  
  /\ msg.clock \in Nat
  /\ \A mid \in McastMsgID : /\ msg.phase[mid] \in ProcMsgStatus
                             /\ msg.localTS[mid] \in Timestamp
                             /\ msg.globalTS[mid] \in Timestamp

IsNEW_STATE_ACK(msg) ==                         
   
  /\ msg.ballot \in Nat  
  
IsProcMsg(msg) ==
  /\ msg.type \in MsgType \ {MULTICAST}
  /\ IF msg.type = ACCEPT 
     THEN IsACCEPT(msg)
     ELSE IF msg.type = ACCEPT_ACK 
     THEN IsACCEPT_ACK(msg)      
     ELSE IF msg.type = DELIVER 
     THEN IsDELIVER(msg)
     ELSE IF msg.type = NEW_LEADER 
     THEN IsNEW_LEADER(msg)
     ELSE IF msg.type = NEW_LEADER_ACK
     THEN IsNEW_LEADER_ACK(msg)
     ELSE IF msg.type = NEW_STATE
     THEN IsNEW_STATE(msg)
     ELSE IF msg.type = NEW_STATE_ACK
     THEN IsNEW_STATE_ACK(msg)
     ELSE FALSE 


(*
 *)  
PhaseInstance == [McastMsgID -> ProcMsgStatus]  



\* Type invariant                  
TypeOK == 
  /\ clock \in [Proc -> Nat]
  /\ phase \in [Proc -> PhaseInstance]
  /\ localTS \in [Proc -> [McastMsgID -> Timestamp]]  
  /\ gtsTemp \in [Proc -> [McastMsgID -> Timestamp]]
  /\ globalTS \in [Proc -> [McastMsgID -> Timestamp]]
  /\ status \in [Proc -> ProcStatus]
  /\ \A p \in Proc : ballot[p] \in Nat /\ cballot[p] \in Nat
  /\ Delivered \in [Proc -> [McastMsgID -> BOOLEAN]]  
  /\ \A p \in Proc : \A k \in DOMAIN deliver[p] : deliver[p][k] \in McastMsgID
  /\ max_delivered_gts \in [Proc -> Timestamp]
  /\ mcasted \in [GroupSet -> SUBSET McastMsg]
  /\ \A p \in Proc, mcastID \in McastMsgID : accFrom[p][mcastID] \subseteq Proc
  /\ \A p \in Proc, mcastID \in McastMsgID, g \in GroupSet : aackCter[p][mcastID][g] \in 0..N
  /\ \A p \in Proc : lackCter[p] \in 0..N
  /\ \A p \in Proc : sackCter[p] \in 0..N
  /\ \A s \in Proc, t \in Proc : \A k \in DOMAIN chan[s][t]: 
        IsProcMsg(chan[s][t][k]) \/ IsMcastMsg(chan[s][t][k])
  /\ \A m1, m2 \in McastMsgID : mcastLess[m1][m2] \in BOOLEAN  
  /\ flag \in BOOLEAN
  /\ \A p, q \in Proc : \A k \in DOMAIN outBuf[p][q] : IsProcMsg(outBuf[p][q][k])
  /\ \A p \in Proc : \A mid \in McastMsgID : \A g \in GroupSet : 
        BalVec[p][mid][g] \in ValidBallot \cup {BallotNull}   
  /\ \A g \in GroupSet : \A k \in DOMAIN mcastStream[g] : mcastStream[g][k] \in McastMsgID         
  /\ \A p \in Proc : cbTemp[p] \in Nat        

\* Integrity: Every process delivers every message at most once               
Integrity == \A s \in Proc : \A k1, k2 \in DOMAIN deliver[s] : deliver[s][k1] = deliver[s][k2] => k1 = k2   

\* Validity: If a process delivers message m, then some process multicasts m before.     
Validity == \A p \in Proc : \A k \in DOMAIN deliver[p] : LET msg == GetMcastMsg[deliver[p][k]]
                                                             g == GetGroup[p]
                                                         IN msg \in mcasted[g]

\* Whether process self is one of receivers of message mcastMsg. Recall that Dest(m) (in the 
\* paper) is the set of process groups. 
isMcastRcver(self, mcastMsg) == \E group \in mcastMsg.groupDest : self \in group  

\* There exists process p such that p delivered m1 before m2.      
DeliverBefore(m1, m2) ==
  /\ m1 # m2
  /\ \E p \in Proc : /\ isMcastRcver(p, m1)
                     /\ isMcastRcver(p, m2)
                     /\ \E k1 \in DOMAIN deliver[p] : /\ deliver[p][k1] = m1.id
                                                      /\ \A k2 \in 1..(k1 - 1) : deliver[p][k2] # m2.id

AsymDeliveryOrder == \A m1, m2 \in McastMsgID: m1 # m2 => ~(DeliverBefore(m1, m2) /\ DeliverBefore(m2, m1))

DeliveryOrder == \A m1, m2 \in McastMsgID:  ~(mcastLess[m1][m2] /\ mcastLess[m2][m1])
  
Stamp(t, g) == [time |-> t, group |-> g]

\* Send one message to a list of processes.
SendOneMsgToMany(snder, rcvers, info) ==
  outBuf' = [p \in Proc |-> [q \in Proc |-> 
                IF p = snder /\ q \in rcvers THEN << info >>
                ELSE << >>]]                 
                  
SendOneMsgToOne(snder, rcver, info) ==
  outBuf' = [p \in Proc |-> [q \in Proc |-> 
                IF p = snder /\ q = rcver THEN << info >>
                ELSE << >>]]                  
                  
SendManyMsgsToMany(snder, rcvers, infoSeq) ==
  outBuf' = [p \in Proc |-> [q \in Proc |-> 
                IF p = snder /\ q \in rcvers THEN infoSeq
                ELSE << >>]]
                  
NatMax(set) ==  
  IF Cardinality(set) = 0 THEN -1
  ELSE CHOOSE max \in set : \A e \in set : e <= max                          

timestampLess(ts1, ts2) ==
  \/ ts1.time < ts2.time
  \/ /\ ts1.time = ts2.time
     /\ GroupOrder[ts1.group][ts2.group]
     
MaxTimestamp(set) ==
  CHOOSE ts \in set : \A ts1 \in set \ {ts} : timestampLess(ts1, ts)              
              
AvailableDelivery_AcceptAck(self, msg) ==
  /\ phase'[self][msg] = COMMITTED  
  /\ Delivered[self][msg] = FALSE
  /\ \A m \in McastMsgID : phase'[self][m] \in {PROPOSED, ACCEPTED} => 
                              timestampLess(globalTS'[self][msg], localTS'[self][m])  
                              
AvailableDelivery_NewStateAck(self, msg) ==
  /\ phase'[self][msg] = COMMITTED  
  /\ \A m \in McastMsgID : phase'[self][m] = ACCEPTED => 
                              timestampLess(globalTS'[self][msg], localTS'[self][m])                              
                              
RECURSIVE DeliverySort(_, _)       
  
DeliverySort(self, set) ==
  IF set = {} THEN << >>
  ELSE LET maxTimestamp == CHOOSE elem \in set : \A x \in (set \ {elem}) : timestampLess(globalTS'[self][x], globalTS'[self][elem])
       IN Append(DeliverySort(self, set \ {maxTimestamp}), maxTimestamp)
      
CONSTANT MCASTSTREAM                      

ASSUME /\ DOMAIN MCASTSTREAM = GroupSet
       /\ \A g \in GroupSet : \A k \in DOMAIN MCASTSTREAM[g] : MCASTSTREAM[g][k] \in McastMsgID  

Init ==  
  /\ clock = [p \in Proc |-> 0]  
  /\ phase = [p \in Proc |-> [m \in McastMsgID|-> START]]
  /\ localTS = [p \in Proc |-> [m \in McastMsgID|-> TimestampNull]]
  /\ globalTS = [p \in Proc |-> [m \in McastMsgID|-> TimestampNull]]
  /\ gtsTemp = [p \in Proc |-> [m \in McastMsgID|-> TimestampNull]]
  /\ status = [p \in Proc |-> FOLLOWER]
  /\ cballot = [p \in Proc |-> 0] 
  /\ ballot = [p \in Proc |-> 0]    
  /\ Delivered = [p \in Proc |-> [m \in McastMsgID|-> FALSE]]
  /\ deliver = [p \in Proc |-> << >>]
  /\ max_delivered_gts = [p \in Proc |-> TimestampNull]
  /\ mcasted = [g \in GroupSet |-> {}]
  /\ accFrom = [p \in Proc |-> [mid \in McastMsgID |-> {}]]
  /\ aackCter = [p \in Proc |-> [mid \in McastMsgID |-> [g \in GroupSet |-> 0]]]
  /\ lackCter = [p \in Proc |-> 0]
  /\ sackCter = [p \in Proc |-> 0]
  /\ outBuf = [p \in Proc |-> [q \in Proc |-> << >> ]]
  /\ chan = [p \in Proc |-> [q \in Proc |-> << >> ]]
  /\ mcastLess = [m1 \in McastMsgID |-> [m2 \in McastMsgID |-> FALSE]]
  /\ flag = FALSE
  /\ BalVec = [p \in Proc |-> [mid \in McastMsgID |-> [g \in GroupSet |-> BallotNull]]]
  /\ Print(<<LeaderIn, GroupOrder>>, TRUE)       
  /\ mcastStream = MCASTSTREAM 
  /\ cbTemp = [p \in Proc |-> 0]

NotSend == outBuf' = [p \in Proc |-> [q \in Proc |-> << >>]]

NoLocalComputation == 
  /\ UNCHANGED << clock, phase, localTS, globalTS, cballot, Delivered, deliver, 
          max_delivered_gts, status, ballot, BalVec, cbTemp, gtsTemp >>
  /\ NotSend

NotUpdateLess == ~flag

UpdateChan(exChan, currOutBuf) ==
  chan' = [p \in Proc |-> [q \in Proc |-> exChan[p][q] \circ currOutBuf[p][q]]]

NotSaveMsg == UNCHANGED << accFrom, aackCter, lackCter, sackCter >>    

DeleteMsgsFromG0(p) == 
  LET g0 == GetGroup[p]
  IN /\ lackCter' = [lackCter EXCEPT ![p] = 0]
     /\ sackCter' = [sackCter EXCEPT ![p] = 0]
     /\ aackCter' = [aackCter EXCEPT ![p] = [mid \in McastMsgID |->
                       [g \in GroupSet |-> 0]]]
     /\ accFrom' = [accFrom EXCEPT ![p] = [mid \in McastMsgID |->
                       {snder \in accFrom[p][mid] : snder \notin g0}]]

Handle_NewLeader(p, leaderCand, msg) ==
  IF ballot[p] < msg.ballot
  THEN /\ UNCHANGED << clock, phase, localTS, globalTS, cballot, Delivered, deliver, max_delivered_gts, BalVec, cbTemp >>
       /\ UNCHANGED << accFrom, aackCter, gtsTemp >>       
       /\ LET g0 == GetGroup[p]
              newBal == msg.ballot
              info == [type |-> NEW_LEADER_ACK, ballot |-> ballot'[p], cballot |-> cballot'[p], 
                         clock |-> clock'[p], phase |-> phase'[p], localTS |-> localTS'[p], 
                         globalTS |-> globalTS'[p]]                         
          IN /\ status' = [status EXCEPT ![p] = RECOVERING]
             /\ ballot' = [ballot EXCEPT ![p] = newBal]
             /\ SendOneMsgToOne(p, leaderCand, info)             
             /\ lackCter' = [lackCter EXCEPT ![p] = 0]
             /\ sackCter' = [sackCter EXCEPT ![p] = 0]          
  ELSE /\ NotSaveMsg
       /\ NoLocalComputation     

MaxClock(newestAckMsg) ==
  LET msg == CHOOSE m \in newestAckMsg : \A m1 \in newestAckMsg :
                      m1.clock <= m.clock
  IN msg.clock

  
IsExpiredNewLeaderAck(p, msg) ==
  \/ status[p] # RECOVERING 
  \/ msg.ballot < ballot[p]  
  \/ LET g0 == GetGroup[p]
     IN lackCter[p] >= QuorumGuard[g0]      
                       
mergeLog(p, mid, ackMsg) ==
  IF phase[p][mid] < ackMsg.phase[mid] 
  THEN [phase |-> ackMsg.phase[mid], lts |-> ackMsg.localTS[mid], 
               gts |-> ackMsg.globalTS[mid]]
  ELSE [phase |-> phase[p][mid], lts |-> localTS[p][mid], 
               gts |-> globalTS[p][mid]]                        

Handle_NewLeaderAck(p, msg) ==
  IF IsExpiredNewLeaderAck(p, msg)
  THEN /\ NoLocalComputation
       /\ NotSaveMsg
  ELSE IF status[p] = RECOVERING /\ ballot[p] = msg.ballot
  THEN /\ lackCter' = [lackCter EXCEPT ![p] = lackCter[p] + 1]        
       /\ UNCHANGED << accFrom, aackCter, gtsTemp >>
       /\ IF cbTemp[p] > msg.cballot 
          THEN UNCHANGED << phase, localTS, globalTS, clock, cbTemp >>
          ELSE IF cbTemp[p] = msg.cballot
          THEN LET bind == [m \in McastMsgID |-> mergeLog(p, m, msg)]
               IN /\ phase' = [phase EXCEPT ![p] = [m \in McastMsgID |-> bind[m].phase]]
                  /\ localTS' = [localTS EXCEPT ![p] = [m \in McastMsgID |-> bind[m].lts]]  
                  /\ globalTS' = [globalTS EXCEPT ![p] = [m \in McastMsgID |-> bind[m].gts]]
                  /\ UNCHANGED cbTemp
                  /\ IF clock[p] < msg.clock 
                     THEN clock' = [clock EXCEPT ![p] = msg.clock] 
                     ELSE UNCHANGED clock
                  /\ UNCHANGED cbTemp 
          ELSE /\ cbTemp[p] < msg.cballot
               /\ phase' = [phase EXCEPT ![p] = msg.phase]
               /\ localTS' = [localTS EXCEPT ![p] = msg.localTS]
               /\ globalTS' = [globalTS EXCEPT ![p] = msg.globalTS]
               /\ cbTemp' = [cbTemp EXCEPT ![p] = msg.cballot]
               /\ clock' = [clock EXCEPT ![p] = msg.clock] 
       /\ LET g0 == GetGroup[p]                      
          IN IF lackCter'[p] = QuorumGuard[g0]
             THEN LET info == [type |-> NEW_STATE, ballot |-> msg.ballot, clock |-> clock'[p], phase |-> phase'[p], 
                             localTS |-> localTS'[p], globalTS |-> globalTS'[p]]
                  IN /\ UNCHANGED << status, ballot,  Delivered, deliver, max_delivered_gts, BalVec >>      
                     /\ cballot' = [cballot EXCEPT ![p] = msg.ballot]               
                     /\ SendOneMsgToMany(p, g0 \ {p}, info)
                     /\ sackCter' = [sackCter EXCEPT ![p] = 1]
                     /\ UNCHANGED << accFrom, aackCter >>
             ELSE /\ NotSend 
                  /\ UNCHANGED << status, ballot, cballot, Delivered, deliver, max_delivered_gts, BalVec, 
                        accFrom, aackCter, sackCter >>        
  ELSE Print("NewLeaderAck_Error", TRUE)
                   
IsExpiredNewState(p, msg) ==
  \/ /\ status[p] # RECOVERING 
  \/ /\ msg.ballot < ballot[p] 
     
Handle_NewState(p, leaderCand, msg) ==
  IF IsExpiredNewState(p, msg)
  THEN /\ NotSaveMsg
       /\ NoLocalComputation 
  ELSE IF status[p] = RECOVERING /\ ballot[p] = msg.ballot  
       THEN /\ UNCHANGED << ballot, Delivered, deliver, max_delivered_gts, BalVec, gtsTemp >>
            /\ status' = [status EXCEPT ![p] = FOLLOWER]
            /\ cballot'= [cballot EXCEPT ![p] = msg.ballot]
            /\ clock' = [clock EXCEPT ![p] = msg.clock]
            /\ phase' = [phase EXCEPT ![p] = msg.phase]
            /\ localTS' = [localTS EXCEPT ![p] = msg.localTS]
            /\ globalTS' = [globalTS EXCEPT ![p] = msg.globalTS]
            /\ cbTemp' = [cbTemp EXCEPT ![p] = cballot'[p]]
            /\ LET info == [type |-> NEW_STATE_ACK, ballot |-> ballot'[p]]
               IN SendOneMsgToOne(p, leaderCand, info)
            /\ DeleteMsgsFromG0(p)   
        ELSE /\ NotSaveMsg
             /\ NoLocalComputation             
  
IsExpiredNewStateAck(p, msg) ==
  \/ status[p] # RECOVERING 
  \/ msg.ballot < ballot[p] 
            
Handle_NewStateAck(p, msg) ==
  IF IsExpiredNewStateAck(p, msg)
  THEN /\ NoLocalComputation
       /\ NotSaveMsg
  ELSE IF /\ status[p] = RECOVERING 
          /\ ballot[p] = msg.ballot
       THEN IF sackCter[p] + 1 = QuorumGuard[GetGroup[p]] 
            THEN LET g0 == GetGroup[p]   
                 IN /\ UNCHANGED << ballot, deliver, max_delivered_gts, cballot, clock, globalTS, localTS, phase, BalVec, gtsTemp >>   
                    /\ status' = [status EXCEPT ![p] = LEADER]
                    /\ cbTemp' = [cbTemp EXCEPT ![p] = cballot'[p]]          
                    /\ DeleteMsgsFromG0(p)
                    /\ LET newDelivery == { m \in McastMsgID : AvailableDelivery_NewStateAck(p, m)}
                       IN IF newDelivery # {}     
                          THEN LET deliverySeq == DeliverySort(p, newDelivery) 
                                   infoSeq == [k \in DOMAIN deliverySeq |-> 
                                                  [type |-> DELIVER, cballot |-> cballot'[p], mid |-> deliverySeq[k],  
                                                   lts |-> localTS'[p][deliverySeq[k]], gts |-> globalTS'[p][deliverySeq[k]]]]
                               IN /\ Delivered' = [Delivered EXCEPT ![p] = [m \in McastMsgID |-> 
                                                          IF m \in newDelivery THEN TRUE ELSE Delivered[p][m]]]
                                  /\ SendManyMsgsToMany(p, g0, infoSeq)
                          ELSE /\ UNCHANGED << Delivered >>
                               /\ NotSend  
            ELSE /\ NotSend
                 /\ sackCter' = [sackCter EXCEPT ![p] = sackCter[p] + 1]
                 /\ UNCHANGED << status, ballot,  Delivered, deliver, max_delivered_gts, cballot, clock,   
                        globalTS, localTS, phase, BalVec, accFrom, aackCter, lackCter, gtsTemp, cbTemp >>
       ELSE Print("NewStateAck_Error", TRUE) 
            
Handle_Multicast(p, msg) ==
  IF status[p] = LEADER
  THEN LET mid == msg.id
           g0 == GetGroup[p]
           rcvers == UNION msg.groupDest
           t == clock[p] + 1
           newStamp == Stamp(t, g0)
           data == [type |-> ACCEPT, mid |-> mid, group |-> g0, cballot |-> cballot'[p], lts |-> newStamp] 
       IN /\ UNCHANGED << globalTS, status, ballot, cballot,  Delivered, deliver, max_delivered_gts, BalVec,
                  accFrom, aackCter, lackCter, sackCter, cbTemp, gtsTemp >>
          /\ clock' = [clock EXCEPT ![p] = t]        
          /\ localTS' = [localTS EXCEPT ![p][mid] = newStamp]          
          /\ phase' = [phase EXCEPT ![p][mid] = PROPOSED]
          /\ NotSaveMsg           
          /\ SendOneMsgToMany(p, rcvers, data)    
  ELSE /\ NoLocalComputation
       /\ NotSaveMsg
       
FreshMcast(p, mcast) == 
  LET g == GetGroup[p] 
  IN mcast \notin mcasted[g]          
          
\* If we don't encode re_multicast and retry, do we have
\*  a) is expiredAccept always empty?
\*  b) is Deliver[p][mid] always false?

IsExpiredAccept(p, msg) ==
  \/ LET g0 == GetGroup[p] 
     IN /\ msg.group = g0
        /\ msg.cballot < ballot[p]
  \/ Delivered[p][msg.mid]
  
  
UpdateOnlyBalVec(p, msg) ==   
  
  /\ UNCHANGED << clock, phase, localTS, globalTS, cballot, Delivered, deliver, 
          max_delivered_gts, status, ballot >>
  /\ NotSend
             
Handle_Accept(p, snder, msg) ==
  IF IsExpiredAccept(p, msg)
  THEN /\ NoLocalComputation
       /\ NotSaveMsg
  ELSE LET mid == msg.mid
           mcast == GetMcastMsg[mid]
           g0 == GetGroup[p]
       IN /\ accFrom' = [accFrom EXCEPT ![p][mid] = accFrom[p][mid] \cup {snder}]
          /\ BalVec' = [BalVec EXCEPT ![p][msg.mid][GetGroup[snder]] = msg.cballot]
          /\ IF timestampLess(gtsTemp[p][mid], msg.lts)
             THEN gtsTemp' = [gtsTemp EXCEPT ![p][mid] = msg.lts]
             ELSE UNCHANGED gtsTemp
          /\ IF snder \in g0
             THEN localTS' = [localTS EXCEPT ![p][mid] = msg.lts]
             ELSE UNCHANGED localTS
          /\ IF \A g \in mcast.groupDest : \E leader \in accFrom'[p][mid] : leader \in g
             THEN /\ clock' = [clock EXCEPT ![p] = NatMax({clock[p], gtsTemp'[p][mid].time})]
                  /\ IF /\ \A g \in mcast.groupDest : aackCter[p][mid][g] >= QuorumGuard[g]
                        /\ cballot[p] = BalVec'[p][mid][g0]
                        /\ status[p] = LEADER
                     THEN /\ phase' = [phase EXCEPT ![p][mid] = COMMITTED]
                          /\ globalTS' = [globalTS EXCEPT ![p][mid] = gtsTemp'[p][mid]]
                          /\ UNCHANGED << status, ballot, cballot, deliver, max_delivered_gts, 
                                            cbTemp, aackCter, lackCter, sackCter >>
                          /\ LET newDelivery == { m \in McastMsgID : AvailableDelivery_AcceptAck(p, m) }
                             IN IF newDelivery # {}     
                                THEN LET deliverySeq == DeliverySort(p, newDelivery) 
                                         infoAack == << [type |-> ACCEPT_ACK, mid |-> mid, group |-> g0, balVec |-> BalVec'[p][mid]] >>
                                         infoDelivery == [k \in DOMAIN deliverySeq |-> [type |-> DELIVER, cballot |-> cballot'[p], mid |-> deliverySeq[k],  
                                           lts |-> localTS'[p][deliverySeq[k]], gts |-> globalTS'[p][deliverySeq[k]]]]
                                     IN /\ Delivered' = [Delivered EXCEPT ![p] = [m \in McastMsgID |-> 
                                                            IF m \in newDelivery THEN TRUE 
                                                            ELSE Delivered[p][m]]]
                                        /\ outBuf' = [s \in Proc |-> [t \in Proc |-> 
                                                        IF s = p THEN IF t = snder /\ t \in g0 
                                                                      THEN infoAack \circ infoDelivery
                                                                      ELSE IF t # snder /\ t \in g0 THEN infoDelivery
                                                                      ELSE IF t = snder /\ t \notin g0 THEN infoAack
                                                                      ELSE << >>
                                                        ELSE << >>]]
                                ELSE /\ UNCHANGED << Delivered >>
                                     /\ NotSend
                     ELSE /\ IF phase[p][mid] \in {START, PROPOSED} 
                             THEN phase' = [phase EXCEPT ![p][mid] = ACCEPTED]
                             ELSE UNCHANGED phase
                          /\ UNCHANGED << globalTS, status, ballot, cballot, Delivered, deliver, max_delivered_gts, aackCter,
                                cbTemp, lackCter, sackCter >>
                          /\ LET info == [type |-> ACCEPT_ACK, mid |-> mid, group |-> g0, balVec |-> BalVec'[p][mid]] 
                             IN SendOneMsgToMany(p, accFrom'[p][mid], info)      
             ELSE /\ UNCHANGED << clock, phase, globalTS, status, ballot, cballot, Delivered, deliver, 
                        max_delivered_gts, cbTemp, aackCter, lackCter, sackCter >>
                  /\ NotSend
            
            
            
            
            
           
            
IsExpiredAcceptAck(p, snder, msg) ==
  \/ status[p] # LEADER
  \/ LET mid == msg.mid
         g0 == GetGroup[p]
         g1 == GetGroup[snder]
     IN \/ phase[p][msg.mid] = COMMITTED  
        \/ Delivered[p][msg.mid]               
        \/ msg.balVec[g0] < ballot[p]
        \/ aackCter[p][mid][g1] = QuorumGuard[g1]
             
Handle_AcceptAck(p, snder, msg) ==
  IF IsExpiredAcceptAck(p, snder, msg)
  THEN /\ NoLocalComputation
       /\ NotSaveMsg
  ELSE LET mid == msg.mid
           mcast == GetMcastMsg[mid]
           g0 == GetGroup[p]
           g1 == GetGroup[snder]
       IN /\ aackCter' = [aackCter EXCEPT ![p][mid][g1] = aackCter[p][mid][g1] + 1]
          /\ IF /\ \A g \in mcast.groupDest : aackCter'[p][mid][g] >= QuorumGuard[g]
                /\ \A g \in mcast.groupDest : \E leader \in accFrom[p][mid] : leader \in g 
             THEN IF /\ status[p] = LEADER
                     /\ cballot[p] = msg.balVec[g0]
                  THEN /\ phase' = [phase EXCEPT ![p][mid] = COMMITTED]
                       /\ globalTS' = [globalTS EXCEPT ![p][mid] = gtsTemp[p][mid]]                 
                       /\ UNCHANGED << clock, localTS, gtsTemp, status, ballot, cballot, deliver, max_delivered_gts, BalVec,
                           cbTemp, accFrom, lackCter, sackCter >>
                       /\ LET newDelivery == { m \in McastMsgID : AvailableDelivery_AcceptAck(p, m) }
                          IN IF newDelivery # {}     
                             THEN LET deliverySeq == DeliverySort(p, newDelivery) 
                                      infoSeq == [k \in DOMAIN deliverySeq |-> [type |-> DELIVER, cballot |-> cballot'[p], mid |-> deliverySeq[k],  
                                                    lts |-> localTS'[p][deliverySeq[k]], gts |-> globalTS'[p][deliverySeq[k]]]]
                                  IN /\ Delivered' = [Delivered EXCEPT ![p] = [m \in McastMsgID |-> 
                                                         IF m \in newDelivery THEN TRUE 
                                                         ELSE Delivered[p][m]]]
                                     /\ SendManyMsgsToMany(p, g0, infoSeq)
                             ELSE /\ UNCHANGED << Delivered >>
                                  /\ NotSend
                  ELSE /\ UNCHANGED << clock, phase, localTS, globalTS, gtsTemp, status, ballot, cballot, Delivered, deliver, 
                           max_delivered_gts, BalVec, cbTemp, accFrom, lackCter, sackCter >>
                       /\ NotSend    
             ELSE /\ UNCHANGED << clock, phase, localTS, globalTS, gtsTemp, status, ballot, cballot, Delivered, deliver, 
                        max_delivered_gts, BalVec, cbTemp, accFrom, lackCter, sackCter >>
                  /\ NotSend
          
Handle_Deliver(p, msg) ==
  IF /\ status[p] \in {LEADER, FOLLOWER}
     /\ cballot[p] = msg.cballot
     /\ timestampLess(max_delivered_gts[p], msg.gts)
  THEN LET mid == msg.mid 
       IN /\ UNCHANGED << status, ballot, cballot, BalVec, accFrom, aackCter, lackCter, sackCter, cbTemp, gtsTemp >>          
          /\ phase' = [phase EXCEPT ![p][mid] = COMMITTED]
          /\ localTS' = [localTS EXCEPT ![p][mid] = msg.lts]
          /\ globalTS' = [globalTS EXCEPT ![p][mid] = msg.gts]
          /\ clock' = [clock EXCEPT ![p] = NatMax({clock[p], msg.gts.time})]
          /\ max_delivered_gts' = [max_delivered_gts EXCEPT ![p] = msg.gts]
          /\ deliver' = [deliver EXCEPT ![p] = Append(deliver[p], mid) ]
          /\ Delivered' = [Delivered EXCEPT ![p][mid] = TRUE ]
          /\ NotSend
  ELSE /\ NoLocalComputation
       /\ NotSaveMsg  
       
UpdateMcastLess ==  
  /\ mcastLess' = [id1 \in McastMsgID |-> [id2 \in McastMsgID |->
        \/ LET m1 == GetMcastMsg[id1]
               m2 == GetMcastMsg[id2]
           IN DeliverBefore(m1, m2) 
        \/ \E id3 \in McastMsgID : mcastLess[id1][id3] /\ mcastLess[id3][id2]]]
  /\ flag' = (mcastLess # mcastLess')   
  (*/\ IF mcastLess' = mcastLess /\ flag' = flag THEN Print(1, TRUE)
     ELSE Print(2, TRUE)*)

(*                                      
ReachBounds ==
  /\ \A mcast \in McastMsg : \A g \in GroupSet : 
        g \in mcast.groupDest => mcast \in mcasted[g]
  /\ \A p, q \in Proc : chan[p][q] = << >>
  /\ \A g \in GroupSet, mid \in McastMsgID : 
          ( \E p \in g : Delivered[p][mid] )
       => ( \E q \in g : phase[q][mid] \in {ACCEPTED, COMMITTED} )
  /\ \A mid \in McastMsgID :
        ((\E p \in Proc : Delivered[p][mid] = FALSE)
            => (\E p \in Proc : 
                    \/ globalTS[p][mid] = TimestampNull
                    \/ \E mid1 \in McastMsgID : 
                            /\ globalTS[p][mid1] = TimestampNull
                            /\ localTS[p][mid1] # TimestampNull
                            /\ timestampLess(localTS[p][mid1], globalTS[p][mid])))
  /\ UpdateMcastLess
  (*/\ Print(<<mcastLess, mcastLess'>>, TRUE)*)
  /\ mcastLess = mcastLess'
  /\ UNCHANGED << clock, phase, localTS, globalTS, status, ballot, cballot, 
        Delivered, deliver, max_delivered_gts, mcastStream,
        mcasted, aackCter, lackCter, sackCter, chan, outBuf, BalVec,
        accFrom, cbTemp, gtsTemp  >>
        
ReachBounds0 ==
  /\ UpdateMcastLess
  /\ UNCHANGED << clock, phase, localTS, globalTS, status, ballot, cballot, 
        Delivered, deliver, max_delivered_gts, mcastStream,
        mcasted, aackCter, lackCter, sackCter, chan, outBuf, BalVec,
        accFrom, cbTemp, gtsTemp  >>      
  *)
  
ReachBounds ==
  /\ \A g \in GroupSet : mcastStream[g] = << >> 
  /\ \A p, q \in Proc : chan[p][q] = << >>
  /\ \A g \in GroupSet, mid \in McastMsgID : 
          ( \E p \in g : Delivered[p][mid] )
       => ( \E q \in g : phase[q][mid] \in {ACCEPTED, COMMITTED} )
  /\ UpdateMcastLess
  /\ UNCHANGED << clock, phase, localTS, globalTS, status, ballot, cballot, 
        Delivered, deliver, max_delivered_gts, mcastStream,
        mcasted, aackCter, lackCter, sackCter, chan, outBuf, BalVec,
        accFrom, cbTemp, gtsTemp  >>             


UpdateDeliveryOrder ==
  /\ flag
  /\ UpdateMcastLess
  /\ UNCHANGED << clock, phase, localTS, globalTS, status, ballot, cballot, 
           Delivered, deliver, max_delivered_gts,
           mcasted, aackCter, lackCter, sackCter, chan, outBuf, BalVec, mcastStream,
           accFrom, cbTemp, gtsTemp  >>
         
UnchangeDeliveryOrder == UNCHANGED << mcastLess, flag >>
   
UpdateMcasted(p, mcast) ==
  LET g == GetGroup[p]
  IN mcasted' = [mcasted EXCEPT ![g] = mcasted[g] \cup {mcast}]      
            
Receive_WhenNormal(rcver) ==  
  /\ \E snder \in Proc :
        /\ chan[snder][rcver] # << >>
        /\ LET msg == Head(chan[snder][rcver])
               inTransit == [chan EXCEPT ![snder][rcver] = Tail(chan[snder][rcver])]
           IN /\ IF msg.type = NEW_LEADER    
                 THEN /\ Handle_NewLeader(rcver, snder, msg)
                      /\ UnchangeDeliveryOrder
                 ELSE IF msg.type = NEW_LEADER_ACK    
                 THEN /\ Handle_NewLeaderAck(rcver, msg)
                      /\ UnchangeDeliveryOrder
                 ELSE IF msg.type = NEW_STATE     
                 THEN /\ Handle_NewState(rcver, snder, msg)
                      /\ UnchangeDeliveryOrder
                 ELSE IF msg.type = NEW_STATE_ACK     
                 THEN /\ Handle_NewStateAck(rcver, msg)
                      /\ UnchangeDeliveryOrder
                 ELSE IF msg.type = ACCEPT
                 THEN /\ ballot[rcver] > 0
                      /\ Handle_Accept(rcver, snder, msg)
                      /\ UnchangeDeliveryOrder
                 ELSE IF msg.type = ACCEPT_ACK
                 THEN /\ ballot[rcver] > 0
                      /\ Handle_AcceptAck(rcver, snder, msg)
                      /\ UnchangeDeliveryOrder
                 ELSE /\ msg.type = DELIVER
                      /\ ballot[rcver] > 0           
                      /\ Handle_Deliver(rcver, msg)
                      /\ IF status[rcver] = LEADER /\ deliver[rcver] # deliver'[rcver] 
                         THEN UpdateMcastLess
                         ELSE UNCHANGED << mcastLess, flag >>
              /\ UpdateChan(inTransit, outBuf')
              /\ UNCHANGED << mcasted, mcastStream >>
              
ReceiveMcast(p) ==
  /\ status[p] = LEADER
  /\ ballot[p] > 0  
  /\ LET g0 == GetGroup[p] 
     IN /\ mcastStream[g0] # <<>>
        /\ LET mcastID == Head(mcastStream[g0])
               mcast == GetMcastMsg[mcastID]  
           IN /\ isMcastRcver(p, mcast)
              /\ FreshMcast(p, mcast)
              /\ UpdateMcasted(p, mcast)
              /\ Handle_Multicast(p, mcast)
              /\ UnchangeDeliveryOrder
              /\ UpdateChan(chan, outBuf')
              /\ mcastStream' = [mcastStream EXCEPT ![g0] = Tail(mcastStream[g0])]
        
Receive_WhenRecovering(rcver) ==  
  \E snder \in GetGroup[rcver] :
        /\ chan[snder][rcver] # << >>
        /\ LET msg == Head(chan[snder][rcver])
               inTransit == [chan EXCEPT ![snder][rcver] = Tail(chan[snder][rcver])]
           IN /\ IF msg.type = NEW_LEADER    
                 THEN Handle_NewLeader(rcver, snder, msg)
                 ELSE IF msg.type = NEW_LEADER_ACK    
                 THEN Handle_NewLeaderAck(rcver, msg)
                 ELSE IF msg.type = NEW_STATE     
                 THEN Handle_NewState(rcver, snder, msg)
                 ELSE IF msg.type = NEW_STATE_ACK     
                 THEN Handle_NewStateAck(rcver, msg)
                 ELSE IF msg.type = ACCEPT
                 THEN Handle_Accept(rcver, snder, msg)
                 ELSE IF msg.type = ACCEPT_ACK
                 THEN /\ Handle_AcceptAck(rcver, snder, msg)
                      /\ UnchangeDeliveryOrder
                 ELSE /\ msg.type = DELIVER           
                      /\ Handle_Deliver(rcver, msg)
                      /\ IF status[rcver] = LEADER /\ deliver[rcver] # deliver'[rcver] 
                         THEN UpdateMcastLess
                         ELSE UNCHANGED << mcastLess, flag >>
              /\ UnchangeDeliveryOrder
              /\ UpdateChan(inTransit, outBuf')
              /\ UNCHANGED << mcasted, mcastStream >>
              
Recover(p) ==
  /\ status[p] = FOLLOWER
  (* /\ p = 2 => Delivered[p][1] *)
  /\ \E newBal \in (ballot[p] + 1)..BalMax:
          /\ p = LeaderIn[GetGroup[p]][newBal]        
          /\ LET info == [type |-> NEW_LEADER, ballot |-> newBal]
                 g0 == GetGroup[p] 
                 rcvers == g0 \ {p}
             IN IF rcvers # {} 
                THEN /\ UNCHANGED << clock, phase, localTS, globalTS, cballot, Delivered, deliver,     
                          max_delivered_gts, mcasted, accFrom, aackCter, BalVec, gtsTemp >>
                     /\ lackCter' = [lackCter EXCEPT ![p] = 1]
                     /\ sackCter' = [sackCter EXCEPT ![p] = 0] 
                     /\ cbTemp' = [cbTemp EXCEPT ![p] = cballot[p]]
                     /\ status' = [status EXCEPT ![p] = RECOVERING]
                     /\ ballot' = [ballot EXCEPT ![p] = newBal]
                     /\ SendOneMsgToMany(p, rcvers, info)
                ELSE /\ status' = [status EXCEPT ![p] = LEADER]
                     /\ ballot' = [ballot EXCEPT ![p] = newBal]
                     /\ cballot' = [cballot EXCEPT ![p] = newBal]
                     /\ cbTemp' = [cbTemp EXCEPT ![p] = cballot'[p]]
                     /\ NotSend
                     /\ UNCHANGED << clock, phase, localTS, globalTS, chan, Delivered, deliver,      
                          max_delivered_gts, mcasted, accFrom, aackCter, lackCter, sackCter, BalVec, gtsTemp >>
  /\ UnchangeDeliveryOrder
  /\ UpdateChan(chan, outBuf')
  /\ UNCHANGED << mcasted, mcastStream >>                          
                                
       
Next == 
  \/ \E p \in Proc :
        \/ /\ \/ status[p] = LEADER
              \/ status[p] = FOLLOWER          
           /\ NotUpdateLess
           /\ \/ ReceiveMcast(p)
              \/ Receive_WhenNormal(p)
              \/ Recover(p)
        \/ /\ status[p] = RECOVERING           
           /\ NotUpdateLess
           /\ Receive_WhenRecovering(p)           
  \/ UpdateDeliveryOrder 
  \/ ReachBounds 
       
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Jan 03 16:54:47 CET 2019 by tthai
\* Created Sat Dec 15 16:59:41 CET 2018 by tthai
