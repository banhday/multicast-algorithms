---------------- MODULE Skeen3_disable_symbolic_transitions ----------------

EXTENDS Integers,  FiniteSets, Sequences, TLC

a <: b == a


VARIABLE clock, phase, localTS, globalTS, deliver, rcvdMcastID, rcvdProposeMsg, mcastedID,   
            inTransit, front, Delivered, mcastGreater
  
vars == << clock, phase, localTS, globalTS, deliver, rcvdMcastID, rcvdProposeMsg, mcastedID, 
            inTransit, front, Delivered, mcastGreater >>



N == 3
Proc == 1..N
Group == {{p} : p \in Proc}  
GroupNull == {} <: {Int}
groupLess == [g1 \in Group |-> [g2 \in Group |-> 
                  \E p1 \in g1, p2 \in g2 : /\ \A p \in g1 : p <= p1
                                            /\ \A p \in g2 : p <= p2
                                            /\ p1 < p2 ]]        
       
Multicast == N * 10 + 1
Propose == Multicast + 1
Start == Propose + 1
Proposed == Start + 1
Committed == Proposed + 1 

MyNat == 0..100  
McastID == (N * 20 + 1) .. (N * 20 + 3)
McastMsgStatus == {Start, Proposed, Committed}
McastMsg == { [groupDest |-> {{1}, {2}}, data |-> [type |-> Multicast, id |-> (N * 20 + 1)]],
              [groupDest |-> {{2}, {3}}, data |-> [type |-> Multicast, id |-> (N * 20 + 2)]],
              [groupDest |-> {{3}, {1}}, data |-> [type |-> Multicast, id |-> (N * 20 + 3)]]  }
                            
McastPhase == [McastID -> McastMsgStatus]                              

\* Is a Multicast message
IsMcastMsg(msg) == \E m \in McastMsg : m = msg

\* TimestampNull: used in the initialization 
TimeNull == 0 
TimestampNull == [time |-> TimeNull, group |-> GroupNull]
Timestamp == [time : MyNat, group : Group \cup {GroupNull}]
 
\* Is a timestamp 
IsTimestamp(ts) == ts.group \in ( Group \cup {GroupNull} ) /\ ts.time \in MyNat

\* Is a Propose message
IsProposeMsg(msg) == 
  /\ msg.data.type = Propose
  /\ msg.source \in Proc
  /\ msg.dest \in Proc
  /\ \E m \in McastID : m = msg.data.mcastID
  /\ msg.data.g \in Group
  /\ IsTimestamp(msg.data.lts)  

\* Type invariant                  
TypeInv == 
  /\ clock \in [Proc -> MyNat]  
  /\ phase \in [Proc -> McastPhase]  
  /\ \A p \in Proc, id \in McastID : IsTimestamp(localTS[p][id])  
  /\ \A p \in Proc, id \in McastID : IsTimestamp(globalTS[p][id])
  /\ \A p \in Proc : \A k \in DOMAIN deliver[p] :  deliver[p][k] \in McastID
  /\ Delivered \in [Proc -> [McastID -> BOOLEAN]]  
  /\ \A p \in Proc : \A id \in rcvdMcastID[p] : id \in McastID
  /\ \A p \in Proc : \A msg \in rcvdProposeMsg[p] : IsProposeMsg(msg)
  /\ \A s \in Proc, t \in Proc : \A k \in DOMAIN inTransit[s][t]: IsProposeMsg(inTransit[s][t][k])    
  /\ \A snder, rcver \in Proc : front[snder][rcver] \in ( {0} \cup DOMAIN inTransit[snder][rcver])    
  /\ mcastGreater \in [McastID -> [McastID -> BOOLEAN]]  
  /\ mcastedID \subseteq McastID 
  
\* Integrity: Every process delivers every message at most once               
Integrity ==
  \A s \in Proc : \A k1, k2 \in DOMAIN deliver[s] : deliver[s][k1] = deliver[s][k2] => k1 = k2   


\* Validity: If a process delivers message m, then some process multicasts m before.     
Validity == \A p \in Proc : \A k \in DOMAIN deliver[p] : deliver[p][k] \in mcastedID 

\* Whether process self is one of receivers of message mcastMsg. Recall that Dest(m) (in the 
\* paper) is the set of process groups. 
isMcastRcver(self, mcastMsg) == ( \E group \in mcastMsg.groupDest : self \in group )  
\* isMcastRcver(self, mcastMsg) == ( \E group \in mcastMsg.groupDest : self \in group ) <: BOOLEAN


\* There exists process p such that p delivered m1 before m2.      
DeliverBefore(m1, m2) ==
  \E p \in Proc : /\ isMcastRcver(p, m1)
                  /\ isMcastRcver(p, m2)
                  /\ \E k2 \in DOMAIN deliver[p] : /\ deliver[p][k2] = m2.data.id
                                                   /\ \A k1 \in 1..(k2 - 1) : deliver[p][k1] # m1.data.id

(* The relation "less than" is asymmetric. In other words, for every pair of Broadcast messages m1 and m2, if there exists 
   server s1 such that s1 delivers m1 before m2, there exists no server s2 such that (i) s2 delivers m2 before delivering m1,  
   or (ii) s2 delivered m2, but not delivered m1.
 *) 
AsymDeliveryOrder == \A m1, m2 \in McastMsg : m1 # m2 => ~(DeliverBefore(m1, m2) /\ DeliverBefore(m2, m1))

DeliveryOrder == \A m1, m2 \in McastID :  ~(mcastGreater[m1][m2] /\ mcastGreater[m2][m1])

GlobalTotalDeliveryOrder == \A m1, m2 \in McastID :  ~(mcastGreater[m1][m2] /\ mcastGreater[m2][m1])
      
AllDeliveries == <>(\A msg \in McastMsg : \A p \in Proc : isMcastRcver(p, msg) => Delivered[p][msg.data.id])   
                 
Stamp(t, g) == [time |-> t, group |-> g]

\* The group to which process self belongs 
memberOfGroup == [p \in Proc |-> CHOOSE group \in Group : p \in group]

         
\* One message constructor for all kinds of messages in the protocol
OneMsgCtor(snder, rcver, info) == [source |-> snder, dest |-> rcver, data |-> info]

\* Send one message to a list of processes.
SendOneMsg(snder, rcvers, info) ==
  inTransit' = [p \in Proc |-> [q \in Proc |->  
                  IF p = snder /\ q \in rcvers
                  THEN Append(inTransit[p][q], OneMsgCtor(p, q, info))
                  ELSE inTransit[p][q]]]
                           
                                                                                                                                                               
ReceiveMcast(rcver, msg) ==  
  /\ msg.data.type = Multicast
  /\ isMcastRcver(rcver, msg)
  /\ rcvdMcastID' = [rcvdMcastID EXCEPT ![rcver] = rcvdMcastID[rcver] \cup {msg.data.id}]
  /\ UNCHANGED rcvdProposeMsg 

                                           
\* The primitive for receiving one message
\*  - There exisits implicitly an assumption about the hiararchy of messages in transit.
\*    This assumption is described by the first guards.
\*  - A message sent by a process to itself should be received immediately. In other words, 
\*    a process should receive all messages which it send to itself before
\*    receiving messages from others. 
\*  - m is the message which proc rcver has received in this transition.
\*  - slot is the slot containing m.
\*  - Increase front[snder][rcver] by 1 to mark that proc rcver has received message m.
\*  - Messages from front'[snder][rcver] to rear[snder][rcver] are in transit.  
\*  - Push message m to a list of message which proc rcver has received. 
ReceivePropose(rcver, snder, msg) ==
  /\ msg.data.type = Propose
  /\ front' = [front EXCEPT ![snder][rcver] = front[snder][rcver] + 1]  
  /\ rcvdProposeMsg' = [rcvdProposeMsg EXCEPT ![rcver] = rcvdProposeMsg[rcver] \cup {msg}]
  /\ UNCHANGED rcvdMcastID 
                                            
                          
\* The initialized states
\*  - Only one leader in the initialize state, other Proces are followers.
\*  - No faults has happened.
\*  - No client requests are stored at every Procs.   
\*  - Both ballot and cballot are initialized with 0
\*  - No client requests are known by a majority of Procs.
\*  - Every client has not received any message.
\*  - No message is in transit, in every communication channel.
Init ==  
  /\ clock = [p \in Proc |-> 0]
  /\ phase = [p \in Proc |-> [m \in McastID |-> Start]]
  /\ localTS = [p \in Proc |-> [m \in McastID |-> TimestampNull]]
  /\ globalTS = [p \in Proc |-> [m \in McastID |-> TimestampNull]]
  /\ Delivered = [p \in Proc |-> [m \in McastID |-> FALSE]]
  /\ rcvdMcastID = [p \in Proc |-> ({} <: {Int})]
  \* /\ rcvdProposeMsg = [p \in Proc |-> {} ] 
  
  /\ rcvdProposeMsg = [p \in Proc |-> ({} <: {[source |-> Int, 
                                               dest |-> Int, 
                                               data |-> [type |-> Int, 
                                                         mcastID |-> Int, 
                                                         g |-> {Int},
                                                         lts |-> [time |-> Int, group |-> {Int} ]]]}) ]
  
  /\ mcastedID = {} <: {Int}
  /\ inTransit = [p \in Proc |-> [q \in Proc |-> 
                    (<< >> <: Seq([source |-> Int, 
                                   dest |-> Int, 
                                   data |-> [type |-> Int, 
                                             mcastID |-> Int, 
                                             g |-> {Int},
                                             lts |-> [time |-> Int, group |-> {Int}]] ]))  ]]
  /\ front = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ deliver = [p \in Proc |-> (<< >> <: Seq(Int)) ]
  /\ mcastGreater = [m1 \in McastID |-> [m2 \in McastID |-> FALSE]]
                                      

HasAllProposes(self, mcastID, proposeMsg) ==
  \E mcast \in McastMsg : 
      /\ mcast.data.id = mcastID
      /\ \A g \in mcast.groupDest : \E m \in proposeMsg : m.source \in g
  
  
TakeMaxLocalTS(proposeMsg) == 
  CHOOSE lastPropose \in proposeMsg : \A msg \in proposeMsg : 
            \/ msg.data.lts.time < lastPropose.data.lts.time
            \/ /\ msg.data.lts.time = lastPropose.data.lts.time
               /\ ~groupLess[lastPropose.data.lts.group][msg.data.lts.group]

                               
Max(x, y) == IF x > y THEN x ELSE y


timestampLess(ts1, ts2) ==
  \/ ts1.time < ts2.time
  \/ /\ ts1.time = ts2.time
     /\ groupLess[ts1.group][ts2.group]
                                                          
  
HandleProposeMsg(self, msg) ==   
  /\ msg.data.type = Propose 
  /\ UNCHANGED <<inTransit, localTS, mcastedID >>
  /\ LET mcastID == msg.data.mcastID
         proposeMsg == { rMsg \in rcvdProposeMsg'[self] : rMsg.data.mcastID = mcastID }
     IN IF HasAllProposes(self, mcastID, proposeMsg)
        THEN LET lastPropose == TakeMaxLocalTS(proposeMsg)
                 lts == lastPropose.data.lts                 
             IN /\ phase' = [phase EXCEPT ![self][mcastID] = Committed]
                /\ globalTS' = [globalTS EXCEPT ![self][mcastID] = lts]
                /\ clock' = [clock EXCEPT ![self]  = Max(clock[self], lts.time)]
                /\ UNCHANGED << Delivered, deliver, mcastGreater >>            
        ELSE UNCHANGED <<phase, globalTS, clock, Delivered, deliver, mcastGreater >>
                              
                              
ReachUpperBounds ==
  /\ \A p \in Proc : \A msg \in McastMsg : isMcastRcver(p, msg) => msg.data.id \in rcvdMcastID[p] 
  /\ \A p, q \in Proc : front[p][q] = Len(inTransit[p][q])
  /\ UNCHANGED vars
  

HandleMcastMsg(self, mcast) ==
  /\ mcast.data.type = Multicast  
  /\ UNCHANGED << globalTS, deliver, Delivered, mcastGreater, front >>
  /\ LET id == mcast.data.id
         t == clock[self] + 1
         g0 == memberOfGroup[self]
         newStamp == Stamp(t, g0)
         data == [type |-> Propose, mcastID |-> id, g |-> g0, lts |-> newStamp]  
         rcvers == {p \in Proc : isMcastRcver(p, mcast)}       
     IN /\ clock' = [clock EXCEPT ![self] = t]        
        /\ localTS' = [localTS EXCEPT ![self][id] = newStamp]          
        /\ phase' = [phase EXCEPT ![self][id] = Proposed]
        /\ SendOneMsg(self, rcvers, data)  


Deliver(self, id) ==  
  /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]     
  /\ phase[self][id] = Committed
  /\ Delivered[self][id] = FALSE  
  /\ \A tid \in rcvdMcastID[self] : phase[self][tid] = Proposed => 
                                       timestampLess(globalTS[self][id], localTS[self][tid]) 
  /\ \A tid \in rcvdMcastID[self] : ( phase[self][tid] = Committed /\ ~Delivered[self][tid] ) => 
                                          ~timestampLess(globalTS[self][tid], globalTS[self][id])                                         
  /\ Delivered' = [Delivered EXCEPT ![self][id] = TRUE]  
  /\ deliver' = [deliver EXCEPT ![self] = Append(deliver[self], id)] 
  /\ mcastGreater' = [mcastGreater EXCEPT ![id] = [tid \in McastID |->
                        IF Delivered[self][tid]  
                        THEN TRUE
                        ELSE mcastGreater[id][tid]]]                                              
  /\ UNCHANGED << localTS, globalTS, rcvdMcastID, rcvdProposeMsg, mcastedID, phase, inTransit, front >>
     
   
Next ==
  \/ \E rcver \in Proc : \E msg \in McastMsg :
      /\ msg.data.id \notin (rcvdMcastID[rcver] <: {Int})
      /\ ReceiveMcast(rcver, msg)       
      /\ HandleMcastMsg(rcver, msg)           
      /\ IF msg.data.id \notin mcastedID THEN mcastedID' = mcastedID \cup {msg.data.id}
         ELSE UNCHANGED mcastedID         
  \/ \E snder, rcver \in Proc :          
        /\ front[snder][rcver] < Len(inTransit[snder][rcver]) 
        /\ LET slot == front[snder][rcver] + 1
               msg == inTransit[snder][rcver][slot]
           IN /\ ReceivePropose(rcver, snder, msg)
              /\ HandleProposeMsg(rcver, msg)                   
  \/ \E p \in Proc : \E id \in rcvdMcastID[p] : Deliver(p, id)      
  \/ ReachUpperBounds
  

\* The specification              
Spec == 
  /\ Init /\ [][Next]_vars 
  /\ WF_vars(\/ \E rcver \in Proc : \E msg \in McastMsg  :
                    /\ msg.data.id \notin rcvdMcastID[rcver]               
                    /\ ReceiveMcast(rcver, msg) 
                    /\ HandleMcastMsg(rcver, msg)      
                    /\ IF msg.data.id \notin mcastedID THEN mcastedID' = mcastedID \cup {msg.data.id}
                       ELSE UNCHANGED mcastedID                       
             \/ \E snder, rcver \in Proc :          
                    /\ front[snder][rcver] < Len(inTransit[snder][rcver]) 
                    /\ LET slot == front[snder][rcver] + 1
                           msg == inTransit[snder][rcver][slot]
                       IN /\ ReceivePropose(rcver, snder, msg)
                          /\ HandleProposeMsg(rcver, msg) 
             \/ \E p \in Proc : \E msg \in rcvdMcastID[p] : Deliver(p, msg) )      



=============================================================================
\* Modification History
\* Last modified Thu Mar 11 12:50:53 CET 2021 by tran
\* Created Thu Mar 11 12:49:45 CET 2021 by tran
