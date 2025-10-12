---- MODULE wire ----
EXTENDS Integers

 (*--algorithm wire
 variables
     people = {"alice", "bob"},
     acc = [p \in people |-> 5],
     inflight = 0;

define
     NoOverdrafts == \A p \in people: acc[p] >= 0
     NonNegativeInflight == inflight >= 0
     Conservation == acc["alice"] + acc["bob"] + inflight = 10
    \*  EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)
    \* （システム障害などで）stuttringが存在する世界では、EventuallyConsistentは満たせない
end define;

process Wire \in 1..2
     variables
         sender = "alice",
         receiver = "bob",
         amount \in 1..acc[sender];

begin
    CheckAndReserve:
         if amount <= acc[sender] then
                 acc[sender] := acc[sender] - amount;
                 inflight := inflight + amount;
             Deposit:
                 acc[receiver] := acc[receiver] + amount;
                 inflight := inflight - amount;
         end if;

end process;    

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "83f6193c" /\ chksum(tla) = "338fce51")
VARIABLES pc, people, acc, inflight

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0
NonNegativeInflight == inflight >= 0
Conservation == acc["alice"] + acc["bob"] + inflight = 10
EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)

VARIABLES sender, receiver, amount

vars == << pc, people, acc, inflight, sender, receiver, amount >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ inflight = 0
        (* Process Wire *)
        /\ sender = [self \in 1..2 |-> "alice"]
        /\ receiver = [self \in 1..2 |-> "bob"]
        /\ amount \in [1..2 -> 1..acc[sender[CHOOSE self \in  1..2 : TRUE]]]
        /\ pc = [self \in ProcSet |-> "CheckAndReserve"]

CheckAndReserve(self) == /\ pc[self] = "CheckAndReserve"
                         /\ IF amount[self] <= acc[sender[self]]
                               THEN /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] - amount[self]]
                                    /\ inflight' = inflight + amount[self]
                                    /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << acc, inflight >>
                         /\ UNCHANGED << people, sender, receiver, amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acc' = [acc EXCEPT ![receiver[self]] = acc[receiver[self]] + amount[self]]
                 /\ inflight' = inflight - amount[self]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << people, sender, receiver, amount >>

Wire(self) == CheckAndReserve(self) \/ Deposit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=================================
