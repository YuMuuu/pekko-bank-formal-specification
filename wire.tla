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
     \* Reserve 後は Deposit か Refund のいずれかで処理を終えるため、全プロセス終了時に inflight は必ず 0。
     NoInflightAtAllDone == (\A self \in DOMAIN pc: pc[self] = "Done") => inflight = 0
    \*  EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)
    \* （システム障害などで）stuttering が存在する世界では、EventuallyConsistent は満たせない
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
             either
                 \* 受取側システムが健全であれば通常通り入金（Deposit）
                 Deposit:
                     acc[receiver] := acc[receiver] + amount;
                     inflight := inflight - amount;
             or
                 \* 受取側システムが復旧不可能な場合はロックをキャンセルし送金元へ返金（Refund）
                 Refund:
                     acc[sender] := acc[sender] + amount;
                     inflight := inflight - amount;
             end either;
         end if;

end process;    

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "0")
VARIABLES pc, people, acc, inflight

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0
NonNegativeInflight == inflight >= 0
Conservation == acc["alice"] + acc["bob"] + inflight = 10

NoInflightAtAllDone == (\A self \in DOMAIN pc: pc[self] = "Done") => inflight = 0

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
                                    /\ \/ /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                                       \/ /\ pc' = [pc EXCEPT ![self] = "Refund"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << acc, inflight >>
                         /\ UNCHANGED << people, sender, receiver, amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acc' = [acc EXCEPT ![receiver[self]] = acc[receiver[self]] + amount[self]]
                 /\ inflight' = inflight - amount[self]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << people, sender, receiver, amount >>

Refund(self) == /\ pc[self] = "Refund"
                /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] + amount[self]]
                /\ inflight' = inflight - amount[self]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << people, sender, receiver, amount >>

Wire(self) == CheckAndReserve(self) \/ Deposit(self) \/ Refund(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=================================
