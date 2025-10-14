---- MODULE wire ----
EXTENDS Integers

CONSTANT TIMEOUT 

(*--algorithm wire
variables
    people = {"alice", "bob"},
    acc = [p \in people |-> 5],
    inflight = 0,
    age = [i \in 1..2 |-> 0], \* Reserved になってからの経過ステップ
    sender = [i \in 1..2 |-> "alice"],
    receiver = [i \in 1..2 |-> "bob"],
    reserved = [i \in 1..2 |-> 0],
    state = [i \in 1..2 |-> "Init"]; 

define
    NoOverdrafts == \A p \in people: acc[p] >= 0
    NonNegativeInflight == inflight >= 0
    Conservation == acc["alice"] + acc["bob"] + inflight = 10
    NoInflightAtAllDone == (\A self \in 1..2: pc[self] = "Done") => inflight = 0
    ReservedInflightConsistency == inflight = reserved[1] + reserved[2]
    GuardConsistency == \A self \in 1..2:
        /\ state[self] \in {"Init","Reserved","Deposited","Refunded"}
        /\ (state[self] \in {"Deposited","Refunded"} => reserved[self] = 0)
end define;

process Wire \in 1..2
    variables
        amount \in 1..acc["alice"];
begin
    CheckAndReserve:
        if amount <= acc[sender[self]] then
            acc[sender[self]] := acc[sender[self]] - amount;
            inflight := inflight + amount;
            reserved[self] := amount;
            state[self] := "Reserved";
        end if;

    Choice:
        either
            if state[self] = "Reserved" then
            Deposit:
                acc[receiver[self]] := acc[receiver[self]] + reserved[self];
                inflight := inflight - reserved[self];
                reserved[self] := 0;
                state[self] := "Deposited";
            end if;
        or
            if state[self] = "Reserved" then
            RefundSelf:
                acc[sender[self]] := acc[sender[self]] + reserved[self];
                inflight := inflight - reserved[self];
                reserved[self] := 0;
                state[self] := "Refunded";
            end if;
        end either;
end process;

\* スタッタリング検知と Refund を行うガーディアン
fair process Guardian = 0
variables dummy = 0;
begin
    Loop:
        while TRUE do
            with i \in 1..2 do
                \* willRefund をブール式として評価
                if state[i] = "Reserved" /\ age[i] + 1 >= TIMEOUT then
                    acc[sender[i]] := acc[sender[i]] + reserved[i];
                    inflight := inflight - reserved[i];
                    reserved[i] := 0;
                    state[i] := "Refunded";
                end if;
                \* age はブランチに依らず 1 度だけ更新
                age[i] := IF state[i] = "Reserved"
                          THEN IF age[i] + 1 >= TIMEOUT THEN 0 ELSE age[i] + 1
                          ELSE 0;
            end with;
        end while;
end process;

end algorithm;*)

\* BEGIN TRANSLATION (auto-generated; run `make pcal` to refresh)
VARIABLES pc, people, acc, inflight, age, sender, receiver, reserved, state

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0
NonNegativeInflight == inflight >= 0
Conservation == acc["alice"] + acc["bob"] + inflight = 10

NoInflightAtAllDone == (\A self \in 1..2: pc[self] = "Done") => inflight = 0

ReservedInflightConsistency == inflight = reserved[1] + reserved[2]

GuardConsistency == \A self \in 1..2:
    /\ state[self] \in {"Init","Reserved","Deposited","Refunded"}
    /\ (state[self] \in {"Deposited","Refunded"} => reserved[self] = 0)

VARIABLES amount, dummy

vars == << pc, people, acc, inflight, age, sender, receiver, reserved, state, 
           amount, dummy >>

ProcSet == (1..2) \cup {0}

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ inflight = 0
        /\ age = [i \in 1..2 |-> 0]
        /\ sender = [i \in 1..2 |-> "alice"]
        /\ receiver = [i \in 1..2 |-> "bob"]
        /\ reserved = [i \in 1..2 |-> 0]
        /\ state = [i \in 1..2 |-> "Init"]
        (* Process Wire *)
        /\ amount \in [1..2 -> 1..acc["alice"]]
        (* Process Guardian *)
        /\ dummy = 0
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> "CheckAndReserve"
                                        [] self = 0 -> "Loop"]

CheckAndReserve(self) == /\ pc[self] = "CheckAndReserve"
                         /\ IF amount[self] <= acc[sender[self]]
                               THEN /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] - amount[self]]
                                    /\ inflight' = inflight + amount[self]
                                    /\ reserved' = [reserved EXCEPT ![self] = amount[self]]
                                    /\ state' = [state EXCEPT ![self] = "Reserved"]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << acc, inflight, reserved, 
                                                    state >>
                         /\ pc' = [pc EXCEPT ![self] = "Choice"]
                         /\ UNCHANGED << people, age, sender, receiver, amount, 
                                         dummy >>

Choice(self) == /\ pc[self] = "Choice"
                /\ \/ /\ IF state[self] = "Reserved"
                            THEN /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   \/ /\ IF state[self] = "Reserved"
                            THEN /\ pc' = [pc EXCEPT ![self] = "RefundSelf"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << people, acc, inflight, age, sender, receiver, 
                                reserved, state, amount, dummy >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acc' = [acc EXCEPT ![receiver[self]] = acc[receiver[self]] + reserved[self]]
                 /\ inflight' = inflight - reserved[self]
                 /\ reserved' = [reserved EXCEPT ![self] = 0]
                 /\ state' = [state EXCEPT ![self] = "Deposited"]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << people, age, sender, receiver, amount, dummy >>

RefundSelf(self) == /\ pc[self] = "RefundSelf"
                    /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] + reserved[self]]
                    /\ inflight' = inflight - reserved[self]
                    /\ reserved' = [reserved EXCEPT ![self] = 0]
                    /\ state' = [state EXCEPT ![self] = "Refunded"]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << people, age, sender, receiver, amount, 
                                    dummy >>

Wire(self) == CheckAndReserve(self) \/ Choice(self) \/ Deposit(self)
                 \/ RefundSelf(self)

Loop == /\ pc[0] = "Loop"
        /\ \E i \in 1..2:
             /\ IF state[i] = "Reserved" /\ age[i] + 1 >= TIMEOUT
                   THEN /\ acc' = [acc EXCEPT ![sender[i]] = acc[sender[i]] + reserved[i]]
                        /\ inflight' = inflight - reserved[i]
                        /\ reserved' = [reserved EXCEPT ![i] = 0]
                        /\ state' = [state EXCEPT ![i] = "Refunded"]
                   ELSE /\ TRUE
                        /\ UNCHANGED << acc, inflight, reserved, state >>
             /\ age' = [age EXCEPT ![i] = IF state'[i] = "Reserved"
                                          THEN IF age[i] + 1 >= TIMEOUT THEN 0 ELSE age[i] + 1
                                          ELSE 0]
        /\ pc' = [pc EXCEPT ![0] = "Loop"]
        /\ UNCHANGED << people, sender, receiver, amount, dummy >>

Guardian == Loop

Next == Guardian
           \/ (\E self \in 1..2: Wire(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Guardian)

\* END TRANSLATION

=================================
