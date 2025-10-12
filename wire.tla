---- MODULE wire ----
EXTENDS Integers

 (*--algorithm wire
 variables
     people = {"alice", "bob"},
     acc = [p \in people |-> 5],
     sender = "alice",
     receiver = "bob",
     amount = 3;

define
     NoOverdrafts == \A p \in people: acc[p] >= 0
 end define;

begin
     skip;
 end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "837e18bd" /\ chksum(tla) = "e2535a9")
VARIABLES pc, people, acc, sender, receiver, amount

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0


vars == << pc, people, acc, sender, receiver, amount >>

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ sender = "alice"
        /\ receiver = "bob"
        /\ amount = 3
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << people, acc, sender, receiver, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=================================
