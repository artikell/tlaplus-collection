---- MODULE TwoPhase ----

EXTENDS Integers

(* --algorithm TwoPhase {
    variables
        people={"alice", "bob", "charlie"},
        acc=[p \in people |-> 6];
    {
        skip;
    }
} *)
\* --------------------------------
\* BEGIN TRANSLATION (chksum(pcal) = "6e4a9ef3" /\ chksum(tla) = "4325ea7a")
VARIABLES pc, people, acc

vars == << pc, people, acc >>

Init == (* Global variables *)
        /\ people = {"alice", "bob", "charlie"}
        /\ acc = [p \in people |-> 6]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << people, acc >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
