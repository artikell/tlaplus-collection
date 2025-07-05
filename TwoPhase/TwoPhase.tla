---- MODULE TwoPhase ----

EXTENDS Integers

(*--algorithm wire
    variables
        people={"alice","bob"},
        acc=[p \in people |-> 6];
begin
    skip;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "67c19764" /\ chksum(tla) = "bb299360")
VARIABLES pc, people, acc

vars == << pc, people, acc >>

Init == (* Global variables *)
        /\ people = {"alice","bob"}
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
