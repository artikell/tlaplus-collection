---- MODULE Traffic -----
NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"
(*--algorithm Traffic
variables
    at_light = TRUE;
    light = "red";
process light = "light"
begin
    Cycle:
        while at_light do
            light := NextColor(light);
        end while;
end process;
process car = "car"
begin
    Drive:
        when light = "green";
        at_light := FALSE;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "7fd345" /\ chksum(tla) = "84749621")
\* Process light at line 8 col 1 changed to light_
VARIABLES pc, at_light, light

vars == << pc, at_light, light >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Drive"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF at_light
               THEN /\ light' = NextColor(light)
                    /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

light_ == Cycle

Drive == /\ pc["car"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ light' = light

car == Drive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == light_ \/ car
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
