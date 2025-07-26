---- MODULE PGrammar ----

(* 
 * This module demonstrates the use of various data types in TLA+.
 * It includes strings, booleans, integers, sets, sequences, records, and functions
 * Standard Library: https://www.learntla.com/reference/standard-library.html
 *)
EXTENDS Integers, TLC, Naturals, Sequences, FiniteSets

(* --algorithm PGrammar
variable strvar = "Hello World",
        boolvar = TRUE,
        intvar = 42;
        setvar = 1..10;
        sequencevar = <<1, 2, 3>>;
        structvar = [x |-> 1, y |-> 2];
        funcationvar = [x \in 1..3 |-> x * 2];
begin
    print strvar;
    print boolvar;
    print intvar;
    print setvar;
    print sequencevar;
    print structvar;
    print funcationvar;

    if boolvar then
        print "Boolean is true";
    else
        print "Boolean is false";
    end if;

    (* Perform some operations on integer *)

    intvar := intvar + 1;
    print intvar;
    intvar := intvar * 2;
    print intvar;
    intvar := intvar - 2;
    print intvar;
    intvar := intvar \div 2;
    print intvar;
    intvar := -intvar;
    print intvar;

    if intvar > 0 then
        print "intvar is positive";
    else 
        if intvar < 0 then
            print "intvar is negative";
        else
            print "intvar is zero";
        end if;
    end if;

    (* Perform some operations on set *)
    print Seq(setvar);
    print Cardinality(setvar);

    (* Perform some operations on sequence *)
    \* sequencevar := Seq(setvar);
    sequencevar := Append(sequencevar, 16);
    print Len(sequencevar);
    print Head(sequencevar);
    print Tail(sequencevar);
    print sequencevar \o << 4, 5, 6 >>;
    print SubSeq(sequencevar, 1, 2);
    \* print SelectSeq(<<1, 2, 3>>, IsEven);
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2d08e5c0" /\ chksum(tla) = "be0e689")
VARIABLES pc, strvar, boolvar, intvar, setvar, sequencevar, structvar, 
          funcationvar

vars == << pc, strvar, boolvar, intvar, setvar, sequencevar, structvar, 
           funcationvar >>

Init == (* Global variables *)
        /\ strvar = "Hello World"
        /\ boolvar = TRUE
        /\ intvar = 42
        /\ setvar = 1..10
        /\ sequencevar = <<1, 2, 3>>
        /\ structvar = [x |-> 1, y |-> 2]
        /\ funcationvar = [x \in 1..3 |-> x * 2]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(strvar)
         /\ PrintT(boolvar)
         /\ PrintT(intvar)
         /\ PrintT(setvar)
         /\ PrintT(sequencevar)
         /\ PrintT(structvar)
         /\ PrintT(funcationvar)
         /\ IF boolvar
               THEN /\ PrintT("Boolean is true")
               ELSE /\ PrintT("Boolean is false")
         /\ intvar' = intvar + 1
         /\ PrintT(intvar')
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << strvar, boolvar, setvar, sequencevar, structvar, 
                         funcationvar >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ intvar' = intvar * 2
         /\ PrintT(intvar')
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << strvar, boolvar, setvar, sequencevar, structvar, 
                         funcationvar >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ intvar' = intvar - 2
         /\ PrintT(intvar')
         /\ pc' = "Lbl_4"
         /\ UNCHANGED << strvar, boolvar, setvar, sequencevar, structvar, 
                         funcationvar >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ intvar' = (intvar \div 2)
         /\ PrintT(intvar')
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << strvar, boolvar, setvar, sequencevar, structvar, 
                         funcationvar >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ intvar' = -intvar
         /\ PrintT(intvar')
         /\ IF intvar' > 0
               THEN /\ PrintT("intvar is positive")
               ELSE /\ IF intvar' < 0
                          THEN /\ PrintT("intvar is negative")
                          ELSE /\ PrintT("intvar is zero")
         /\ PrintT(Seq(setvar))
         /\ PrintT(Cardinality(setvar))
         /\ sequencevar' = Append(sequencevar, 16)
         /\ PrintT(Len(sequencevar'))
         /\ PrintT(Head(sequencevar'))
         /\ PrintT(Tail(sequencevar'))
         /\ PrintT(sequencevar' \o << 4, 5, 6 >>)
         /\ PrintT(SubSeq(sequencevar', 1, 2))
         /\ pc' = "Done"
         /\ UNCHANGED << strvar, boolvar, setvar, structvar, funcationvar >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
