---- MODULE PGrammar ----

(* 
 * This module demonstrates the use of various data types in TLA+.
 * It includes strings, booleans, integers, sets, sequences, records, and functions
 * Standard Library: https://www.learntla.com/reference/standard-library.html
 *)
EXTENDS Integers, TLC, Naturals, Sequences, FiniteSets

\* Define a function to print values
set ++ elem == set \union {elem}

(* --algorithm PGrammar
variable strvar = "Hello World",
        boolvar = TRUE,
        intvar \in 42..43,
        setvar = 1..10,
        sequencevar = <<1, 2, 3>>,
        structvar = [x |-> 1, y |-> 2],
        funcationvar = [x \in 1..3 |-> x * 2];

macro inc(var) begin
  if var < 10 then
    var := var + 1;
  end if;
end macro;

begin
    print strvar;
    print boolvar;
    print intvar;
    print setvar;
    print sequencevar;
    print structvar;
    print funcationvar;

    print "Perform some operations on boolean";
    print ~boolvar;
    if boolvar then
        print "Boolean is true";
    else
        print "Boolean is false";
    end if;
    assert boolvar;

    print "Perform some operations on integer";
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
    elsif intvar < 0 then
        print "intvar is negative";
    else
        print "intvar is zero";
    end if;

    if intvar = 0 \/ intvar # 0 \/ intvar /= 0 then
        print "intvar is zero";
    else
        print "intvar is not zero";
    end if;

    print "Perform some operations on set";
    print Seq(setvar);
    print Cardinality(setvar);
    if 5 \in setvar \/ 5 \notin setvar then
        print "5 is in setvar or 5 is not in setvar";
    end if;

    if 2..3 \subseteq setvar then
        print "2..3 is a subset of setvar";
    end if;

    print setvar ++ 2;
    print 1..2 \cup setvar;
    print 1..2 \union setvar;
    print 1..2 \cap setvar;
    print 1..2 \intersect setvar;
    setvar := 1..2;
    print setvar \X setvar;
    print SUBSET setvar;
    \* print 1..2 \setminus setvar;

    print "Perform some operations on sequence";
    \* sequencevar := Seq(setvar);
    sequencevar := Append(sequencevar, 16);
    print Len(sequencevar);
    print Head(sequencevar);
    print Tail(sequencevar);
    print sequencevar \o << 4, 5, 6 >>;
    print SubSeq(sequencevar, 1, 2);

    while sequencevar /= <<>> do
        print Head(sequencevar);
        sequencevar := Tail(sequencevar);
    end while;
    \* print SelectSeq(<<1, 2, 3>>, IsEven);

    print "Perform some operations on record";
    either
        print "Done";
    or
        print "Not done";
    end either;

    with v \in 1..2 do
        print v;
    end with;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b74f0f9a" /\ chksum(tla) = "20b4e422")
VARIABLES pc, strvar, boolvar, intvar, setvar, sequencevar, structvar, 
          funcationvar

vars == << pc, strvar, boolvar, intvar, setvar, sequencevar, structvar, 
           funcationvar >>

Init == (* Global variables *)
        /\ strvar = "Hello World"
        /\ boolvar = TRUE
        /\ intvar \in 42..43
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
         /\ PrintT("Perform some operations on boolean")
         /\ PrintT(~boolvar)
         /\ IF boolvar
               THEN /\ PrintT("Boolean is true")
               ELSE /\ PrintT("Boolean is false")
         /\ Assert(boolvar, "Failure of assertion at line 44, column 5.")
         /\ PrintT("Perform some operations on integer")
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
         /\ IF intvar' = 0 \/ intvar' # 0 \/ intvar' /= 0
               THEN /\ PrintT("intvar is zero")
               ELSE /\ PrintT("intvar is not zero")
         /\ PrintT("Perform some operations on set")
         /\ PrintT(Seq(setvar))
         /\ PrintT(Cardinality(setvar))
         /\ IF 5 \in setvar \/ 5 \notin setvar
               THEN /\ PrintT("5 is in setvar or 5 is not in setvar")
               ELSE /\ TRUE
         /\ IF 2..3 \subseteq setvar
               THEN /\ PrintT("2..3 is a subset of setvar")
               ELSE /\ TRUE
         /\ PrintT(setvar ++ 2)
         /\ PrintT(1..2 \cup setvar)
         /\ PrintT(1..2 \union setvar)
         /\ PrintT(1..2 \cap setvar)
         /\ PrintT(1..2 \intersect setvar)
         /\ setvar' = 1..2
         /\ PrintT(setvar' \X setvar')
         /\ PrintT(SUBSET setvar')
         /\ PrintT("Perform some operations on sequence")
         /\ sequencevar' = Append(sequencevar, 16)
         /\ PrintT(Len(sequencevar'))
         /\ PrintT(Head(sequencevar'))
         /\ PrintT(Tail(sequencevar'))
         /\ PrintT(sequencevar' \o << 4, 5, 6 >>)
         /\ PrintT(SubSeq(sequencevar', 1, 2))
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << strvar, boolvar, structvar, funcationvar >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ IF sequencevar /= <<>>
               THEN /\ PrintT(Head(sequencevar))
                    /\ sequencevar' = Tail(sequencevar)
                    /\ pc' = "Lbl_6"
               ELSE /\ PrintT("Perform some operations on record")
                    /\ \/ /\ PrintT("Done")
                       \/ /\ PrintT("Not done")
                    /\ \E v \in 1..2:
                         PrintT(v)
                    /\ pc' = "Done"
                    /\ UNCHANGED sequencevar
         /\ UNCHANGED << strvar, boolvar, intvar, setvar, structvar, 
                         funcationvar >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
