---- MODULE BinarySearch ----
EXTENDS Integers,TLC,Sequences
PT == INSTANCE PT
OrderedSeqOf(set,n) == 
    { seq \in PT!SeqOf(set,n):
      \A x \in 2..Len(seq):
       seq[x]>=seq[x-1]}
Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2*f[x-1]
    IN f[n]
MaxInt == 4
Range(f) == {f[x]: x \in DOMAIN f}
(*--algorithm BinarySearch
variables low=1,
          seq \in OrderedSeqOf(1..MaxInt,MaxInt),
          target \in 1..MaxInt,
          high = Len(seq),
          found_index = 0,
          counter = 0;
begin
    Search:
        while low <= high do
            counter := counter + 1;
            with
                mid=(high+low) \div 2
            do
                if seq[mid] = target then
                    found_index := mid;
                    goto Result;
                elsif seq[mid] > target then
                    high := mid-1;
                else
                    low := mid+1;
                end if;
            end with;
        end while;
    Result:
        if Len(seq) > 0 then
            assert Pow2(counter-1) <= Len(seq);
        end if;
        if target \in PT!Range(seq) then
            assert seq[found_index] =target;
        else
            assert found_index = 0;
        end if;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "3009fb34" /\ chksum(tla) = "9481983")
VARIABLES pc, low, seq, target, high, found_index, counter

vars == << pc, low, seq, target, high, found_index, counter >>

Init == (* Global variables *)
        /\ low = 1
        /\ seq \in OrderedSeqOf(1..MaxInt,MaxInt)
        /\ target \in 1..MaxInt
        /\ high = Len(seq)
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ LET mid == (high+low) \div 2 IN
                          IF seq[mid] = target
                             THEN /\ found_index' = mid
                                  /\ pc' = "Result"
                                  /\ UNCHANGED << low, high >>
                             ELSE /\ IF seq[mid] > target
                                        THEN /\ high' = mid-1
                                             /\ low' = low
                                        ELSE /\ low' = mid+1
                                             /\ high' = high
                                  /\ pc' = "Search"
                                  /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << low, high, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter-1) <= Len(seq), 
                               "Failure of assertion at line 42, column 13.")
                ELSE /\ TRUE
          /\ IF target \in PT!Range(seq)
                THEN /\ Assert(seq[found_index] =target, 
                               "Failure of assertion at line 45, column 13.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 47, column 13.")
          /\ pc' = "Done"
          /\ UNCHANGED << low, seq, target, high, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
