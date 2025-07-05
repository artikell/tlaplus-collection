---- MODULE TwoPhase_TTrace_1751702641 ----
EXTENDS Sequences, TLCExt, TwoPhase, Toolbox, Naturals, TLC

_expression ==
    LET TwoPhase_TEExpression == INSTANCE TwoPhase_TEExpression
    IN TwoPhase_TEExpression!expression
----

_trace ==
    LET TwoPhase_TETrace == INSTANCE TwoPhase_TETrace
    IN TwoPhase_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        participantStates = ([P1 |-> "VOTE_REQUEST", P2 |-> "VOTE_REQUEST"])
        /\
        votes = ()
        /\
        coordinatorState = ("VOTE_REQUEST")
        /\
        timestamp = (1)
    )
----

_init ==
    /\ participantStates = _TETrace[1].participantStates
    /\ coordinatorState = _TETrace[1].coordinatorState
    /\ timestamp = _TETrace[1].timestamp
    /\ votes = _TETrace[1].votes
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ participantStates  = _TETrace[i].participantStates
        /\ participantStates' = _TETrace[j].participantStates
        /\ coordinatorState  = _TETrace[i].coordinatorState
        /\ coordinatorState' = _TETrace[j].coordinatorState
        /\ timestamp  = _TETrace[i].timestamp
        /\ timestamp' = _TETrace[j].timestamp
        /\ votes  = _TETrace[i].votes
        /\ votes' = _TETrace[j].votes

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("TwoPhase_TTrace_1751702641.json", _TETrace)

=============================================================================

 Note that you can extract this module `TwoPhase_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `TwoPhase_TEExpression.tla` file takes precedence 
  over the module `TwoPhase_TEExpression` below).

---- MODULE TwoPhase_TEExpression ----
EXTENDS Sequences, TLCExt, TwoPhase, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `TwoPhase` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        participantStates |-> participantStates
        ,coordinatorState |-> coordinatorState
        ,timestamp |-> timestamp
        ,votes |-> votes
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_participantStatesUnchanged |-> participantStates = participantStates'
        
        \* Format the `participantStates` variable as Json value.
        \* ,_participantStatesJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(participantStates)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_participantStatesModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].participantStates # _TETrace[s-1].participantStates
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE TwoPhase_TETrace ----
\*EXTENDS IOUtils, TwoPhase, TLC
\*
\*trace == IODeserialize("TwoPhase_TTrace_1751702641.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TwoPhase_TETrace ----
EXTENDS TwoPhase, TLC

trace == 
    <<
    ([participantStates |-> [P1 |-> "INIT", P2 |-> "INIT"],votes |-> [P1 |-> FALSE, P2 |-> FALSE],coordinatorState |-> "INIT",timestamp |-> 0]),
    ([participantStates |-> [P1 |-> "VOTE_REQUEST", P2 |-> "VOTE_REQUEST"],votes |-> ,coordinatorState |-> "VOTE_REQUEST",timestamp |-> 1])
    >>
----


=============================================================================

---- CONFIG TwoPhase_TTrace_1751702641 ----

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Sat Jul 05 16:04:02 CST 2025