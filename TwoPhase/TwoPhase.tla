---- MODULE TwoPhase ----

EXTENDS Naturals, Sequences, TLC

(* 定义常量并使用 ASSUME 确保常量类型符合预期 *)
Coordinators == {"C1"}
ASSUME Coordinators \subseteq STRING

Participants == {"P1", "P2"}
ASSUME Participants \subseteq STRING

Timeout == 10
ASSUME Timeout \in Nat

VARIABLES
    coordinatorState,  \* 协调者状态
    participantStates, \* 参与者状态
    votes,             \* 参与者投票结果
    timestamp          \* 时间戳

\* 定义状态类型
StateType == {"INIT", "VOTE_REQUEST", "COMMIT", "ABORT", "DONE"}

\* 初始化状态
Init ==
    /\ coordinatorState = "INIT"
    /\ participantStates = [p \in Participants |-> "INIT"]
    /\ votes = [p \in Participants |-> FALSE]
    /\ timestamp = 0

\* 协调者发送投票请求
CoordinatorSendVoteRequest ==
    /\ coordinatorState = "INIT"
    /\ coordinatorState' = "VOTE_REQUEST"
    /\ participantStates' = [p \in Participants |-> "VOTE_REQUEST"]
    /\ votes' = votes  \* 添加对 votes 变量下一个状态的定义，保持其值不变
    /\ timestamp' = timestamp + 1

\* 参与者投票
ParticipantVote ==
    \E p \in Participants:
        /\ participantStates[p] = "VOTE_REQUEST"
        /\ LET voteOK == RandomElement({TRUE, FALSE}) IN
            /\ votes' = [votes EXCEPT ![p] = voteOK]
            /\ participantStates' = [participantStates EXCEPT ![p] = IF voteOK THEN "VOTED_YES" ELSE "VOTED_NO"]
            /\ timestamp' = timestamp + 1

\* 协调者收集投票并决策
CoordinatorCollectVoteAndDecide ==
    /\ coordinatorState = "VOTE_REQUEST"
    /\ \A p \in Participants: participantStates[p] \in {"VOTED_YES", "VOTED_NO"}
    /\ LET allYes == \A p \in Participants: votes[p] IN
        /\ coordinatorState' = IF allYes THEN "COMMIT" ELSE "ABORT"
        /\ participantStates' = [p \in Participants |-> IF allYes THEN "COMMIT" ELSE "ABORT"]
        /\ timestamp' = timestamp + 1

\* 参与者执行提交或中止
ParticipantExecute ==
    \E p \in Participants:
        /\ participantStates[p] \in {"COMMIT", "ABORT"}
        /\ participantStates' = [participantStates EXCEPT ![p] = "DONE"]
        /\ timestamp' = timestamp + 1

\* 超时处理
TimeoutHandler ==
    /\ timestamp >= Timeout
    /\ coordinatorState' = "ABORT"
    /\ participantStates' = [p \in Participants |-> "ABORT"]
    /\ timestamp' = timestamp + 1

\* 下一状态转移
Next ==
    \/ CoordinatorSendVoteRequest
    \/ ParticipantVote
    \/ CoordinatorCollectVoteAndDecide
    \/ ParticipantExecute
    \/ TimeoutHandler

\* 系统规范
Spec == Init /\ [][Next]_<<coordinatorState, participantStates, votes, timestamp>>

\* 类型不变式
TypeOK ==
    /\ coordinatorState \in StateType
    /\ participantStates \in [Participants -> StateType]
    /\ votes \in [Participants -> BOOLEAN]
    /\ timestamp \in Nat

\* 一致性属性：所有参与者最终状态一致
ConsistencyProperty ==
    [] (\A p1, p2 \in Participants: participantStates[p1] = "DONE" /\ participantStates[p2] = "DONE" =>
        (coordinatorState = "COMMIT" <=> participantStates[p1] = "DONE") /\
        (coordinatorState = "ABORT" <=> participantStates[p1] = "DONE"))

====