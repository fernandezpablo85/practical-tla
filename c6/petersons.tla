---- MODULE petersons ----
(****************************************************************************************)
(* Peterson's Algorithm for mutual exclusion, as specified in Wikipedia's pseudocode[1] *)
(*                                                                                      *)
(* [1] https://en.wikipedia.org/wiki/Peterson%27s_algorithm#The_algorithm               *)
(****************************************************************************************)
EXTENDS TLC, Integers

VARIABLES
    flag,
    turn,
    pc

vars == << flag, turn, pc >>

Threads == {0, 1}

Init ==
    /\ flag \in [Threads -> {FALSE}]
    /\ turn \in Threads
    /\ pc \in [Threads -> {"init"}]

SetFlag(self) ==
    /\ pc[self] = "init"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "flag_set"]
    /\ UNCHANGED turn

SetTurn(self) ==
    /\ pc[self] = "flag_set"
    /\ turn' = 1 - self
    /\ pc' = [pc EXCEPT ![self] = "busy_wait"]
    /\ UNCHANGED flag

BusyWait(self) ==
    /\ pc[self] = "busy_wait"
    /\ \/ ~flag[1 - self]
       \/ turn = self
    /\ pc' = [pc EXCEPT ![self] = "enter_critical"]
    /\ UNCHANGED << flag, turn >>

Critical(self) ==
    /\ pc[self] = "enter_critical"
    /\ TRUE \* perform critical stuff
    /\ pc' = [pc EXCEPT ![self] = "exit_critical"]
    /\ UNCHANGED << flag, turn >>

ExitCritical(self) ==
    /\ pc[self] = "exit_critical"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "init"]
    /\ UNCHANGED turn

ThreadSteps(t) ==
    \/ SetFlag(t)
    \/ SetTurn(t)
    \/ BusyWait(t)
    \/ Critical(t)
    \/ ExitCritical(t)

Next == \E t \in Threads: ThreadSteps(t)

Spec == Init /\ [][Next]_vars /\ \A t \in Threads: WF_vars(ThreadSteps(t))

----

Safety ==
    \/ \A t \in Threads: pc[t] /= "enter_critical"
    \/ \E t \in Threads:
        /\ pc[t] = "enter_critical"
        /\ \A u \in Threads \ {t}: pc[u] /= "enter_critical"

Liveness == \A t \in Threads: <>(pc[t] = "enter_critical")
====