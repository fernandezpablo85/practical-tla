---- MODULE dekkers ----
EXTENDS TLC
CONSTANT Threads

VARIABLES
    flag,
    pc,
    next

vars == <<flag, pc, next>>

Init ==
    /\ pc \in [Threads -> {"init"}]
    /\ flag \in [Threads -> {FALSE}]
    /\ next \in Threads


SomeWaiting(self) ==  \E t \in Threads \ {self}: flag[t]


SetFlag(self) ==
    /\ pc[self] = "init"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "wait_for_rest"]
    /\ UNCHANGED next


WaitForRest(self) ==
    /\ pc[self] = "wait_for_rest"
    /\ IF SomeWaiting(self)
        THEN IF self /= next
            THEN /\ pc' = [pc EXCEPT ![self] = "active_wait"]
                 /\ UNCHANGED <<next, flag>>
            ELSE /\ pc' = [pc EXCEPT ![self] = "critical"]
                 /\ next' = self
                 /\ UNCHANGED <<flag>>
        ELSE /\ pc' = [pc EXCEPT ![self] = "critical"]
             /\ next' = self
             /\ UNCHANGED <<flag>>


ActiveWait(self) ==
    /\ pc[self] = "active_wait"
    /\ next = self
    /\ pc' = [pc EXCEPT ![self] = "critical"]
    /\ UNCHANGED <<next, flag>>


Critical(self) ==
    /\ pc[self] = "critical"
    /\ TRUE \* do critical work here
    /\ pc' = [pc EXCEPT ![self] = "unset_flag"]
    /\ UNCHANGED <<flag, next>>


UnsetFlag(self) ==
    /\ pc[self] = "unset_flag"
    /\ \E t \in Threads \ {self}: next' = t
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "end"]


End(self) ==
    /\ pc[self] = "end"
    /\ pc' = [pc EXCEPT ![self] = "init"]
    /\ UNCHANGED <<flag, next>>

----

ThreadActions(t) == SetFlag(t) \/ WaitForRest(t) \/ Critical(t) \/ UnsetFlag(t) \/ End(t) \/ ActiveWait(t)

Next == \E t \in Threads: ThreadActions(t)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A t \in Threads: WF_vars(WaitForRest(t))
    /\ \A t \in Threads: WF_vars(ThreadActions(t))

----

CriticalSection ==
    \/ \A t \in Threads: pc[t] /= "critical"
    \/ \E t \in Threads:
        /\ pc[t] = "critical"
        /\ \A u \in Threads \ {t}: pc[u] /= "critical"

Liveness == \A t \in Threads: <>(pc[t] = "critical")
=====
