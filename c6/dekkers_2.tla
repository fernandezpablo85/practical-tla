---- MODULE dekkers_2 ----
(*******************************************************************************)
(* Dekker's Algorithm built from scratch using only Wikipedia's pseudocode [1] *)
(* as reference.                                                               *)
(*                                                                             *)
(* [1] https://en.wikipedia.org/wiki/Dekker%27s_algorithm                      *)
(*******************************************************************************)

EXTENDS TLC, Integers

Threads == {1, 2}

----

VARIABLES
    want_to_enter,
    turn,
    pc

vars == <<want_to_enter, turn, pc>>

----
(*************)
(* Utilities *)
(*************)

Go(thread, state) == pc' = [pc EXCEPT ![thread] = state]

Signal(thread, bool) == want_to_enter' = [want_to_enter EXCEPT ![thread] = bool]

----

Init ==
    /\ want_to_enter \in [Threads -> {FALSE}]
    /\ turn \in Threads
    /\ pc \in [Threads -> {"init"}]


WantToEnter(thread) ==
    (***************************************************)
    (* Thread sets its boolean flag and tries to enter *)
    (* the critical section                            *)
    (***************************************************)
    /\ pc[thread] = "init"
    /\ Signal(thread, TRUE)
    /\ Go(thread, "flag_set")
    /\ UNCHANGED turn


WaitingOther(thread) ==
    (*************************************************************)
    (* Thread checks for others intention to access the critical *)
    (* section. If no one is waiting it proceeds, if there are   *)
    (* other threads with the same intention it waits it's turn  *)
    (*************************************************************)
    /\ pc[thread] = "flag_set"
    /\ IF \A t \in Threads \ {thread}: want_to_enter[t]
        THEN /\ Go(thread, "wait_turn")
        ELSE /\ Go(thread, "enter_critical")
    /\ UNCHANGED <<want_to_enter, turn>>


WaitTurn(thread) ==
    (***************************************************************)
    (* The thread checks to see if it can go ahead, if so it goes  *)
    (* back to the waiting others step. If it can't, it unsets its *)
    (* flag and busy-waits                                         *)
    (***************************************************************)
    /\ pc[thread] = "wait_turn"
    /\ IF turn = thread
        THEN /\ Go(thread, "flag_set")
             /\ UNCHANGED <<turn, want_to_enter>>
        ELSE /\ Signal(thread, FALSE)
             /\ Go(thread, "busy_wait")
             /\ UNCHANGED turn


BusyWait(thread) ==
    (************************************************************************)
    (* Thread busy waits for its turn, once it arrives it sets its flag and *)
    (* goes back to the initial wait state                                  *)
    (************************************************************************)
    /\ pc[thread] = "busy_wait"
    /\ turn = thread
    /\ Signal(thread, TRUE)
    /\ Go(thread, "flag_set")
    /\ UNCHANGED turn


CriticalSection(thread) ==
    (******************************************************************************)
    (* The critical section of the code. The /\ TRUE simulates real critical work *)
    (******************************************************************************)
    /\ pc[thread] = "enter_critical"
    /\ TRUE \* perform critical work
    /\ Go(thread, "exit_critical")
    /\ UNCHANGED <<want_to_enter, turn>>


ExitCritical(thread) ==
    (******************************************************************************)
    (* Once done, the thread unsets it's intention flag and changes the turn to a *)
    (* thread != than itself. Then goes back to the initial state.                *)
    (******************************************************************************)
    /\ pc[thread] = "exit_critical"
    /\ Signal(thread, FALSE)
    /\ \E t \in Threads \ {thread}: turn' = t
    /\ Go(thread, "init")


ThreadOps(t) ==
    \/ WantToEnter(t)
    \/ WaitingOther(t)
    \/ WaitTurn(t)
    \/ BusyWait(t)
    \/ CriticalSection(t)
    \/ ExitCritical(t)


Next == \E t \in Threads: ThreadOps(t)


Spec == Init /\ [][Next]_vars /\ \A t \in Threads: WF_vars(ThreadOps(t))

----

TypeOk ==
    /\ Threads = {1, 2}
    /\ turn \in {1, 2}
    /\ want_to_enter \in BOOLEAN \X BOOLEAN
    /\ LET valid_state == {"init", "flag_set", "enter_critical", "exit_critical", "wait_turn", "busy_wait"}
        IN /\ pc \in valid_state \X valid_state


Safety ==
    (*****************************************************************)
    (* Only one thread at a time is allowed in the critical section. *)
    (*****************************************************************)
    \/ \A t \in Threads: pc[t] /= "enter_critical"
    \/ \E t \in Threads:
        /\ pc[t] = "enter_critical"
        /\ \A u \in Threads \ {t}: pc[u] /= "enter_critical"


Liveness ==
    (*************************************************************)
    (* All threads must enter the critical section at least once *)
    (*************************************************************)
    /\ \A t \in Threads: <>(pc[t] = "enter_critical")

====