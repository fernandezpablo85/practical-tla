---- MODULE wire ----
EXTENDS Integers

VARIABLES
    snd,
    rcv,
    acc,
    amount,
    pc

vars == << snd, rcv, acc, amount, pc >>

threads == 1..2

Init ==
    /\ snd = "bob"
    /\ rcv = "alice"
    /\ acc = [p \in {"bob", "alice"} |-> 5]
    /\ amount \in 1..acc[snd]
    /\ pc = [t \in threads |-> "init"]

CheckAndWithdraw(t) ==
    /\ pc[t] = "init"
    /\ IF amount <= acc[snd] THEN
        /\ acc' = [acc EXCEPT ![snd] = acc[snd] - amount]
        /\ pc' = [pc EXCEPT ![t] = "deposit"]
        /\ UNCHANGED << snd, rcv, amount >>
        ELSE
        /\ pc' = [pc EXCEPT ![t] = "done"]
        /\ UNCHANGED << snd, rcv, acc, amount >>

Deposit(t) ==
    /\ pc[t] = "deposit"
    /\ acc' = [acc EXCEPT ![rcv] = acc[rcv] + amount]
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED << snd, rcv, amount >>

Done(t) ==
    /\ pc[t] = "done"
    /\ UNCHANGED vars

Next == \E t \in threads:
    \/ CheckAndWithdraw(t)
    \/ Deposit(t)
    \/ Done(t)


Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

------
NoOverdrafts == \A p \in {"bob", "alice"}: acc[p] >= 0

EventuallyConsistent == <>[](acc[snd] + acc[rcv] = 10)
====