---- MODULE linear_search ----
EXTENDS TLC, Integers, Sequences

CONSTANT MaxInt
ASSUME MaxInt > 1

----
Seqs(s, n) == UNION {[1..m -> s]: m \in 1..n}

OrderedSeq(set, n) == {seq \in Seqs(set, n): \A i \in 2..Len(seq): seq[i] >= seq[i-1]}

Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2*f[x-1]
    IN f[n]
----

VARIABLES
    i,
    pc,
    seq,
    target,
    found,
    count

vars == << i, pc, seq, target, found, count >>

Init ==
    /\ pc = "init"
    /\ i = 1
    /\ seq \in OrderedSeq(1..MaxInt, MaxInt)
    /\ target \in 1..MaxInt
    /\ found = 1
    /\ count = 0

DoSearch ==
    /\ count' = count + 1
    /\ IF seq[i] = target
        THEN /\ found' = i
             /\ pc' = "done"
             /\ UNCHANGED <<seq, target, i>>
        ELSE /\ i' = i + 1
             /\ UNCHANGED <<seq, target, pc, found>>

Search ==
    /\ pc = "init"
    /\ IF i <= Len(seq)
        THEN DoSearch
        ELSE /\ pc' = "done"
             /\ UNCHANGED <<seq, target, i, found, count>>

Done ==
    /\ pc = "done"
    /\ LET seq_contains_target == target \in {seq[x]: x \in DOMAIN seq}
           element_found == target = seq[found]
        IN /\ Assert(seq_contains_target => element_found, <<"element", target, "not found">>)

    \* this will always fail because search is linear
    \* /\ Assert(Pow2(count - 1) <= Len(seq), <<"function must be log-n", count>>)
    /\ UNCHANGED vars

Next == Search \/ Done

====