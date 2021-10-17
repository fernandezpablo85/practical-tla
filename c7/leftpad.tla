---- MODULE leftpad ----
EXTENDS TLC, Integers, Sequences

----
Seqs(s, n) == UNION {[1..m -> s]: m \in 1..n}
----

Max(a, b) == IF a > b THEN a ELSE b

Leftpad(padding, padded_size, str) ==
    LET
        padded_length == Max(Len(str), padded_size)
        pad_length == CHOOSE l \in 0..padded_size:
            l + Len(str) = padded_length
    IN
        [x \in 1..pad_length |-> padding] \o str

VARIABLES
    unpadded,
    padded,
    padding,
    pc

vars == <<unpadded, padded, padding, pc>>

Init ==
    /\ unpadded \in Seqs({"a", "b", "c", "d"}, 5)
    /\ padding \in 1..10
    /\ padded = ""
    /\ pc = "init"

LP ==
    /\ pc = "init"
    /\ padded' = Leftpad(" ", padding, unpadded)
    /\ pc' = "done"
    /\ UNCHANGED <<unpadded, padding>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == LP \/ Done

----
PaddedEndsUpWithUnpadded ==
    /\ (pc = "done") => \A i \in 0..Len(unpadded)-1: unpadded[Len(unpadded) - i] = padded[Len(padded) - i]

PaddedHasAtLeastPadLength ==
    /\ (pc = "done") => Len(padded) >= padding

IfPaddedIsLargerThanUnpaddedItMustBeginWithPad ==
    /\ (Len(padded) > Len(unpadded)) => padded[1] = " "
====