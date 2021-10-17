---- MODULE max ----
EXTENDS TLC, Sequences, Integers

CONSTANT ListLength
ASSUME ListLength >= 1

Numbers == -5..5

Seqs == UNION {[1..m -> Numbers]: m \in 1..ListLength}

Max(seq) ==
    LET set == {seq[i]: i \in 1..Len(seq)}
    IN CHOOSE max \in set: \A rest \in set: max >= rest

VARIABLES
    seq,
    max,
    pc

Init ==
    /\ seq \in Seqs
    /\ max = 0
    /\ pc = "start"

GetMax ==
    /\ pc = "start"
    /\ max' = Max(seq)
    /\ pc' = "done"
    /\ UNCHANGED seq

Done ==
    /\ pc = "done"
    /\ UNCHANGED <<seq, max, pc>>

Next == GetMax \/ Done

----
Maxed == (pc = "done") => ~\E i \in 1..Len(seq): seq[i] > max

====