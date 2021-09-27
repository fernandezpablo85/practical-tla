---- MODULE telephone ----
EXTENDS TLC, Sequences

VARIABLES
    to_send,
    received,
    in_transit,
    can_send,
    pc

vars == << to_send, received, in_transit, pc, can_send >>

Init ==
    /\ to_send = <<1, 2, 3>>
    /\ received = <<>>
    /\ in_transit = {}
    /\ can_send = TRUE
    /\ pc = "init"

Send ==
    (********************************)
    (* Sends a message from to_send *)
    (********************************)
    /\ IF can_send /\ to_send /= << >>
        THEN /\ in_transit' = in_transit \union {Head(to_send)}
             /\ to_send' = Tail(to_send)
             /\ can_send' = FALSE
             /\ UNCHANGED  << pc, received >>
        ELSE /\ UNCHANGED vars


Receive ==
    (****************************************************************************)
    (* Receives a message from in_transit.                                      *)
    (* Note: uncomment can_send' = FALSE for enabling ACK loss. This will cause *)
    (*     temporal properties to fail                                          *)
    (****************************************************************************)
    /\ \E m \in in_transit:
        /\ received' = Append(received, m)
        /\ in_transit' = in_transit \ {m}
        /\ \/ can_send' = TRUE
        \*    \/ can_send' = FALSE
        /\ UNCHANGED  << to_send, pc >>

Process ==
    (***********************************************************)
    (* Send or receive messages until all arrive at `received` *)
    (***********************************************************)
    /\ pc = "init"
    /\ IF Len(received) = 3
        THEN /\ pc' = "done"
             /\ UNCHANGED << to_send, received, in_transit, can_send >>
        ELSE \/ Send
             \/ Receive

Done == pc = "done" /\ UNCHANGED vars

Next == Process \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----
MessagesInOrder == <>[](received = <<1, 2, 3>>)
====

