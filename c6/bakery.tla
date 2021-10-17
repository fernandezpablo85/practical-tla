---- MODULE bakery ----
EXTENDS TLC, Integers, Sequences

CONSTANT N

Procs == 1..N

(*--algorithm bakery
variables
    entering \in [Procs -> {FALSE}],
    tickets \in [Procs -> {0}];

define
    MaxTicket == LET set == {tickets[i]: i \in 1..Len(tickets)}
       IN CHOOSE max \in set: \A rest \in set: max >= rest
end define;

process thread \in Procs
variables
    others = Procs \ {self},
    nxt \in Procs;
begin
    Enter: entering[self] := TRUE;
    PickNumber: tickets[self] := MaxTicket;
    Exit: entering[self] := FALSE;
    WaitEntering: while(others # {}) do
        with i \in others do
            nxt := i;
            await ~entering[i];
        end with;
    WaitTicketNumber:
        await tickets[nxt] = 0;
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b415a440" /\ chksum(tla) = "3bf68e2d")
VARIABLES entering, tickets, pc

(* define statement *)
MaxTicket == LET set == {tickets[i]: i \in 1..Len(tickets)}
   IN CHOOSE max \in set: \A rest \in set: max >= rest

VARIABLES others, nxt

vars == << entering, tickets, pc, others, nxt >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ entering \in [Procs -> {FALSE}]
        /\ tickets \in [Procs -> {0}]
        (* Process thread *)
        /\ others = [self \in Procs |-> Procs \ {self}]
        /\ nxt \in [Procs -> Procs]
        /\ pc = [self \in ProcSet |-> "Enter"]

Enter(self) == /\ pc[self] = "Enter"
               /\ entering' = [entering EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "PickNumber"]
               /\ UNCHANGED << tickets, others, nxt >>

PickNumber(self) == /\ pc[self] = "PickNumber"
                    /\ tickets' = [tickets EXCEPT ![self] = MaxTicket]
                    /\ pc' = [pc EXCEPT ![self] = "Exit"]
                    /\ UNCHANGED << entering, others, nxt >>

Exit(self) == /\ pc[self] = "Exit"
              /\ entering' = [entering EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "WaitEntering"]
              /\ UNCHANGED << tickets, others, nxt >>

WaitEntering(self) == /\ pc[self] = "WaitEntering"
                      /\ IF (others[self] # {})
                            THEN /\ \E i \in others[self]:
                                      /\ nxt' = [nxt EXCEPT ![self] = i]
                                      /\ ~entering[i]
                                 /\ pc' = [pc EXCEPT ![self] = "WaitTicketNumber"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ nxt' = nxt
                      /\ UNCHANGED << entering, tickets, others >>

WaitTicketNumber(self) == /\ pc[self] = "WaitTicketNumber"
                          /\ tickets[nxt[self]] = 0
                          /\ pc' = [pc EXCEPT ![self] = "WaitEntering"]
                          /\ UNCHANGED << entering, tickets, others, nxt >>

thread(self) == Enter(self) \/ PickNumber(self) \/ Exit(self)
                   \/ WaitEntering(self) \/ WaitTicketNumber(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
