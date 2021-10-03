---- MODULE message_queue ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
    MaxQueueSize,
    Readers

ASSUME MaxQueueSize \in 1..10
ASSUME Cardinality(Readers) \in 1..5

VARIABLES
    queue,
    pc,
    current_message


vars == << queue, pc, current_message >>


AddToQueue(msg) ==
    /\ Len(queue) < MaxQueueSize
    /\ queue' = Append(queue, msg)


Init ==
    /\ queue = <<>>
    /\ current_message = [it \in Readers |-> "none"]
    /\ pc = [it \in {"writer"} \cup Readers |-> "ready"]


Write ==
    /\ pc["writer"] = "ready"
    /\ AddToQueue("msg")
    /\ UNCHANGED << current_message, pc >>


DoRead(self) ==
    /\ current_message' = [current_message EXCEPT ![self] = Head(queue)]
    /\ queue' = Tail(queue)
    /\ \/ UNCHANGED pc
       \/ pc' = [pc EXCEPT ![self] = "crashed"]


ReadCrashPre(self) ==
    /\ pc' = [pc EXCEPT ![self] = "crashed"]
    /\ current_message' = [current_message EXCEPT ![self] = "killed"]
    /\ UNCHANGED <<queue>>


Read(self) ==
    /\ pc[self] = "ready"
    /\ queue /= <<>>
    /\ ReadCrashPre(self) \/ DoRead(self)


ReaderReboot(self) ==
    /\ pc[self] = "crashed"
    /\ current_message' = [current_message EXCEPT ![self] = "none"]
    /\ pc' = [pc EXCEPT ![self] = "ready"]
    /\ UNCHANGED << queue >>

----

Next ==
    \/ Write
    \/ \E reader \in Readers: Read(reader) \/ ReaderReboot(reader)


Spec ==
    /\ Init
    /\ [][Next]_vars
    (***************************************************)
    (* Eventually some reader comes back from the dead *)
    (***************************************************)
    /\ WF_vars(\E r \in Readers: ReaderReboot(r))


BoundedQueue == Len(queue) <= MaxQueueSize

(*****************************************)
(* Not all Readers can stay dead forever *)
(*****************************************)
NotAllCrash == []<>(\E reader \in Readers: pc[reader] # "crashed")

====
