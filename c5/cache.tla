---- MODULE cache ----
EXTENDS TLC, Integers

CONSTANTS
    ResourceCap,
    MaxConsumerCap,
    Actors

ASSUME ResourceCap > 0
ASSUME MaxConsumerCap \in 1..ResourceCap

Time == {"t1"}
Processes == Actors \cup Time

VARIABLES
    resources_left,
    resources_needed,
    reserved,
    pc


vars == <<resources_left, resources_needed, pc, reserved >>


Init ==
    /\ resources_left = ResourceCap
    /\ reserved = 0
    /\ resources_needed \in [Actors -> 1..MaxConsumerCap]
    /\ pc \in [Processes -> {"init"}]


CheckConsume(actor) ==
    (***************************************************************************)
    (* Check if there are enought resources to consume. If so reserve them and *)
    (* set up as reday for consumption                                         *)
    (***************************************************************************)
    /\ pc[actor] = "init"
    /\ resources_left >= resources_needed[actor] + reserved
    /\ reserved' = reserved + resources_needed[actor]
    /\ pc' = [pc EXCEPT ![actor] = "working"]
    /\ UNCHANGED << resources_left, resources_needed >>


Consume(actor) ==
    (******************************************************************************)
    (* Given that there are enough reserved resources, consume them one at a time *)
    (******************************************************************************)
    /\ pc[actor] = "working"
    /\ resources_needed[actor] > 0
    /\ resources_left' = resources_left - 1
    /\ resources_needed' = [resources_needed EXCEPT ![actor] = resources_needed[actor] - 1]
    /\ reserved' = reserved - 1
    /\ UNCHANGED << pc >>


RebootConsumer(actor) ==
    /\ pc[actor] = "working"
    /\ resources_needed[actor] = 0
    /\ \E x \in 1..MaxConsumerCap: resources_needed' = [resources_needed EXCEPT ![actor] = x]
    /\ pc' = [pc EXCEPT ![actor] = "init"]
    /\ UNCHANGED << resources_left, reserved >>



Refill(time) ==
    (********************************)
    (* Refill resources at any time *)
    (********************************)
    /\ pc[time] = "init"
    /\ resources_left' = ResourceCap
    /\ UNCHANGED << pc, resources_needed, reserved >>


----


Next ==
    \/ \E actor \in Actors: Consume(actor) \/ CheckConsume(actor) \/ RebootConsumer(actor)
    \/ \E timer \in Time: Refill(timer)


Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A timer \in Time: WF_vars(Refill(timer))
    /\ \A actor \in Actors: WF_vars(Consume(actor))
    /\ \A actor \in Actors: WF_vars(CheckConsume(actor))

----


NoZeroResources == resources_left >= 0


EventuallyRefills == \E n \in 1..ResourceCap: (resources_left = n)  ~> (resources_left > n)

EventuallyItsConsumed == <>(resources_left < ResourceCap)


====
