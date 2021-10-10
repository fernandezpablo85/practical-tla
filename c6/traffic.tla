---- MODULE traffic ----

VARIABLES
    at_light,
    light

vars == << at_light, light >>

Init ==
    /\ at_light = TRUE
    /\ light = "red"


NextColor(color) == CASE color = "red" -> "green"
                      [] color = "green" -> "red"

LightToggle ==
    /\ at_light
    /\ light' = NextColor(light)
    /\ UNCHANGED at_light

CarMoves ==
    /\ light = "green"
    /\ at_light' = FALSE
    /\ UNCHANGED light

Next == LightToggle \/ CarMoves

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(LightToggle)
    /\ SF_vars(CarMoves)

----
CarRuns == <>(at_light = FALSE)

====
