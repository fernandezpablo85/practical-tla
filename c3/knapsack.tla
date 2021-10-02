---- MODULE knapsack ----
EXTENDS TLC, Integers, Sequences, Naturals

(*****************************************************************************************)
(* We have a knapsack of volume N and a set of items. Each item has a value and a size.  *)
(* You can fit any number of each item in the knapsack as long as the sum of them all is *)
(* less than the capacity of the sack. What’s the most valuable knapsack you can make?   *)
(*****************************************************************************************)

CONSTANTS
    Capacity,
    Items,
    Sizes,
    Values

ASSUME Capacity \in Nat \ {0}
ASSUME Sizes \subseteq 1..Capacity
ASSUME \A v \in Values: v \in Nat

VARIABLES pc, chosen

ItemParams == [size: Sizes, value: Values]

ItemSets == [Items -> ItemParams]

Knapsacks == [Items -> 0..4]

HardcodedItemSet == [
  a |-> [size |-> 1, value |-> 1],
  b |-> [size |-> 2, value |-> 3],
  c |-> [size |-> 3, value |-> 1]
]

----

ReduceSet(op(_, _), set, acc) ==
    (**************************************)
    (* Shamelessly stolen from PT library *)
    (**************************************)
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]


KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)


KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)


ValidKnapsacks(itemset) ==
  {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}


BestKnapsackSlow(itemset) ==
    LET all == ValidKnapsacks(itemset)
        val(k) == KnapsackValue(k, itemset)

    IN CHOOSE all_the_best \in SUBSET all: \* there exists a subset of all knapsacks such that
        /\ all_the_best # {} \* is not empty
        /\ \A good \in all_the_best:
            /\ \A best \in all_the_best: val(best) = val(good) \* every knapsack has the same value
            /\ \A not_best \in (all \ all_the_best): val(good) > val(not_best) \* it's value is greater than all other knapsacks.


BestKnapsack(itemset) ==
    (*************************************************************************)
    (* Select the knapsack with the highest value, then select all Knapsacks *)
    (* with that same value                                                  *)
    (*************************************************************************)
    LET all == ValidKnapsacks(itemset)
        val(k) == KnapsackValue(k, itemset)
        best == CHOOSE x \in all: \A y \in (all \ {x}): val(x) >= val(y)
    IN {k \in all: val(k) = val(best) }


----

Init ==
    /\ pc = "init"
    /\ chosen = {}


PickBest ==
    /\ pc = "init"
    /\ chosen' = { BestKnapsack(it): it \in ItemSets }
    /\ pc' = "done"


Done ==
    /\ pc = "done"
    /\ PrintT(<<"best knapsack", chosen>>)
    /\ UNCHANGED << pc, chosen >>


Next == PickBest \/ Done


========
