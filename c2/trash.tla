---- MODULE trash ----
EXTENDS Sequences, TLC, Integers
VARIABLES
    capacity,
    bins,
    count,
    items,
    item,
    pc

vars == << capacity, bins, count, items, pc, item >>

Init ==
    /\ pc = "init"
    /\ capacity \in [trash: 1..10, recycle: 1..10]
    /\ bins = [trash |-> <<>>, recycle |-> <<>>]
    /\ count = [trash |-> 0, recycle |-> 0]
    /\ item = [type: {"recycle", "trash"}, size: 1..6]
    /\ items \in item \X item \X item \X item

PutIn(bin, it) ==
    /\ bins'  = [bins EXCEPT ![bin] = Append(bins[bin], it)]
    /\ count' = [count EXCEPT ![bin] = count[bin] + 1]
    /\ capacity' = [capacity EXCEPT ![bin] = capacity[bin] - it.size]

Process ==
    (**************************************************************************************)
    (* • If the item is labeled as “recycling” and it is under the remaining capacity     *)
    (*     for the recycling bin, the item goes into recycling.                           *)
    (* • If the item is labeled as “trash” OR the item is labeled as “recycling” and      *)
    (*     there is not enough recycling capacity AND there is sufficient capacity in the *)
    (*     trash bin, the item goes into trash.                                           *)
    (* • Otherwise, it’s dropped on the floor and somebody else gets to sweep it up.      *)
    (**************************************************************************************)
    /\ LET it == Head(items) IN
        /\ items' = Tail(items)
        /\ IF it.type = "recycle" /\ it.size < capacity.recycle THEN
            /\ PutIn("recycle", it)
            ELSE
            /\ IF it.size < capacity.trash THEN
                /\ PutIn("trash", it)
                ELSE
                /\ UNCHANGED << bins, count, capacity >>

ProcessAll ==
    /\ pc = "init"
    /\ IF items # <<>> THEN
        /\ Process
        /\ UNCHANGED << pc, item >>
        ELSE
        /\ pc'= "done"
        /\ UNCHANGED << capacity, bins, count, items, item >>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == ProcessAll \/ Done
----
NoOverflow == capacity.trash >= 0 /\ capacity.recycle >= 0
RecycleCountOk == Len(bins.recycle) = count.recycle
RecycleTrashOk == Len(bins.trash) = count.trash
====
