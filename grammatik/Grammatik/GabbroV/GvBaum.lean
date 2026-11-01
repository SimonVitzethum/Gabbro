/-
   File:      Grammatik/GabbroV/GvBaum.lean
   Subject:   Agent 04 task V-04c: the `TreeState` projection -- a World's
              tree edges plus occupancy into the abstract structure the
              `GvTreeParent` lemmas consume, lifted along a world run.

   Per-field commutation of the projection with `storeSlot` (on the
   `kantenBild_slotfeld_anders` pattern, reusing the accepted frames
   plus `storeSlot_anders`); run lifts for `benutzt`-preservation,
   `elternKonsistent` and `lokalBenutzt`; the `blatt_loeschen` call
   obligation (`benutzt(opfer)` for the reached victim) as a theorem
   from per-call contracts plus the initial state, with the
   reachability-monotonicity link stated as an explicit premise (it
   holds for relink shapes, fails for naive clears -- see the planted
   failure). Witness: a real leaf deletion on a concrete 3-node tree;
   planted failure: deleting a non-leaf is not covered.
-/
module

public import Grammatik.GabbroV.GvBaum.Teil1
public import Grammatik.GabbroV.GvBaum.Teil2
