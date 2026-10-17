/-
  File:      Grammatik/RennfreiOrte.lean
  Subject:   RACE FREEDOM ON UNGUARDED CARRIERS -- what a thread can touch
             is bounded by its call graph, so an unguarded carrier that one
             thread's graph may write and no other thread's graph may read
             or write is never part of a cross-thread pair.

  `rennfrei_g_voll` (RennfreiVoll.lean) orders every cross-thread pair on a
  LOCK-GUARDED carrier. For an unguarded carrier there is no lock to order
  anything, so the claim there is that such a pair does not exist. That
  needs two static bounds per step, both new:

  * **Reads.** Every read event a step records lies on a carrier of the
    footprint `fussOrteG P f` of the function `f` of the acting frame. The
    residue predicate `GRest.oR P C` ("every expression still to run reads
    only carriers in `C`", over the existing `blockOrteP`/`endblockOrteP`)
    is kept by every rule (`schrittOrte`, the twin of `schrittMerk`); the
    frame invariant `OrteInvG` holds on every reachable machine
    (`orteInvG_erreichbar`) with `C` the footprint of each frame's function.
  * **Writes.** Every write event a step records is on a carrier the acting
    frame's function may write by signature (`TraegerSchreibt`): every write
    form carries its permission `hw` in the syntax; axioms write only their
    declared frame, which the call's `hw` bounds. Memory changes are
    `schritt_traeger`.

  `schritt_zugriffe` joins both per step. With the call-graph invariant
  `merkInvG_erreichbar` every acting function lies in its thread's call
  graph, which gives `zugriff_im_graph`, and from it the theorem
  `rennfrei_ungeschuetzt`: a carrier that is SEPARATED over the call graphs
  (`SchreibGetrenntK`: one graph may write it => no other graph may write it
  or have it in a footprint) has no cross-thread access pair with a write.
  `rennfrei_alle` combines both halves into the full race-freedom statement
  for every carrier that is not atomic and not a publish payload.
-/

import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T1
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T2
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T3
