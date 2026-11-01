/-
  File:      Grammatik/GabbroV/GvTraversal.lean
  Subject:   GabbroV: a traversal index is a member of its domain.

  Agent 03 (TODO 0f; draft lane 1391, repaired here). `RunsLoopN`
  (programmlogik `Body.lean`) bounds the range and the count of a
  traversal's passes, not the MEMBERSHIP of the index, nor that a
  `by unvisited` traversal without `leave` covers the domain
  (`beispiele/57`, `09`, `01`, `messung/caprock/kapraum`).

  This file states both over the accepted exec model (`traverseLauf` over
  `alleIndizes`, `Kern/Semantik/Semantik.lean`; no mathlib): the schedule
  is exactly the domain (complete, duplicate-free), and a run whose every
  pass continues visits every member. The visited set is a ghost log, not
  a second semantics: it applies the SAME `schritt` to the SAME states.
-/
module

public import Grammatik.GabbroV.GvTraversal.Teil1
public import Grammatik.GabbroV.GvTraversal.Teil2
