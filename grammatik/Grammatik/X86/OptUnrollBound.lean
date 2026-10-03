/-
  File:      Grammatik/X86/OptUnrollBound.lean
  Subject:   Bounded loop-unroll rule lemma (lane 874).

  DESIGN section 7 row "Loop unroll (bounded)": local premise "explicit `k`
  + trip evidence + remainder path in map; token ops duplicated, never
  fused", certificate "B" (block map + recomputed analysis citations),
  failure case "fuse two token ops into one wide access (tearing /
  visibility change)", phase M, cost O(k*body).

  The optimisation is stated as a generic rule lemma over arbitrary values:
  a loop trip of `n` iterations with per-iteration token list `b` rewrites
  to full groups of `k` plus a remainder of `r`, duplicating (never fusing)
  the token ops. The validator decides the side conditions
  (`unrollZulassen`); a refused optional optimisation falls back to another
  certified translation, never to a warning.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.CostSummary

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Validator-decided side conditions for one bounded-unroll site (DESIGN
    section 7 row): explicit factor `k`, trip evidence present, remainder
    path in the block map, and token ops duplicated, never fused. -/
structure UnrollCert where
  k : Nat
  tripBekannt : Bool
  restPfad : Bool
  keineFusion : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. `decide (0 < c.k)` makes the
    explicit factor positive by decision; anything else refuses. -/
def unrollZulassen (c : UnrollCert) : Bool :=
  decide (0 < c.k) && c.tripBekannt && c.restPfad && c.keineFusion

/- CUTS (skeleton):
   - Rule lemma, preservation, certificate shape, witness: follow.
-/

#print axioms unrollZulassen

end Gabbro.Grammatik.X86
