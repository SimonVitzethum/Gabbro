-- Audit demo F: `invErhalt_aus_Kontext` discards both worlds' content.
-- Pattern (a): the `iff` conclusion follows from `hInv` alone; the two
-- worlds `vor`/`nach` contribute only membership facts, and the invariant
-- predicate at each world is never unfolded. Any two chain worlds agree
-- on every carrier invariant -- by construction of the premise, not by
-- any step reasoning. Slice anchor: Ziel.lean:581-666 consumes this via
-- `interferenceFree_of_invariantForm` in the §8 leg.
import Grammatik.Ziel

namespace GabbroAudit19

open Gabbro.Grammatik

-- The proof term `⟨fun _ => hInv c nach hkn, fun _ => hInv c vor hkv⟩`
-- ignores its argument in both directions: the forward direction never
-- uses `I.inv c vor`, the backward never uses `I.inv c nach`.
-- Demonstrated: from `hInv` alone, `I.inv c nach` holds with the
-- hypothesis `I.inv c vor` discharged vacuously.
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (vor nach : World D)
    (hkn : nach ∈ J.welten) (_ : I.inv c vor) :
    I.inv c nach :=
  hInv c nach hkn

-- Correlate: with `hInv`, the "preservation" across a foreign step is
-- independent of the step -- worlds, writer, locks all drop out.
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (vor nach : World D)
    (hkv : vor ∈ J.welten) (hkn : nach ∈ J.welten) :
    I.inv c vor ↔ I.inv c nach :=
  invErhalt_aus_Kontext Nb J I hInv c vor nach hkv hkn

#print axioms Gabbro.Grammatik.invErhalt_aus_Kontext

/-
CUTS:
- This is pattern (a) in the strict sense: the conclusion's `iff` is the
  premise `hInv` applied twice, with both payloads discarded. It is still
  a valid lemma; the audit point is only that the §7/§8 "no per-run
  interference proof" claim rests on `hInv` (invariant at EVERY chain
  world) doing all the work -- and §8 derives `hInv` from entry/return/
  watch, which is where the real obligations sit.
- Not demonstrated: whether `hEntry`/`hReturn`/`hWatch` are dischargeable
  for ordinary programs; out of slice 1-1200.
-/
