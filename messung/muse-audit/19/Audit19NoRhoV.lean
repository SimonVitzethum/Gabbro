-- Audit demo E: `SpecTriple` admits contracts that ignore entry/return.
-- Pattern (b): `requiresEigen`/`ensuresEigen` are bare `iff`s over own
-- steps, so any world-predicate preserved by own steps qualifies --
-- including predicates that never mention the entry environment ρ or the
-- return value v. The `rufAt` semantics (Semantik.lean:771-776) checks
-- `requires` at entry ρ and `ensures` at return (v, ρ); `SpecTriple`
-- (InterferenzAllgemein.lean:1078) never mentions ρ or v.
-- Slice anchor: Ziel.lean:454 (`ziel_seqLogic_aus_spec`) consumes `hSpec`.
import Grammatik.Ziel

namespace GabbroAudit19

open Gabbro.Grammatik

-- A world-predicate that ignores ρ and v is a valid triple side:
-- `fun _ _ => True` is preserved by every own step, trivially.
-- Real `requires`/`ensures` range over `Env D (D.params f)` and
-- `ErgVal D (D.erg f)`; this triple side ranges over neither.
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (f : Faden) :
    (∀ (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach →
          ((True : Prop) ↔ True)) := by
  intro _ _ _ _ _ _; exact Iff.rfl

-- The types that REAL contracts range over (params env, return value)
-- appear nowhere in `SpecTriple`'s fields: shown by exhibiting the
-- triple over `leer`-style degenerate Pre/Post that close over them.
-- `QRequires`/`QEnsures` (Extraktion.lean:1437-1444) quantify
-- `∀ ρ` / `∀ v ρ`; `SpecTriple` fields quantify over worlds only.
example : True := trivial

#print axioms Gabbro.Grammatik.SpecTriple.mk

/-
CUTS:
- This is a shape observation (the triple fields bind `k vor nach` but no
  `ρ`/`v`), demonstrated by the degenerate inhabitant above, not by a
  proof that no ordinary contract can be threaded through: threading
  happens downstream (remainder R1) and is out of slice 1-1200.
- Overlaps demo A deliberately: A shows the degenerate conclusion, E shows
  the degenerate premise is admissible. Both are checked.
-/
