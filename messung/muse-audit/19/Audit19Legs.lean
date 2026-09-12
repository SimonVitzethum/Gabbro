-- Audit demo H: `ziel_nutzer_last`'s outcome leg and lowering leg are
-- premise-projections. Pattern (a): the 6th conjunct (`zwei_fehler o`)
-- uses only `o`, and the 5th (`hLowering.begrenzt`) only `hLowering`;
-- both hold independently of every other premise. Demonstrated by
-- re-proving each leg from its single premise alone.
-- Slice anchors: Ziel.lean:370 (`hLowering : Absenkung`), :379-380
-- (outcome disjunction), :388-389 (proof lines).
import Grammatik.Ziel

namespace GabbroAudit19

open Gabbro.Grammatik

-- Outcome leg from `o` alone: no run, contract, probe, or lowering
-- premise is needed. (This is `zwei_fehler`, already demo D(a3);
-- here it is shown in the exact §5 conclusion shape.)
example {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (o : Ausgang V l Γ) :
    ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨
      (∃ σ r, o = .grund σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e)) :=
  zwei_fehler o

-- Lowering leg from `hLowering` alone: no program, trace, or measurement
-- premise is needed; the "measured witness" plays no role in the proof
-- term `exact hLowering.begrenzt`.
example (hLowering : Absenkung) : hLowering.proPrimitiv ≤ 18 :=
  hLowering.begrenzt

-- The section-4 docstring rule ("was hier stuende und dort beweist,
-- waere ein Kommentar, der mehr behauptet als sein Satz", Ziel.lean:271)
-- applied symmetrically: `ziel` restates `zwei_fehler` proved elsewhere
-- (Satz.lean:50), so by that rule it is itself such a comment.
example {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (o : Ausgang V l Γ) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) :=
  ziel o

#print axioms Gabbro.Grammatik.ziel_nutzer_last

/-
CUTS:
- Load-bearing in the elaboration sense is NOT disputed: deleting `o` or
  `hLowering` breaks the proof term. The audit point is semantic: these
  two legs are independent of the other 20+ premises, so the conjunction
  proves no connection between the outcome classification (or the bound)
  and the run/contract/probe legs. That independence is demonstrated by
  the single-premise proofs above.
-/
