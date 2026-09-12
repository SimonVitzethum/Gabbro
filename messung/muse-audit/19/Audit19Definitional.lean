-- Audit demo D: the "goal" legs that are definitional restatements.
-- Pattern (a): conclusion equal to a premise modulo unfolding / case split.
-- Ziel.lean:107 (`absenkung_wert`), :110 (`absenkung_haelt_schranke`),
-- :125 (`ziel_zwei_fehler`/`ziel`), :132 (`ziel_total`), :139
-- (`ziel_deterministisch`), and the Absenkung leg `hLowering.begrenzt`
-- inside `ziel_nutzer_last` (line 388).
import Grammatik.Ziel
import Grammatik.Satz

namespace GabbroAudit19

open Gabbro.Grammatik

-- (a1) `absenkung_wert`: the conclusion IS the definition, by rfl.
example : absenkung.proPrimitiv = 17 := rfl

-- (a2) `absenkung_haelt_schranke`: the conclusion IS the structure field.
-- Any `Absenkung` proves its own bound by projection; the witness adds nothing.
example (A : Absenkung) : A.proPrimitiv ≤ 18 := A.begrenzt

-- (a3) `ziel_zwei_fehler` / `ziel`: case split on the inductive itself.
-- The "every outcome is ..." claim is the constructor list restated.
example {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (o : Ausgang V l Γ) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) := by
  cases o
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))))

-- (a4) `ziel_total`: any function is "total" by `⟨_, rfl⟩`.
example {D : Deklaration} (f : Nat → Nat) (n : Nat) : ∃ m, f n = m :=
  ⟨_, rfl⟩

-- (a5) `ziel_deterministisch`: `x = x` by rfl; mentions `exec` twice
-- but observes nothing about it.
example {D : Deklaration} (f : Nat → Nat) (n : Nat) : f n = f n := rfl

-- (a6) the Absenkung leg of `ziel_nutzer_last` (line 388) is `A.begrenzt`:
-- conclusion = premise field, no lowering map is ever consulted.
example (A : Absenkung) : A.proPrimitiv ≤ 18 := A.begrenzt

#print axioms Gabbro.Grammatik.ziel
#print axioms Gabbro.Grammatik.absenkung_haelt_schranke

/-
CUTS:
- The file itself already flags `ziel_zeit_ist_hardware` as withdrawn for
  exactly this reason (lines 255-263); these demos show the same shape
  survives in the six legs above. Whether the legs still add value as
  named conjunction members is an editorial judgment, stated here, not proved.
-/
