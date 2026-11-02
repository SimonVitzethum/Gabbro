module
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil2Basis
import all Grammatik.Logik.Vertraege.HandlerKongruenz.Teil2Basis

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
/-! ## 5. ONE UNFOLDING OF `rufAt`, and its congruence

    `rufAt P O passes (n+1)` IS one entry-contract test, one body run against
    the handler `rufAt P O passes n`, one exit-contract test and the owed
    invariants (`rufAt_succ_eq` -- `rfl`). Naming that step as a function of
    the handler is what lets the congruence above be used at the call level:
    the two consumers both compare `rufAt` with SOME other handler in exactly
    this shape. -/

/-- **One unfolding of `rufAt`, with the handler as a parameter.** -/
def rufSchritt (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) : RufAusgang f :=
  let σ := σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
  if wahr? (eval σ (P.requires f) σ ρ) = false then .logik (.vorbedingung f) else
  match execEnd (V := vertragVon D f) O passes R (P.rumpf f) σ ρ with
  | EndAusgang.zurueck σ' v =>
      let σ' := σ'.lese (vertragVon D f).ende (P.ensures f).orte
      if wahr? (eval σ (P.ensures f) σ' (ergEnv (D.erg f) v ρ)) = false then
        .logik (.nachbedingung f)
      else
        let σ' := (D.invs.filter (schuldet f)).foldl
          (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ'
        match D.invs.find? (fun i => schuldet f i && !wahr? (eval σ' (P.invariante i) σ' .nil)) with
        | Option.some i => .logik (.invariante i)
        | Option.none => .ok σ' v
  | .why σ' r => .why σ' r
  | .leave h _ _ => absurd h (by decide)
  | .next h _ _ => absurd h (by decide)
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- **`rufAt` at depth `n+1` IS that step over `rufAt` at depth `n`** -- by
    definition, so `rfl`. -/
theorem rufAt_succ_eq (P : Programm D) (O : Orakel D) (passes n : Nat) :
    rufAt P O passes (n + 1) = rufSchritt P O passes (rufAt P O passes n) := by rfl

/-- **THE CONGRUENCE AT THE CALL LEVEL.** Two handlers that differ only where
    the first answers an error give CALLS that differ only where the first is
    an error -- the entry test, the exit test and the invariant test are the
    same computation on both sides, and the body run is related by
    `Endblock.kongruent`. -/
theorem rufSchritt_kongruent {Er : Fehlermarke D → Prop}
    {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : HandlerUnter Er R₁ R₂) (P : Programm D) (O : Orakel D) (passes : Nat)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    RufUnter Er (rufSchritt P O passes R₁ f σ ρ) (rufSchritt P O passes R₂ f σ ρ) := by
  have hcong := Endblock.kongruent (V := vertragVon D f) O passes R₁ R₂ hR (P.rumpf f)
    (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ
  simp only [rufSchritt]
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (P.requires f) (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = false
  · rw [if_pos hq, if_pos hq]; exact Or.inl rfl
  · rw [if_neg hq, if_neg hq]
    rcases hcong with h | ⟨mk, h1, hE⟩
    · rw [h]
      cases hx : execEnd (V := vertragVon D f) O passes R₂ (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ with
      | zurueck σ' v => exact Or.inl rfl
      | why σ' r => exact Or.inl rfl
      | leave hl σ' ρ' => exact Or.inl rfl
      | next hl σ' ρ' => exact Or.inl rfl
      | logik e => exact Or.inl rfl
      | hardware e => exact Or.inl rfl
    · exact Or.inr ⟨mk, by rw [h1]; cases mk <;> rfl, hE⟩

#print axioms Gabbro.Grammatik.rufSchritt_kongruent
#print axioms Gabbro.Grammatik.Stmt.kongruent
#print axioms Gabbro.Grammatik.Block.kongruent
#print axioms Gabbro.Grammatik.Endblock.kongruent

end Gabbro.Grammatik
