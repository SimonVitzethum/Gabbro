/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Verbrauch.lean
  Subject:   Package P1 of the closed calls of the image theorem, part 3: the consuming traversal (`verbrauchLauf`,
             C11) keeps outcomes related up to read events. Every round re-selects, reads the measure, runs the body
             and reads the measure again; selection and measure are world-reading tests (`FunLG`), so both runs make
             the same choices and compare the same numbers.
-/
module
public import Stage0.Senke.Bild.Gleich.Schleifen
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {V : Vertrag D} {Er : Fehlermarke D → Prop}

/-- A world-reading test on `≈` worlds answers a related pair. -/
theorem PaarLG.von {Γ : Ctx} {α : Type} {k : World D → Env D Γ → World D × α} (hk : FunLG k)
    {σ σ' : World D} (h : WeltGleich σ σ') (ρ : Env D Γ) : PaarLG (k σ ρ) (k σ' ρ) :=
  PaarLG.of (hk σ σ' ρ h).1 (hk σ σ' ρ h).2

theorem verbrauchLauf_lg {l : Bool} {Γ : Ctx} (t : D.Tab)
    {s₁ s₂ : World D → Env D (.index (D.count t) :: Γ) → Ausgang V true (.index (D.count t) :: Γ)}
    {inv : World D → Env D Γ → World D × Bool}
    {sel : World D → Env D Γ → World D × Option (Wert D (.index (D.count t))) × Bool}
    {massW : World D → Env D Γ → World D × Int}
    (hs : ∀ σ σ' ρ, WeltGleich σ σ' → AusLG Er (s₁ σ ρ) (s₂ σ' ρ))
    (hinv : FunLG inv) (hsel : FunLG sel) (hmass : FunLG massW) (bound : Int) :
    ∀ (fuel : Nat) (σ σ' : World D) (ρ : Env D Γ), WeltGleich σ σ' →
      AusLG Er (verbrauchLauf (l := l) t s₁ inv sel massW bound fuel σ ρ)
        (verbrauchLauf (l := l) t s₂ inv sel massW bound fuel σ' ρ)
  | 0, _, _, _, _ => .logik _
  | n + 1, σ, σ', ρ, h => by
      obtain ⟨hw, hb⟩ := hinv σ σ' ρ h
      simp only [verbrauchLauf]
      rw [hb]
      by_cases hc : (inv σ' ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact .logik _
      · rw [if_neg hc, if_neg hc]
        have hS := PaarLG.von hsel hw ρ
        generalize sel (inv σ ρ).1 ρ = A at hS ⊢
        generalize sel (inv σ' ρ).1 ρ = B at hS ⊢
        cases hS with
        | @mk σA σB x hσS =>
          obtain ⟨w, b⟩ := x
          cases w with
          | none =>
              cases b with
              | false => exact .ok hσS
              | true => exact .logik _
          | some k =>
              have hM := PaarLG.von hmass hσS ρ
              dsimp only
              generalize massW σA ρ = MA at hM ⊢
              generalize massW σB ρ = MB at hM ⊢
              cases hM with
              | @mk σmA σmB m hσm =>
                have hst := hs _ _ (.cons k ρ) hσm
                dsimp only
                generalize s₁ σmA (.cons k ρ) = o₁ at hst ⊢
                generalize s₂ σmB (.cons k ρ) = o₂ at hst ⊢
                cases hst with
                | @ok σa σb ρa hw' =>
                    have hM2 := PaarLG.von hmass hw' ρa.tail
                    dsimp only
                    generalize massW σa ρa.tail = MA2 at hM2 ⊢
                    generalize massW σb ρa.tail = MB2 at hM2 ⊢
                    cases hM2 with
                    | @mk σ2 σ2' m2 hσ2 =>
                      exact AusLG.ite (verbrauchLauf_lg t hs hinv hsel hmass bound n _ _ _ hσ2) (.logik _)
                | @next _ σa σb ρa hw' =>
                    have hM2 := PaarLG.von hmass hw' ρa.tail
                    dsimp only
                    generalize massW σa ρa.tail = MA2 at hM2 ⊢
                    generalize massW σb ρa.tail = MB2 at hM2 ⊢
                    cases hM2 with
                    | @mk σ2 σ2' m2 hσ2 =>
                      exact AusLG.ite (verbrauchLauf_lg t hs hinv hsel hmass bound n _ _ _ hσ2) (.logik _)
                | @leave _ σa σb ρa hw' =>
                    have hM2 := PaarLG.von hmass hw' ρa.tail
                    dsimp only
                    generalize massW σa ρa.tail = MA2 at hM2 ⊢
                    generalize massW σb ρa.tail = MB2 at hM2 ⊢
                    cases hM2 with
                    | @mk σ2 σ2' m2 hσ2 =>
                      obtain ⟨hw3, hb3⟩ := hinv σ2 σ2' ρa.tail hσ2
                      exact AusLG.ite (AusLG.ite_eq hb3 (.ok hw3) (.logik _)) (.logik _)
                | zurueck hw' => exact .zurueck hw'
                | why hw' => exact .why hw'
                | logik e => exact .logik e
                | hardware e => exact .hardware e
                | frueh hE => exact .frueh hE
                | fruehH hE => exact .fruehH hE

end Gabbro.Stage0.Senke.BildLauf
