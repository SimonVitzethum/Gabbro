module
public import Bruecke.Anweisung.Schleife.Ausgang
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- The actual canonical retry runner and Body's finite constructor have the same
    operational outcomes. Read bookkeeping is explicit in `htest`. The static bound
    counts body executions; the stop test also runs after the last one.

    This is the semantic lifting lemma, not an admission theorem for `zuBodyZ`. Its
    premises must be discharged by the source reader before a form is carried. -/
theorem retry_operational_sim
    (state : World D → Env D Γ → Gabbro.Body.State → Prop)
    (result : World D → ErgVal D V.erg → Gabbro.Body.State → Option Gabbro.Body.Value → Prop)
    (reason : World D → Fin V.gruende → Gabbro.Body.State → Option Gabbro.Body.Value → Prop)
    (pass : World D → Env D Γ → Ausgang V true Γ)
    (test : World D → Env D Γ → World D × Bool)
    (overflow : World D → Env D Γ → Ausgang V l Γ)
    (ρB : Gabbro.Body.Env) (stop : Gabbro.Body.Expr) (body exceeded : List Gabbro.Body.Stmt)
    (htest : ∀ σ ρ s, state σ ρ s →
      ∃ σ' b, test σ ρ = (σ', b) ∧ state σ' ρ s ∧
        Gabbro.Body.eval s stop = some (.bool b))
    (hpass : ∀ σ ρ s, state σ ρ s →
      OperationalRel state result reason (pass σ ρ) (Gabbro.Body.exec ρB body s))
    (hover : ∀ σ ρ s, state σ ρ s →
      OperationalRel state result reason (overflow σ ρ) (Gabbro.Body.exec ρB exceeded s)) :
    ∀ fuel σ ρ s, state σ ρ s →
      OperationalRel state result reason (retryLauf pass test overflow fuel σ ρ)
        (Gabbro.Body.step ρB (.retry fuel stop body exceeded) s)
  | 0, σ, ρ, s, hs => by
      obtain ⟨σ', b, ht, hr, hc⟩ := htest σ ρ s hs
      cases b with
      | true =>
          rw [Gabbro.Body.retry_done ρB 0 stop body exceeded s hc]
          simpa only [retryLauf, ht, ↓reduceIte, OperationalRel] using hr
      | false =>
          rw [Gabbro.Body.retry_exceeded ρB stop body exceeded s hc]
          simpa only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte] using hover σ' ρ s hr
  | n + 1, σ, ρ, s, hs => by
      obtain ⟨σ', b, ht, hr, hc⟩ := htest σ ρ s hs
      cases b with
      | true =>
          rw [Gabbro.Body.retry_done ρB (n + 1) stop body exceeded s hc]
          simpa only [retryLauf, ht, ↓reduceIte, OperationalRel] using hr
      | false =>
          have hp := hpass σ' ρ s hr
          cases hg : pass σ' ρ with
          | ok σ₁ ρ₁ =>
              cases hb : Gabbro.Body.exec ρB body s <;>
                simp only [hg, hb, OperationalRel] at hp
              rename_i t
              rw [Gabbro.Body.retry_running ρB n stop body exceeded s t hc hb]
              simpa only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte, hg] using
                retry_operational_sim state result reason pass test overflow ρB stop body exceeded
                  htest hpass hover n σ₁ ρ₁ t hp
          | next h σ₁ ρ₁ =>
              cases hb : Gabbro.Body.exec ρB body s <;>
                simp only [hg, hb, OperationalRel] at hp
              rename_i t
              rw [Gabbro.Body.retry_next ρB n stop body exceeded s t hc hb]
              simpa only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte, hg] using
                retry_operational_sim state result reason pass test overflow ρB stop body exceeded
                  htest hpass hover n σ₁ ρ₁ t hp
          | leave h σ₁ ρ₁ =>
              cases hb : Gabbro.Body.exec ρB body s <;>
                simp only [hg, hb, OperationalRel] at hp
              rename_i t
              rw [Gabbro.Body.retry_leave ρB n stop body exceeded s t hc hb]
              simpa only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte, hg, OperationalRel] using hp
          | zurueck σ₁ v =>
              cases hb : Gabbro.Body.exec ρB body s <;>
                simp only [hg, hb, OperationalRel] at hp
              rename_i t value
              rw [Gabbro.Body.retry_returned ρB n stop body exceeded s t value hc hb]
              simpa only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte, hg, OperationalRel] using hp
          | why σ₁ r =>
              cases hb : Gabbro.Body.exec ρB body s <;>
                simp only [hg, hb, OperationalRel] at hp
              rename_i t value
              rw [Gabbro.Body.retry_returned ρB n stop body exceeded s t value hc hb]
              simpa only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte, hg, OperationalRel] using hp
          | logik e =>
              cases hb : Gabbro.Body.exec ρB body s <;>
                simp only [hg, hb, OperationalRel] at hp
              simp only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte, hg,
                Gabbro.Body.step, Gabbro.Body.retryRun, hc, hb, OperationalRel]
          | hardware e =>
              cases hb : Gabbro.Body.exec ρB body s <;>
                simp only [hg, hb, OperationalRel] at hp
              simp only [retryLauf, ht, Bool.false_eq_true, ↓reduceIte, hg,
                Gabbro.Body.step, Gabbro.Body.retryRun, hc, hb, OperationalRel]

end Gabbro.Bruecke
