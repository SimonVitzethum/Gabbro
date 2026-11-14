/- Fuel induction at one retry header, independent of code replication. -/
module
public import Stage0.Senke.Anweisung.Simulation
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR
variable [Kern]

/-- Condition-first retry composition. Every continuing pass supplies a real
    backedge and the smaller-fuel header in the memory produced by that pass. -/
theorem retry_runtime {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
    {Γ : Ctx} {l : Bool} {reserved : Nat} {sc : List D.Lock}
    {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp fp pc exit outerLeave outerNext : W} {lo K : Nat} {pr : List Nat}
    (body : World D → Env D Γ → Ausgang (vertragVon D f) true Γ)
    (bis : World D → Env D Γ → World D × Bool)
    (overflow : World D → Env D Γ → Ausgang (vertragVon D f) l Γ)
    (entry : Nat → Mem → World D → Env D Γ → Prop)
    (lower : FB ≤ lo)
    (success : ∀ n m σ ρ, entry n m σ ρ → (bis σ ρ).2 = true →
      Reach L fp lo K pr ⟨pc, fp⟩ m exit (bis σ ρ).1 ρ reserved)
    (zero : ∀ m σ ρ, entry 0 m σ ρ → (bis σ ρ).2 ≠ true →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
        (overflow (bis σ ρ).1 ρ) reserved sc)
    (pass : ∀ n m σ ρ, entry (n + 1) m σ ρ → (bis σ ρ).2 ≠ true →
      match body (bis σ ρ).1 ρ with
      | .ok σ' ρ' | .next _ σ' ρ' =>
        ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
          Keeps fp pr m m' ∧ entry n m' σ' ρ'
      | o => Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m pc exit pc o reserved sc) :
    ∀ n m σ ρ, entry n m σ ρ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
        (retryLauf body bis overflow n σ ρ) reserved sc := by
  intro n
  induction n with
  | zero =>
    intro m σ ρ he
    simp only [retryLauf]
    by_cases done : (bis σ ρ).2 = true
    · simp only [done, ↓reduceIte]
      exact success 0 m σ ρ he done
    · simp only [done, ↓reduceIte]
      exact zero m σ ρ he done
  | succ n ih =>
    intro m σ ρ he
    simp only [retryLauf]
    by_cases done : (bis σ ρ).2 = true
    · simp only [done, ↓reduceIte]
      exact success (n + 1) m σ ρ he done
    · simp only [done, ↓reduceIte]
      have step := pass n m σ ρ he done
      have again : ∀ σ' ρ',
          (∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
            Keeps fp pr m m' ∧ entry n m' σ' ρ') →
          Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
            (retryLauf body bis overflow n σ' ρ') reserved sc := by
        intro σ' ρ' next
        obtain ⟨m', run, frame, kept, he'⟩ := next
        exact Sim.prefix lower run frame kept (ih m' σ' ρ' he')
      generalize hb : body (bis σ ρ).1 ρ = o at step ⊢
      cases o with
      | ok σ' ρ' => exact again σ' ρ' step
      | next h σ' ρ' => exact again σ' ρ' step
      | leave h σ' ρ' => exact step
      | zurueck | why | logik | hardware => exact step

end Gabbro.Stage0.Senke
