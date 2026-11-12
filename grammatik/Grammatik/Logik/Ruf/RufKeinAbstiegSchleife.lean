/-
  File:      Grammatik/RufKeinAbstiegSchleife.lean
  Subject:   **PRESERVATION OF "NO `abstieg`" THROUGH OUTCOME TRANSFORMERS
              AND LOOP COMBINATORS** -- the pieces the body induction
              (`RufKeinAbstieg.lean`) needs as premises.

  A handler that never answers `logik (abstieg _)` runs no body into one:
  every `logik` outcome a non-call statement produces itself
  (`vorzustand`, `schleife`, `bereich`, `kapazitaet`) is a different
  constructor, and every outcome transformer (`schrumpf`, `schrumpfArm`,
  `zuAusgang`, `weiterOpt`, `mapWelt`) maps a `logik e` to itself. The four
  loop combinators rerun their body, so they preserve the absence by
  induction on the list respectively the fuel.
-/
module
public import Grammatik.Kern.Semantik.Semantik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. The outcome transformers -/

/-- `schrumpf` maps a `logik e` to itself, so it preserves the absence. -/
theorem Ausgang.schrumpf_keinAbstieg {l : Bool} {Γ : Ctx} {τ : Ty}
    {x : Ausgang V l (τ :: Γ)} {hh : D.Fn} (h : x ≠ .logik (.abstieg hh)) :
    x.schrumpf ≠ .logik (.abstieg hh) := by
  cases x <;> simp only [Ausgang.schrumpf] <;>
    intro hc <;> cases hc <;> exact h rfl

/-- `schrumpf` maps a `logik e` to itself, so it preserves the absence. -/
theorem EndAusgang.schrumpf_keinAbstieg {l : Bool} {Γ : Ctx} {τ : Ty}
    {x : EndAusgang V l (τ :: Γ)} {hh : D.Fn} (h : x ≠ .logik (.abstieg hh)) :
    x.schrumpf ≠ .logik (.abstieg hh) := by
  cases x <;> simp only [EndAusgang.schrumpf] <;>
    intro hc <;> cases hc <;> exact h rfl

/-- `schrumpfArm` is the identity or a `schrumpf`, so it preserves the absence. -/
theorem Ausgang.schrumpfArm_keinAbstieg {l : Bool} {Γ : Ctx} (c : Option Ty)
    {x : Ausgang V l (ArmCtx Γ c)} {hh : D.Fn} (h : x ≠ .logik (.abstieg hh)) :
    x.schrumpfArm c ≠ .logik (.abstieg hh) := by
  cases c <;> cases x <;>
    simp only [Ausgang.schrumpfArm, Ausgang.schrumpf] <;>
    intro hc <;> cases hc <;> exact h rfl

/-- `zuAusgang` maps a `logik e` to itself, so it preserves the absence. -/
theorem EndAusgang.zuAusgang_keinAbstieg {l : Bool} {Γ : Ctx}
    {x : EndAusgang V l Γ} {hh : D.Fn} (h : x ≠ .logik (.abstieg hh)) :
    x.zuAusgang ≠ .logik (.abstieg hh) := by
  cases x <;> simp only [EndAusgang.zuAusgang] <;>
    intro hc <;> cases hc <;> exact h rfl

/-- `weiterOpt` is the identity or a `schrumpf`, so it preserves the absence. -/
theorem Ausgang.weiterOpt_keinAbstieg {l : Bool} {Γ : Ctx} (e : Option Ty)
    {x : Ausgang V l (ErgCtx Γ e)} {hh : D.Fn} (h : x ≠ .logik (.abstieg hh)) :
    Ausgang.weiterOpt e x ≠ .logik (.abstieg hh) := by
  cases e <;> cases x <;>
    simp only [Ausgang.weiterOpt, Ausgang.schrumpf] <;>
    intro hc <;> cases hc <;> exact h rfl

/-- `weiterOpt` is the identity or a `schrumpf`, so it preserves the absence. -/
theorem EndAusgang.weiterOpt_keinAbstieg {l : Bool} {Γ : Ctx} (e : Option Ty)
    {x : EndAusgang V l (ErgCtx Γ e)} {hh : D.Fn} (h : x ≠ .logik (.abstieg hh)) :
    EndAusgang.weiterOpt e x ≠ .logik (.abstieg hh) := by
  cases e <;> cases x <;>
    simp only [EndAusgang.weiterOpt, EndAusgang.schrumpf] <;>
    intro hc <;> cases hc <;> exact h rfl

/-- `mapWelt` maps a `logik e` to itself, so it preserves the absence. -/
theorem Ausgang.mapWelt_keinAbstieg {l : Bool} {Γ : Ctx}
    {x : Ausgang V l Γ} {hh : D.Fn} (f : World D → World D)
    (h : x ≠ .logik (.abstieg hh)) :
    x.mapWelt f ≠ .logik (.abstieg hh) := by
  cases x <;> simp only [Ausgang.mapWelt] <;>
    intro hc <;> cases hc <;> exact h rfl

/-! ## 2. The four loop combinators -/

/-- A `traverse` run whose body never ends in an `abstieg` never ends in one. -/
theorem traverseKeinAbstieg {l : Bool} {Γ : Ctx} {τ : Ty}
    (step : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ (σ : World D) (ρ : Env D (τ :: Γ)) (hh : D.Fn),
      step σ ρ ≠ .logik (.abstieg hh)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ) (hh : D.Fn),
      traverseLauf (l := l) step inv ks σ ρ ≠ .logik (.abstieg hh)
  | [], σ, ρ, hh => by
      simp only [traverseLauf]
      split
      · intro hc; cases hc
      · intro hc; cases hc
  | k :: ks, σ, ρ, hh => by
      simp only [traverseLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc]; intro he; cases he
      · rw [if_neg hc]
        cases hx : step (inv σ ρ).1 (.cons k ρ) with
        | ok σ' ρ' => dsimp only; exact traverseKeinAbstieg step inv hs ks σ' ρ'.tail hh
        | next _ σ' ρ' => dsimp only; exact traverseKeinAbstieg step inv hs ks σ' ρ'.tail hh
        | leave _ σ' ρ' =>
            dsimp only
            split
            · intro hc; cases hc
            · intro hc; cases hc
        | zurueck _ _ => dsimp only; intro hc; cases hc
        | why _ _ => dsimp only; intro hc; cases hc
        | logik e => dsimp only; exact fun hc => hs _ _ hh (hx.trans (by cases hc; rfl))
        | hardware _ => dsimp only; intro hc; cases hc

/-- A consuming run whose body never ends in an `abstieg` never ends in one. -/
theorem verbrauchKeinAbstieg {l : Bool} {Γ : Ctx} (t : D.Tab)
    (step : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ (σ : World D) (ρ : Env D (.index (D.count t) :: Γ)) (hh : D.Fn),
      step σ ρ ≠ .logik (.abstieg hh)) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ) (hh : D.Fn),
      verbrauchLauf (l := l) t step inv sel massW bound fuel σ ρ ≠
        .logik (.abstieg hh)
  | 0, σ, ρ, hh => by
      simp only [verbrauchLauf]
      intro hc; cases hc
  | n + 1, σ, ρ, hh => by
      simp only [verbrauchLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc]; intro he; cases he
      · rw [if_neg hc]
        obtain ⟨σr, w, b⟩ := sel (inv σ ρ).1 ρ
        cases b <;> cases w with
        | none => dsimp only; intro hc; cases hc
        | some v =>
            dsimp only
            obtain ⟨σm, m⟩ := massW σr ρ
            simp only
            cases hx : step σm (.cons v ρ) with
            | ok σ' ρ' =>
                dsimp only
                by_cases hfall : 0 ≤ (massW σ' ρ'.tail).2 ∧
                    (massW σ' ρ'.tail).2 ≤ bound ∧ (massW σ' ρ'.tail).2 < m
                · rw [if_pos hfall]
                  exact verbrauchKeinAbstieg t step inv sel massW bound hs n
                    (massW σ' ρ'.tail).1 ρ'.tail hh
                · rw [if_neg hfall]; intro hc; cases hc
            | next _ σ' ρ' =>
                dsimp only
                by_cases hfall : 0 ≤ (massW σ' ρ'.tail).2 ∧
                    (massW σ' ρ'.tail).2 ≤ bound ∧ (massW σ' ρ'.tail).2 < m
                · rw [if_pos hfall]
                  exact verbrauchKeinAbstieg t step inv sel massW bound hs n
                    (massW σ' ρ'.tail).1 ρ'.tail hh
                · rw [if_neg hfall]; intro hc; cases hc
            | leave _ σ' ρ' =>
                dsimp only
                by_cases hfall : 0 ≤ (massW σ' ρ'.tail).2 ∧
                    (massW σ' ρ'.tail).2 ≤ bound ∧ (massW σ' ρ'.tail).2 < m
                · rw [if_pos hfall]
                  split
                  · intro hc; cases hc
                  · intro hc; cases hc
                · rw [if_neg hfall]; intro hc; cases hc
            | zurueck _ _ => dsimp only; intro hc; cases hc
            | why _ _ => dsimp only; intro hc; cases hc
            | logik e => dsimp only; exact fun hc => hs _ _ hh (hx.trans (by cases hc; rfl))
            | hardware _ => dsimp only; intro hc; cases hc

/-- A `retry` run whose body and overflow never end in an `abstieg` never ends in one. -/
theorem retryKeinAbstieg {l : Bool} {Γ : Ctx}
    (step : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ (σ : World D) (ρ : Env D Γ) (hh : D.Fn),
      step σ ρ ≠ .logik (.abstieg hh))
    (hu : ∀ (σ : World D) (ρ : Env D Γ) (hh : D.Fn),
      ueberlauf σ ρ ≠ .logik (.abstieg hh)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (hh : D.Fn),
      retryLauf step bis ueberlauf n σ ρ ≠ .logik (.abstieg hh)
  | 0, σ, ρ, hh => by
      simp only [retryLauf]
      split
      · intro hc; cases hc
      · exact hu (bis σ ρ).1 ρ hh
  | n + 1, σ, ρ, hh => by
      simp only [retryLauf]
      by_cases hc : (bis σ ρ).2 = true
      · rw [if_pos hc]; intro he; cases he
      · rw [if_neg hc]
        cases hx : step (bis σ ρ).1 ρ with
        | ok σ' ρ' => dsimp only; exact retryKeinAbstieg step bis ueberlauf hs hu n σ' ρ' hh
        | next _ σ' ρ' => dsimp only; exact retryKeinAbstieg step bis ueberlauf hs hu n σ' ρ' hh
        | leave _ σ' ρ' => dsimp only; intro hc; cases hc
        | zurueck _ _ => dsimp only; intro hc; cases hc
        | why _ _ => dsimp only; intro hc; cases hc
        | logik e => dsimp only; exact fun hc => hs _ _ hh (hx.trans (by cases hc; rfl))
        | hardware _ => dsimp only; intro hc; cases hc

/-- A `forever` run whose body never ends in an `abstieg` never ends in one. -/
theorem foreverKeinAbstieg {l : Bool} {Γ : Ctx} (a : D.Annahme)
    (step : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ (σ : World D) (ρ : Env D Γ) (hh : D.Fn),
      step σ ρ ≠ .logik (.abstieg hh)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (hh : D.Fn),
      foreverLauf (l := l) a step inv n σ ρ ≠ .logik (.abstieg hh)
  | 0, σ, ρ, hh => by
      simp only [foreverLauf]
      intro hc; cases hc
  | n + 1, σ, ρ, hh => by
      simp only [foreverLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc]; intro he; cases he
      · rw [if_neg hc]
        cases hx : step (inv σ ρ).1 ρ with
        | ok σ' ρ' => dsimp only; exact foreverKeinAbstieg a step inv hs n σ' ρ' hh
        | next _ σ' ρ' => dsimp only; exact foreverKeinAbstieg a step inv hs n σ' ρ' hh
        | leave _ σ' ρ' => dsimp only; intro hc; cases hc
        | zurueck _ _ => dsimp only; intro hc; cases hc
        | why _ _ => dsimp only; intro hc; cases hc
        | logik e => dsimp only; exact fun hc => hs _ _ hh (hx.trans (by cases hc; rfl))
        | hardware _ => dsimp only; intro hc; cases hc

#print axioms Gabbro.Grammatik.traverseKeinAbstieg
#print axioms Gabbro.Grammatik.verbrauchKeinAbstieg
#print axioms Gabbro.Grammatik.retryKeinAbstieg
#print axioms Gabbro.Grammatik.foreverKeinAbstieg

end Gabbro.Grammatik
