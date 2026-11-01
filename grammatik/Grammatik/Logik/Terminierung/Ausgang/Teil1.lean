module

public import Grammatik.Logik.Terminierung.Klasse

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Outcomes without an exit -/

/-- The outcome is no exit: no return, no reason, and no `leave` where the innermost loop is the one asked about
    (`eb`). -/
def OhneAus {l : Bool} {Γ : Ctx} (eb : Bool) : Ausgang V l Γ → Prop
  | .zurueck .. => False
  | .why .. => False
  | .leave .. => eb = false
  | _ => True

/-- The same for an end outcome. -/
def EndOhneAus {l : Bool} {Γ : Ctx} (eb : Bool) : EndAusgang V l Γ → Prop
  | .zurueck .. => False
  | .why .. => False
  | .leave .. => eb = false
  | _ => True

theorem ohneAus_schrumpf {l : Bool} {Γ : Ctx} {τ : Ty} {eb : Bool} :
    ∀ {a : Ausgang V l (τ :: Γ)}, OhneAus eb a → OhneAus eb a.schrumpf
  | .ok .., h | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

theorem ohneAus_schrumpfArm {l : Bool} {Γ : Ctx} {eb : Bool} :
    ∀ (c : Option (Int × Int)) {a : Ausgang V l (ArmCtx Γ c)}, OhneAus eb a → OhneAus eb (a.schrumpfArm c)
  | Option.none, _, h => h
  | Option.some (_, _), _, h => ohneAus_schrumpf h

theorem ohneAus_mapWelt {l : Bool} {Γ : Ctx} {eb : Bool} (f : World D → World D) :
    ∀ {a : Ausgang V l Γ}, OhneAus eb a → OhneAus eb (a.mapWelt f)
  | .ok .., h | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

theorem endOhneAus_schrumpf {l : Bool} {Γ : Ctx} {τ : Ty} {eb : Bool} :
    ∀ {a : EndAusgang V l (τ :: Γ)}, EndOhneAus eb a → EndOhneAus eb a.schrumpf
  | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

theorem endOhneAus_zuAusgang {l : Bool} {Γ : Ctx} {eb : Bool} :
    ∀ {a : EndAusgang V l Γ}, EndOhneAus eb a → OhneAus eb a.zuAusgang
  | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

/-! ## 2. The loops -/

section Schleifen

variable {l : Bool} {Γ : Ctx}

/-- **A `forever` loop completes only through a pass that leaves.** -/
theorem foreverLauf_ok (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ),
      foreverLauf (l := l) a schritt inv n σ ρ = .ok σ' ρ' →
      ∃ σ1 ρ1, ∃ h : true = true, schritt σ1 ρ1 = .leave h σ' ρ'
  | 0, _, _, _, _, h => by simp only [foreverLauf, reduceCtorEq] at h
  | n + 1, σ, ρ, σ', ρ', h => by
      unfold foreverLauf at h
      split at h
      · cases h
      · split at h
        · exact foreverLauf_ok a schritt inv n _ _ σ' ρ' h
        · exact foreverLauf_ok a schritt inv n _ _ σ' ρ' h
        · rename_i hh σ2 ρ2 he
          cases h
          exact ⟨_, _, hh, he⟩
        all_goals cases h

/-- **A `forever` loop returns only through a pass that returns.** -/
theorem foreverLauf_zurueck (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (σ' : World D) (v : ErgVal D V.erg),
      foreverLauf (l := l) a schritt inv n σ ρ = .zurueck σ' v → ∃ σ1 ρ1, schritt σ1 ρ1 = .zurueck σ' v
  | 0, _, _, _, _, h => by simp only [foreverLauf, reduceCtorEq] at h
  | n + 1, σ, ρ, σ', v, h => by
      unfold foreverLauf at h
      split at h
      · cases h
      · split at h
        · exact foreverLauf_zurueck a schritt inv n _ _ σ' v h
        · exact foreverLauf_zurueck a schritt inv n _ _ σ' v h
        · cases h
        · rename_i σ2 v2 he
          cases h
          exact ⟨_, _, he⟩
        all_goals cases h

/-- **A `forever` loop ends with a reason only through a pass that does.** -/
theorem foreverLauf_why (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (σ' : World D) (r : Fin V.gruende),
      foreverLauf (l := l) a schritt inv n σ ρ = .why σ' r → ∃ σ1 ρ1, schritt σ1 ρ1 = .why σ' r
  | 0, _, _, _, _, h => by simp only [foreverLauf, reduceCtorEq] at h
  | n + 1, σ, ρ, σ', r, h => by
      unfold foreverLauf at h
      split at h
      · cases h
      · split at h
        · exact foreverLauf_why a schritt inv n _ _ σ' r h
        · exact foreverLauf_why a schritt inv n _ _ σ' r h
        · cases h
        · cases h
        · rename_i σ2 r2 he
          cases h
          exact ⟨_, _, he⟩
        all_goals cases h

/-- **A loop without an exit ends only at a logic or hardware stop**: when every pass is free of `leave`, return and
    reason, the loop's outcome is a logic stop or a hardware stop -- at its `progress` assumption when the passes
    are spent. -/
theorem foreverLauf_nur_umwelt (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) (hs : ∀ σ ρ, OhneAus true (schritt σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      (∃ e, foreverLauf (l := l) a schritt inv n σ ρ = .logik e) ∨
        ∃ e, foreverLauf (l := l) a schritt inv n σ ρ = .hardware e
  | 0, _, _ => Or.inr ⟨_, rfl⟩
  | n + 1, σ, ρ => by
      unfold foreverLauf
      split
      · exact Or.inl ⟨_, rfl⟩
      · have h := hs (inv σ ρ).1 ρ
        split
        · exact foreverLauf_nur_umwelt a schritt inv hs n _ _
        · exact foreverLauf_nur_umwelt a schritt inv hs n _ _
        · rename_i he; rw [he] at h; exact absurd h (by simp only [OhneAus, Bool.true_eq_false, not_false_eq_true])
        · rename_i he; rw [he] at h; exact absurd h (by simp only [OhneAus, not_false_eq_true])
        · rename_i he; rw [he] at h; exact absurd h (by simp only [OhneAus, not_false_eq_true])
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inr ⟨_, rfl⟩

theorem ohneAus_forever {eb : Bool} (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) (hs : ∀ σ ρ, OhneAus true (schritt σ ρ)) (n : Nat)
    (σ : World D) (ρ : Env D Γ) : OhneAus eb (foreverLauf (l := l) a schritt inv n σ ρ) := by
  rcases foreverLauf_nur_umwelt a schritt inv hs n σ ρ with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [he] <;> trivial

theorem ohneAus_traverse {τ : Ty} {eb : Bool} (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (hs : ∀ σ ρ, OhneAus false (schritt σ ρ)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), OhneAus eb (traverseLauf (l := l) schritt inv ks σ ρ)
  | [], σ, ρ => by unfold traverseLauf; split <;> trivial
  | k :: ks, σ, ρ => by
      unfold traverseLauf
      split
      · trivial
      · have h := hs (inv σ ρ).1 (.cons k ρ)
        split
        · exact ohneAus_traverse schritt inv hs ks _ _
        · exact ohneAus_traverse schritt inv hs ks _ _
        · split <;> trivial
        · rename_i he; rw [he] at h; exact absurd h (by simp only [OhneAus, not_false_eq_true])
        · rename_i he; rw [he] at h; exact absurd h (by simp only [OhneAus, not_false_eq_true])
        · trivial
        · trivial

theorem ohneAus_retry {eb : Bool} (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueber : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, OhneAus false (schritt σ ρ)) (hu : ∀ σ ρ, OhneAus eb (ueber σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), OhneAus eb (retryLauf schritt bis ueber n σ ρ)
  | 0, σ, ρ => by unfold retryLauf; split; trivial; exact hu _ _
  | n + 1, σ, ρ => by
      unfold retryLauf
      split
      · trivial
      · have h := hs (bis σ ρ).1 ρ
        split
        · exact ohneAus_retry schritt bis ueber hs hu n _ _
        · exact ohneAus_retry schritt bis ueber hs hu n _ _
        · trivial
        · rename_i he; rw [he] at h; exact absurd h (by simp only [OhneAus, not_false_eq_true])
        · rename_i he; rw [he] at h; exact absurd h (by simp only [OhneAus, not_false_eq_true])
        · trivial
        · trivial

end Schleifen

/-! ## 3. Syntax to semantics: a statement without an exit yields none -/

theorem befund_und_austritt (a b : Befund D) : (a ++ b).austritt = (a.austritt || b.austritt) := by rfl

section Semantik

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

set_option hygiene false in
/-- Split a finding `a ++ b` with no exit into its parts. -/
macro "teile" : tactic => `(tactic| (simp only [befS, befB, befE, befArms, befGArms, befund_und_austritt,
  Bool.or_eq_false_iff] at h))

end Semantik
end Gabbro.Grammatik
