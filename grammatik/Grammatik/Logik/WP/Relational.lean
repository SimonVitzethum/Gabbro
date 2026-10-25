import Grammatik.Logik.WP.Regeln3

/-!
# GabbroV over machine G: relational logic (two runs)

Properties of two runs at once -- determinism under different oracle answers, noninterference, invariance under a
renaming -- are relations between their outcomes. The relational weakest precondition is exact as well:
`wp2B b₁ b₂ Q σ₁ ρ₁ σ₂ ρ₂ ↔ Q (run b₁) (run b₂)`. The rules below let a proof walk two programs in lockstep:

* `wp2B_cons`: two sequences, statement against statement;
* `wp2S_ite`: two branches on conditions that agree (the usual low-guard rule);
* `traverse2_regel`: two `traverse` loops over the same indices with a RELATIONAL invariant;
* `wp2_selbst`: a run against itself is its own outcome twice (the diagonal).

The two runs may use different oracles, budgets and call meanings: that is how determinism and oracle independence
are stated.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Relational

variable (O₁ O₂ : Orakel D) (p₁ p₂ : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- The relational weakest precondition of two statements. -/
def wp2S {Λ₁ Λ₁' Λ₂ Λ₂' : List (Res D)} (s₁ : Stmt D V l Γ Λ₁ Λ₁') (s₂ : Stmt D V l Γ Λ₂ Λ₂')
    (Q : Ausgang V l Γ → Ausgang V l Γ → Prop) (σ₁ : World D) (ρ₁ : Env D Γ) (σ₂ : World D) (ρ₂ : Env D Γ) : Prop :=
  Q (execStmt O₁ p₁ R₁ s₁ σ₁ ρ₁) (execStmt O₂ p₂ R₂ s₂ σ₂ ρ₂)

/-- The relational weakest precondition of two blocks. -/
def wp2B {Λ₁ Λ₁' Λ₂ Λ₂' : List (Res D)} (b₁ : Block D V l Γ Λ₁ Λ₁') (b₂ : Block D V l Γ Λ₂ Λ₂')
    (Q : Ausgang V l Γ → Ausgang V l Γ → Prop) (σ₁ : World D) (ρ₁ : Env D Γ) (σ₂ : World D) (ρ₂ : Env D Γ) : Prop :=
  Q (execBlock O₁ p₁ R₁ b₁ σ₁ ρ₁) (execBlock O₂ p₂ R₂ b₂ σ₂ ρ₂)

/-- **Exactness of the relational calculus.** -/
theorem wp2B_exakt {Λ₁ Λ₁' Λ₂ Λ₂' : List (Res D)} (b₁ : Block D V l Γ Λ₁ Λ₁') (b₂ : Block D V l Γ Λ₂ Λ₂')
    (Q : Ausgang V l Γ → Ausgang V l Γ → Prop) (σ₁ : World D) (ρ₁ : Env D Γ) (σ₂ : World D) (ρ₂ : Env D Γ) :
    wp2B O₁ O₂ p₁ p₂ R₁ R₂ b₁ b₂ Q σ₁ ρ₁ σ₂ ρ₂ ↔
      Q (execBlock O₁ p₁ R₁ b₁ σ₁ ρ₁) (execBlock O₂ p₂ R₂ b₂ σ₂ ρ₂) := Iff.rfl

/-- What two statements owe in front of the rests of their blocks: both continue normally into the rests, or the
    outcomes as they are meet `Q` (a rest that does not run is a run that ended). -/
def weiter2B {Λ₁' Λ₁'' Λ₂' Λ₂'' : List (Res D)} (rest₁ : Block D V l Γ Λ₁' Λ₁'') (rest₂ : Block D V l Γ Λ₂' Λ₂'')
    (Q : Ausgang V l Γ → Ausgang V l Γ → Prop) : Ausgang V l Γ → Ausgang V l Γ → Prop
  | .ok σ₁ ρ₁, .ok σ₂ ρ₂ => wp2B O₁ O₂ p₁ p₂ R₁ R₂ rest₁ rest₂ Q σ₁ ρ₁ σ₂ ρ₂
  | .ok σ₁ ρ₁, o₂ => Q (execBlock O₁ p₁ R₁ rest₁ σ₁ ρ₁) o₂
  | o₁, .ok σ₂ ρ₂ => Q o₁ (execBlock O₂ p₂ R₂ rest₂ σ₂ ρ₂)
  | o₁, o₂ => Q o₁ o₂

/-- **Two sequences in lockstep.** -/
theorem wp2B_cons {Λ₁ Λ₁' Λ₁'' Λ₂ Λ₂' Λ₂'' : List (Res D)} (s₁ : Stmt D V l Γ Λ₁ Λ₁') (rest₁ : Block D V l Γ Λ₁' Λ₁'')
    (s₂ : Stmt D V l Γ Λ₂ Λ₂') (rest₂ : Block D V l Γ Λ₂' Λ₂'') (Q : Ausgang V l Γ → Ausgang V l Γ → Prop)
    (σ₁ : World D) (ρ₁ : Env D Γ) (σ₂ : World D) (ρ₂ : Env D Γ) :
    wp2B O₁ O₂ p₁ p₂ R₁ R₂ (.cons s₁ rest₁) (.cons s₂ rest₂) Q σ₁ ρ₁ σ₂ ρ₂ ↔
      wp2S O₁ O₂ p₁ p₂ R₁ R₂ s₁ s₂ (weiter2B O₁ O₂ p₁ p₂ R₁ R₂ rest₁ rest₂ Q) σ₁ ρ₁ σ₂ ρ₂ := by
  unfold wp2B wp2S
  simp only [execBlock]
  cases execStmt O₁ p₁ R₁ s₁ σ₁ ρ₁ <;> cases execStmt O₂ p₂ R₂ s₂ σ₂ ρ₂ <;> rfl

/-- **Two branches on agreeing conditions** (the low-guard rule): if the two conditions agree, each run takes the
    branch of the same side. -/
theorem wp2S_ite {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (Q : Ausgang V l Γ → Ausgang V l Γ → Prop) (σ₁ : World D) (ρ₁ : Env D Γ) (σ₂ : World D) (ρ₂ : Env D Γ)
    (hgleich : wahr? (eval (σ₁.lese Λ c.orte) c (σ₁.lese Λ c.orte) ρ₁) =
      wahr? (eval (σ₂.lese Λ c.orte) c (σ₂.lese Λ c.orte) ρ₂))
    (hdann : wahr? (eval (σ₁.lese Λ c.orte) c (σ₁.lese Λ c.orte) ρ₁) = true →
      wp2B O₁ O₂ p₁ p₂ R₁ R₂ t t Q (σ₁.lese Λ c.orte) ρ₁ (σ₂.lese Λ c.orte) ρ₂)
    (hsonst : wahr? (eval (σ₁.lese Λ c.orte) c (σ₁.lese Λ c.orte) ρ₁) = false →
      wp2B O₁ O₂ p₁ p₂ R₁ R₂ e e Q (σ₁.lese Λ c.orte) ρ₁ (σ₂.lese Λ c.orte) ρ₂) :
    wp2S O₁ O₂ p₁ p₂ R₁ R₂ (.ite c t e) (.ite c t e) Q σ₁ ρ₁ σ₂ ρ₂ := by
  unfold wp2S
  simp only [execStmt]
  rw [← hgleich]
  cases h : wahr? (eval (σ₁.lese Λ c.orte) c (σ₁.lese Λ c.orte) ρ₁)
  · simpa [wp2B] using hsonst h
  · simpa [wp2B] using hdann h

/-- What two passes of two `traverse` loops owe a relational invariant over the same rest of indices. -/
def TraverseSchritt2 {τ : Ty} (I : List (Wert D τ) → World D → Env D Γ → World D → Env D Γ → Prop)
    (ks : List (Wert D τ)) :
    Ausgang V true (τ :: Γ) → Ausgang V true (τ :: Γ) → Prop
  | .ok σ₁ ρ₁, .ok σ₂ ρ₂ => I ks σ₁ ρ₁.tail σ₂ ρ₂.tail
  | .next _ σ₁ ρ₁, .next _ σ₂ ρ₂ => I ks σ₁ ρ₁.tail σ₂ ρ₂.tail
  | .ok σ₁ ρ₁, .next _ σ₂ ρ₂ => I ks σ₁ ρ₁.tail σ₂ ρ₂.tail
  | .next _ σ₁ ρ₁, .ok σ₂ ρ₂ => I ks σ₁ ρ₁.tail σ₂ ρ₂.tail
  | _, _ => False

/-- **Two `traverse` loops over the same indices, in lockstep.** A relational invariant `I` over the rest of the
    indices; both loop checks agree under it; at the end of the indices both ends meet `Q`; every pair of passes from
    the invariant continues both loops normally into it. (A pass that leaves, returns or stops on one side only is
    excluded by `TraverseSchritt2`: the lockstep rule is for loops that run to the end; others go through the exact
    calculus.) -/
theorem traverse2_regel {τ : Ty} (s₁ s₂ : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv₁ inv₂ : World D → Env D Γ → World D × Bool) (Q : Ausgang V l Γ → Ausgang V l Γ → Prop)
    (I : List (Wert D τ) → World D → Env D Γ → World D → Env D Γ → Prop)
    (hEnde : ∀ σ₁ ρ₁ σ₂ ρ₂, I [] σ₁ ρ₁ σ₂ ρ₂ →
      Q (if (inv₁ σ₁ ρ₁).2 = true then .ok (inv₁ σ₁ ρ₁).1 ρ₁ else .logik .schleife)
        (if (inv₂ σ₂ ρ₂).2 = true then .ok (inv₂ σ₂ ρ₂).1 ρ₂ else .logik .schleife))
    (hInv : ∀ k ks σ₁ ρ₁ σ₂ ρ₂, I (k :: ks) σ₁ ρ₁ σ₂ ρ₂ → (inv₁ σ₁ ρ₁).2 = true ∧ (inv₂ σ₂ ρ₂).2 = true)
    (hSchritt : ∀ k ks σ₁ ρ₁ σ₂ ρ₂, I (k :: ks) σ₁ ρ₁ σ₂ ρ₂ →
      TraverseSchritt2 I ks (s₁ (inv₁ σ₁ ρ₁).1 (.cons k ρ₁)) (s₂ (inv₂ σ₂ ρ₂).1 (.cons k ρ₂))) :
    ∀ ks σ₁ ρ₁ σ₂ ρ₂, I ks σ₁ ρ₁ σ₂ ρ₂ →
      Q (traverseLauf s₁ inv₁ ks σ₁ ρ₁) (traverseLauf s₂ inv₂ ks σ₂ ρ₂) := by
  intro ks
  induction ks with
  | nil => intro σ₁ ρ₁ σ₂ ρ₂ h; exact hEnde σ₁ ρ₁ σ₂ ρ₂ h
  | cons k ks ih =>
    intro σ₁ ρ₁ σ₂ ρ₂ h
    obtain ⟨h₁, h₂⟩ := hInv k ks σ₁ ρ₁ σ₂ ρ₂ h
    have hs := hSchritt k ks σ₁ ρ₁ σ₂ ρ₂ h
    unfold traverseLauf
    rw [if_neg (by simp [h₁]), if_neg (by simp [h₂])]
    revert hs
    cases s₁ (inv₁ σ₁ ρ₁).1 (.cons k ρ₁) <;> cases s₂ (inv₂ σ₂ ρ₂).1 (.cons k ρ₂) <;>
      first
      | exact fun hs => ih _ _ _ _ hs
      | exact fun hs => hs.elim

/-- **The diagonal**: a run related to itself (same oracle, budget, call meaning) is its own outcome twice -- the
    relational calculus restricts to the unary one. -/
theorem wp2_selbst {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) :
    wp2B O₁ O₁ p₁ p₁ R₁ R₁ b b (fun o₁ o₂ => o₁ = o₂ ∧ Q o₁) σ ρ σ ρ ↔ wpB O₁ p₁ R₁ b Q σ ρ := by
  unfold wp2B wpB
  simp

end Relational

end Gabbro.Grammatik.WP
