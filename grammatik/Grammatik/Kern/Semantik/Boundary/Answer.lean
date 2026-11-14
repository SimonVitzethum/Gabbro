module

public import Grammatik.Kern.Semantik.Boundary.Contract

@[expose] public section

namespace Gabbro.Grammatik.Boundary

variable {D : Deklaration}

/-- Omitting syntactically trivial checks preserves their truth. -/
theorem requiredB_sound (question answer : World D) (ρ : Env D Γ) :
    (e : Expr D Γ Λ .bool) → requiredB e = false → wahr? (eval question e answer ρ) = true
  | .tru, _ => rfl
  | .and left right, h => by
      simp only [requiredB, Bool.or_eq_false_iff] at h
      change (wahr? (eval question left answer ρ) &&
        wahr? (eval question right answer ρ)) = true
      rw [requiredB_sound question answer ρ left h.1,
        requiredB_sound question answer ρ right h.2]
      rfl
  | _, h => by cases h

/-- The shared value-or-reason gate. Only a decoded normal answer evaluates the
    predicate. An environment reason is forwarded unchanged; an invalid type or
    false predicate takes the declared failure reason. Without one the answer is
    unavailable, which admission must exclude for a required check. -/
def gate (check : α → Bool) (failure : Option β) : Option (α ⊕ β) → Option (α ⊕ β)
  | some (.inl v) => if check v then some (.inl v) else failure.map Sum.inr
  | some (.inr reason) => some (.inr reason)
  | none => failure.map Sum.inr

/-- Successful entry is evidence of the check, independent of any environment
    contract assumption. -/
theorem gate_success (check : α → Bool) (failure : Option β)
    (decoded : Option (α ⊕ β)) (v : α)
    (h : gate check failure decoded = some (.inl v)) :
    decoded = some (.inl v) ∧ check v = true := by
  cases decoded with
  | none => cases failure <;> cases h
  | some answer =>
      cases answer with
      | inr reason => cases h
      | inl value =>
          cases hc : check value with
          | false =>
              simp only [gate, hc, Bool.false_eq_true, ↓reduceIte] at h
              cases failure <;> cases h
          | true =>
              simp only [gate, hc, ↓reduceIte, Option.some.injEq, Sum.inl.injEq] at h
              subst value
              exact ⟨rfl, hc⟩

/-- A failed predicate is an ordinary reason, using precisely the declared code. -/
theorem gate_failed (check : α → Bool) (failure : β) (v : α)
    (h : check v = false) :
    gate check (some failure) (some (.inl v)) = some (.inr failure) := by
  simp only [gate, h, Bool.false_eq_true, ↓reduceIte, Option.map_some]

/-- A supplied environment reason bypasses the normal-result postcondition. -/
theorem gate_reason (check : α → Bool) (failure : Option β) (reason : β) :
    gate check failure (some (.inr reason)) = some (.inr reason) := rfl

/-- An invalid representation follows the same declared error path. -/
theorem gate_invalid (check : α → Bool) (failure : β) :
    gate check (some failure) none = some (.inr failure) := rfl

/-- Evaluate a syntactically admitted postcondition in the answer context. -/
def Check.answer (c : Check D (ErgCtx Γ e) [])
    (question answer : World D) (ρ : Env D Γ) (v : ErgVal D e) : Bool :=
  wahr? (eval question c.expression answer (ergEnv e v ρ))

/-- An infallible answer has no reason continuation. Admission permits a required
    check only on the fallible form; this function still specifies the refused
    form's behavior without manufacturing a stop kind. -/
def Check.value (c : Check D (ErgCtx Γ e) [])
    (question answer : World D) (ρ : Env D Γ) : Option (ErgVal D e) → Option (ErgVal D e)
  | none => none
  | some v => if c.answer question answer ρ v then some v else none

end Gabbro.Grammatik.Boundary
