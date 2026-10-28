import Grammatik.Bausteine.Arena.Ownership.Source.Arguments

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

inductive Modes : Ctx → Type where
  | nil : Modes []
  | cons {τ : Ty} {rest : Ctx} (mode : Option PassingMode) (modes : Modes rest) : Modes (τ :: rest)

/-- Argument admission reserves loans and consumes owners in one traversal.
The reservation set prevents a later owning argument from taking a loaned
origin, independently of argument order. -/
structure ArgumentFlow where
  remaining : Context
  loans : List Nat := []

def passArgument {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (flow : ArgumentFlow) (mode : Option PassingMode) (e : Expr D Γ Λ τ) : Option ArgumentFlow :=
  match mode with
  | none => some flow
  | some .owned => do
    let (c, i) ← consume flow.remaining e
    if i ∈ flow.loans then none else some ⟨c, flow.loans⟩
  | some .borrowed => do
    let i ← origin flow.remaining e
    if (flow.remaining.rights i).isSome then some ⟨flow.remaining, i :: flow.loans⟩ else none

def checkArgumentFlow (A : FreiForm D) {Γ : Ctx} {Λ : List (Res D)} {params : Ctx}
    (flow : ArgumentFlow) (args : Args D Γ Λ params) (modes : Modes params) : Option ArgumentFlow :=
  match args, modes with
  | .nil, .nil => some flow
  | .cons e rest, .cons mode modes => do
    if checkExpression A flow.remaining e then
      let next ← passArgument flow mode e
      checkArgumentFlow A next rest modes
    else none

theorem passArgument_owned {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {flow next : ArgumentFlow} {e : Expr D Γ Λ τ}
    (hp : passArgument flow (some .owned) e = some next) :
    ∃ i, origin flow.remaining e = some i ∧ flow.remaining.rights i = some .owned ∧
      i ∉ flow.loans ∧ next.remaining = flow.remaining.kill i ∧ next.loans = flow.loans := by
  unfold passArgument at hp
  cases hc : consume flow.remaining e with
  | none => simp only [hc, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hp
  | some pair =>
    obtain ⟨c, i⟩ := pair
    rw [hc] at hp
    change (if i ∈ flow.loans then none else some (ArgumentFlow.mk c flow.loans)) = some next at hp
    split at hp
    · cases hp
    · rename_i hn
      cases hp
      obtain ⟨ho, hr, he⟩ := consume_facts hc
      exact ⟨i, ho, hr, hn, he, rfl⟩

theorem consumed_argument_cannot_repeat {Γ : Ctx} {Λ : List (Res D)} {τ υ : Ty}
    {flow next : ArgumentFlow} {first : Expr D Γ Λ τ} {second : Expr D Γ Λ υ} {i : Nat}
    (hp : passArgument flow (some .owned) first = some next)
    (hf : origin flow.remaining first = some i) (hs : origin flow.remaining second = some i) :
    passArgument next (some .owned) second = none ∧
      passArgument next (some .borrowed) second = none := by
  obtain ⟨j, hj, _, _, he, _⟩ := passArgument_owned hp
  have hid : j = i := Option.some.inj (hj.symm.trans hf)
  subst j
  have ho : origin next.remaining second = some i := by rw [he]; exact hs
  have hr : next.remaining.rights i = none := by rw [he]; exact Context.kill_at _ _
  simp only [passArgument, consume, ho, Option.bind_eq_bind, Option.bind_some, hr, reduceCtorEq, ↓reduceIte,
  Option.bind_none, Option.isSome_none, Bool.false_eq_true, and_self]

theorem loan_reservation_blocks_consumption {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (flow : ArgumentFlow) (e : Expr D Γ Λ τ) (i : Nat)
    (hi : origin flow.remaining e = some i) (hr : flow.remaining.rights i = some .owned)
    (loaned : i ∈ flow.loans) : passArgument flow (some .owned) e = none := by
  simp only [passArgument, consume, hi, Option.bind_eq_bind, Option.bind_some, hr, ↓reduceIte, loaned]

#print axioms consumed_argument_cannot_repeat
#print axioms loan_reservation_blocks_consumption

end Gabbro.Grammatik.ArenaOwnership.Source
