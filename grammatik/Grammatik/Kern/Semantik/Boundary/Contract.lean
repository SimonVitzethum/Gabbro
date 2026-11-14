module

public import Grammatik.Kern.Syntax.Boundary.Contract
public import Grammatik.Kern.Semantik.Semantik.T1.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Boundary

variable {D : Deklaration}

/-- Interpretation of named R3 clauses, per contract. No expression or compiler
    fact is obtained from a name. The question world is the `old` world. -/
abbrev Remainders (D : Deklaration) (Γ : Ctx) :=
  String → World D → World D → Env D Γ → Bool

/-- The checked projection is evaluated over the post world and original
    arguments plus answer; `old` reads the question world. -/
def Parts.Q_check (p : Parts D Γ Λ) (question answer : World D) (ρ : Env D Γ) : Bool :=
  wahr? (eval question p.checked.expression answer ρ)

/-- The uncheckable projection consists exactly of the explicitly named R3
    clauses; a fully executable contract contributes the literal true remainder. -/
def Parts.Q_rest (p : Parts D Γ Λ) (R : Remainders D Γ)
    (question answer : World D) (ρ : Env D Γ) : Bool :=
  p.remainder.all fun name => R name question answer ρ

/-- Meaning of the entire written contract, before splitting. A refused clause
    has no admitted execution; its value is irrelevant to `split_correct`. -/
def Contract.denote (R : Remainders D Γ) (question answer : World D) (ρ : Env D Γ) :
    Contract D Γ Λ → Bool
  | .predicate e => wahr? (eval question e answer ρ)
  | .deviceInternal name => R name question answer ρ
  | .conjunction left right => left.denote R question answer ρ && right.denote R question answer ρ
  | .refused _ => false

/-- A computed split loses no clause. In particular, an unsupported expression
    cannot be treated as a true check or silently become an assumption. -/
theorem Contract.split_correct (c : Contract D Γ Λ) (p : Parts D Γ Λ)
    (h : c.split = .ok p) (R : Remainders D Γ)
    (question answer : World D) (ρ : Env D Γ) :
    c.denote R question answer ρ =
      (p.Q_check question answer ρ && p.Q_rest R question answer ρ) := by
  induction c generalizing p with
  | predicate e =>
      cases he : fragmentB e with
      | false => simp [Contract.split, he] at h
      | true =>
          simp only [Contract.split, he, ↓reduceDIte] at h
          have hp := Except.ok.inj h
          cases hp
          exact (Bool.and_true _).symm
  | deviceInternal name =>
      cases h
      simp only [Contract.denote, Parts.Q_check, Parts.Q_rest, Check.trivial,
        eval, wahr?, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  | conjunction left right ihLeft ihRight =>
      cases hl : left.split with
      | error reason => simp [Contract.split, hl] at h
      | ok pl =>
          cases hr : right.split with
          | error reason => simp [Contract.split, hl, hr] at h
          | ok pr =>
              simp only [Contract.split, hl, hr] at h
              have hp := Except.ok.inj h
              cases hp
              rw [Contract.denote, ihLeft pl hl, ihRight pr hr]
              simp only [Parts.Q_check, Parts.Q_rest, eval, List.all_append]
              cases wahr? (eval question pl.checked.expression answer ρ) <;>
                cases wahr? (eval question pr.checked.expression answer ρ) <;>
                cases pl.remainder.all (fun name => R name question answer ρ) <;>
                cases pr.remainder.all (fun name => R name question answer ρ) <;> rfl
  | refused reason => cases h

/-- Accepted values satisfy the full contract once its named remainder holds.
    The checked premise is a branch fact, rather than an environment promise. -/
theorem Contract.of_checked_and_rest (c : Contract D Γ Λ) (p : Parts D Γ Λ)
    (h : c.split = .ok p) (R : Remainders D Γ)
    (question answer : World D) (ρ : Env D Γ)
    (hc : p.Q_check question answer ρ = true)
    (hr : p.Q_rest R question answer ρ = true) :
    c.denote R question answer ρ = true := by
  rw [c.split_correct p h R question answer ρ, hc, hr]
  rfl

end Gabbro.Grammatik.Boundary
