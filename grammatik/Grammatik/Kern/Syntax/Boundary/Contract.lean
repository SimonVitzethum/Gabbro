module

public import Grammatik.Kern.Syntax.Boundary.Fragment
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm

@[expose] public section

namespace Gabbro.Grammatik.Boundary

variable {D : Deklaration}

/-- An environment postcondition separates observable expression syntax from a
    named predicate about unobservable device internals (R3). The latter has no
    expression the compiler could evaluate or use for optimization. Conjunction
    is the only composition across that boundary: moving a remainder through
    negation or disjunction would not preserve `Q = Q_check && Q_rest`. -/
inductive Contract (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) where
  | predicate (expression : Expr D Γ Λ .bool)
  | deviceInternal (name : String)
  | conjunction (left right : Contract D Γ Λ)
  | refused (reason : Refusal)

/-- Computed projections of an admitted contract. Every remainder name is
    retained in source order, including repeated occurrences. -/
structure Parts (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) where
  checked : Check D Γ Λ
  remainder : List String

/-- Compute the split, or refuse the declaration. Unsupported expression syntax
    never migrates into the named remainder. -/
def Contract.split : Contract D Γ Λ → Except Refusal (Parts D Γ Λ)
  | .predicate e =>
      if h : fragmentB e = true then
        .ok {
          checked := {
            expression := e
            admitted := h
          }
          remainder := []
        }
      else .error .unbounded
  | .deviceInternal name => .ok {
      checked := .trivial
      remainder := [name]
    }
  | .conjunction left right =>
      match left.split with
      | .error reason => .error reason
      | .ok p =>
          match right.split with
          | .error reason => .error reason
          | .ok q => .ok {
              checked := {
                expression := .and p.checked.expression q.checked.expression
                admitted := by
                  change fragmentB p.checked.expression && fragmentB q.checked.expression = true
                  rw [p.checked.admitted, q.checked.admitted]
                  rfl
              }
              remainder := p.remainder ++ q.remainder
            }
  | .refused reason => .error reason

/-- R1/R4/R5/R6 are definite refusals, including inside conjunctions. -/
theorem Contract.refused_split (reason : Refusal) :
    (Contract.refused (D := D) (Γ := Γ) (Λ := Λ) reason).split = .error reason := rfl

/-- Refusal of the left clause cannot be hidden by another conjunct. -/
theorem Contract.conjunction_refused_left (left right : Contract D Γ Λ)
    (reason : Refusal) (h : left.split = .error reason) :
    (Contract.conjunction left right).split = .error reason := by
  simp only [Contract.split, h]

end Gabbro.Grammatik.Boundary

namespace Gabbro.Grammatik

/-- The observable postcondition of the canonical call contract supplies the
    entry check. Splitting inspects its syntax, including nested finite bounds;
    no arbitrary `AxEns` function is guessed to be executable. -/
def CallContract.entryParts {D : Deklaration}
    {S : Signatur D.Tab D.Glob D.Lock D.Marke} (c : CallContract D S) :
    Except Boundary.Refusal (Boundary.Parts D (ErgCtx S.params S.erg)
      (Vertrag.vonSig D S).ende) :=
  (Boundary.Contract.predicate c.post).split

end Gabbro.Grammatik
