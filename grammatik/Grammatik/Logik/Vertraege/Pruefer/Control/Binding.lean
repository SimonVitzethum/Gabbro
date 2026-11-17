module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Symbolic
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Relation

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

/-- Bounds and the initializer equation constrain a fresh immutable integer.
    Unsupported nonlinear initializers retain their proved type interval only. -/
def integerSelection {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (expression : Expr D Γ Λ (.int lo hi))
    (target : Env D Γ → Zahl lo hi → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : Except Frag.Refusal (Certificate (program := program) (S := S)
      (context.weaken (Nat.le_succ next))
      (fun valuation item runtime world => ∀ actual,
        symbols.Realizes valuation world actual → ∀ value,
        valuation next = value.n → target actual value item runtime world))) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual →
      target actual (eval world expression world actual) item runtime world)) := do
  let tail ← compile
  let bounds : Frag.LProp (Key D Nat) := .and
    (.le (.konst lo) (.var (.inr next))) (.le (.var (.inr next)) (.konst hi))
  let relation := evaluationRelation expression symbols (.var (.inr next))
  return {
    formula := .all (.inr next) (.imp (.and bounds relation.val) tail.formula)
    sound := fun valuation item present runtime world valid actual realized => by
      let value := eval world expression world actual
      let extended := valuation.bind next value.n
      have agree : ∀ key, key < next → valuation key = extended key := by
        intro key inside
        have different : key ≠ next := Nat.ne_of_lt inside
        simp only [extended, Frag.Assignment.bind, different, ↓reduceIte]
      have present' := (context.stable valuation extended item agree).mp present
      have realized' := (symbols.realizes_congr next bounded valuation extended agree world world actual).mp realized
      have fresh : values extended world (.inr next) = value.n := bind_same valuation next value.n
      have withinBounds : bounds.denote (values extended world) := by
        change lo ≤ values extended world (.inr next) ∧ values extended world (.inr next) ≤ hi
        rw [fresh]
        exact ⟨value.lo_le, value.le_hi⟩
      have defined : relation.val.denote (values extended world) :=
        relation.property extended world actual realized' fresh
      have ready := valid value.n
      rw [← values_bind] at ready
      exact tail.sound extended item present' runtime world (ready ⟨withinBounds, defined⟩)
        actual realized' value (bind_same valuation next value.n) }

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
