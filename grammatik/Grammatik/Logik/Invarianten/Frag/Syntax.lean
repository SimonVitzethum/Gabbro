module

public import Mathlib.Data.Int.Basic

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

/-- Linear integer terms. Multiplication has a literal coefficient by construction.
    Variable names are generic: the source translator uses memory locations; QE may
    use natural numbers. No interpretation of a variable is hidden in the syntax. -/
inductive LTerm (α : Type) where
  | var (name : α)
  | konst (value : Int)
  | add (left right : LTerm α)
  | sub (left right : LTerm α)
  | scale (coefficient : Int) (term : LTerm α)
  deriving DecidableEq, Repr

/-- Presburger formulas. Quantifiers bind a named integer variable. Source-level
    bounded slot quantifiers are expanded by the translator; these integer binders
    are also available to the quantifier-elimination core. -/
inductive LProp (α : Type) where
  | tru
  | fls
  | le (left right : LTerm α)
  | lt (left right : LTerm α)
  | eq (left right : LTerm α)
  | not (body : LProp α)
  | and (left right : LProp α)
  | or (left right : LProp α)
  | imp (left right : LProp α)
  | ex (name : α) (body : LProp α)
  | all (name : α) (body : LProp α)
  | dvd (divisor : Int) (term : LTerm α)
  deriving DecidableEq, Repr

abbrev Assignment (α : Type) := α → Int

/-- Binding shadows only the named variable, including under nested binders. -/
def Assignment.bind [DecidableEq α] (values : Assignment α) (name : α)
    (value : Int) : Assignment α :=
  fun other => if other = name then value else values other

def LTerm.denote (values : Assignment α) : LTerm α → Int
  | .var name => values name
  | .konst value => value
  | .add left right => left.denote values + right.denote values
  | .sub left right => left.denote values - right.denote values
  | .scale coefficient term => coefficient * term.denote values

def LProp.denote [DecidableEq α] (values : Assignment α) : LProp α → Prop
  | .tru => True
  | .fls => False
  | .le left right => left.denote values ≤ right.denote values
  | .lt left right => left.denote values < right.denote values
  | .eq left right => left.denote values = right.denote values
  | .not body => ¬ body.denote values
  | .and left right => left.denote values ∧ right.denote values
  | .or left right => left.denote values ∨ right.denote values
  | .imp left right => left.denote values → right.denote values
  | .ex name body => ∃ value : Int, body.denote (values.bind name value)
  | .all name body => ∀ value : Int, body.denote (values.bind name value)
  | .dvd divisor term => divisor ∣ term.denote values

/-- Closed constant folding, also used to require a state-independent slot index. -/
def LTerm.constant? : LTerm α → Option Int
  | .var _ => none
  | .konst value => some value
  | .add left right => do return (← left.constant?) + (← right.constant?)
  | .sub left right => do return (← left.constant?) - (← right.constant?)
  | .scale coefficient term => do return coefficient * (← term.constant?)

theorem LTerm.constant?_sound {term : LTerm α} {value : Int}
    (h : term.constant? = some value) (values : Assignment α) :
    term.denote values = value := by
  induction term generalizing value with
  | var name => simp [LTerm.constant?] at h
  | konst n => cases h; rfl
  | add left right ihLeft ihRight =>
      cases hl : left.constant? <;> cases hr : right.constant? <;>
        simp [LTerm.constant?, hl, hr] at h
      subst value
      simp [LTerm.denote, ihLeft hl, ihRight hr]
  | sub left right ihLeft ihRight =>
      cases hl : left.constant? <;> cases hr : right.constant? <;>
        simp [LTerm.constant?, hl, hr] at h
      subst value
      simp [LTerm.denote, ihLeft hl, ihRight hr]
  | scale coefficient term ih =>
      cases ht : term.constant? <;> simp [LTerm.constant?, ht] at h
      subst value
      simp [LTerm.denote, ih ht]

end Gabbro.Grammatik.Invarianten.Frag
