module

public import Grammatik.Logik.Invarianten.Frag.Syntax
import Mathlib.Tactic.Tauto

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

/-- Push negation to atoms and eliminate implication. Integer quantifiers remain
    explicit; in negative position their polarity changes. -/
def LProp.nnf (negative : Bool) : LProp α → LProp α
  | .tru => if negative then .fls else .tru
  | .fls => if negative then .tru else .fls
  | .le a b => if negative then .not (.le a b) else .le a b
  | .lt a b => if negative then .not (.lt a b) else .lt a b
  | .eq a b => if negative then .not (.eq a b) else .eq a b
  | .dvd k t => if negative then .not (.dvd k t) else .dvd k t
  | .not body => body.nnf (!negative)
  | .and left right =>
      if negative then .or (left.nnf true) (right.nnf true)
      else .and (left.nnf false) (right.nnf false)
  | .or left right =>
      if negative then .and (left.nnf true) (right.nnf true)
      else .or (left.nnf false) (right.nnf false)
  | .imp left right =>
      if negative then .and (left.nnf false) (right.nnf true)
      else .or (left.nnf true) (right.nnf false)
  | .ex name body =>
      if negative then .all name (body.nnf true) else .ex name (body.nnf false)
  | .all name body =>
      if negative then .ex name (body.nnf true) else .all name (body.nnf false)

theorem LProp.nnf_denote [DecidableEq α] (formula : LProp α)
    (negative : Bool) (values : Assignment α) :
    (formula.nnf negative).denote values ↔
      if negative then ¬ formula.denote values else formula.denote values := by
  classical
  induction formula generalizing negative values <;> cases negative <;>
    simp_all [LProp.nnf, LProp.denote] <;> tauto

theorem LProp.negation_denote [DecidableEq α] (formula : LProp α)
    (values : Assignment α) :
    (formula.nnf true).denote values ↔ ¬ formula.denote values :=
  formula.nnf_denote true values

/-- All arithmetic atoms compare a difference against zero. -/
def LProp.zeroForm : LProp α → LProp α
  | .tru => .tru
  | .fls => .fls
  | .le a b => .le (.sub a b) (.konst 0)
  | .lt a b => .lt (.sub a b) (.konst 0)
  | .eq a b => .eq (.sub a b) (.konst 0)
  | .dvd k t => .dvd k t
  | .not body => .not body.zeroForm
  | .and left right => .and left.zeroForm right.zeroForm
  | .or left right => .or left.zeroForm right.zeroForm
  | .imp left right => .imp left.zeroForm right.zeroForm
  | .ex name body => .ex name body.zeroForm
  | .all name body => .all name body.zeroForm

theorem LProp.zeroForm_denote [DecidableEq α] (formula : LProp α)
    (values : Assignment α) :
    formula.zeroForm.denote values ↔ formula.denote values := by
  induction formula generalizing values <;>
    simp_all [LProp.zeroForm, LProp.denote, LTerm.denote] <;> omega

end Gabbro.Grammatik.Invarianten.Frag
