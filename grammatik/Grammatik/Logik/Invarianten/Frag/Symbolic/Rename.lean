module

public import Grammatik.Logik.Invarianten.Korrekt.Linear

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt

/-- Renaming changes keys only; it never evaluates an unknown integer. -/
def renameTerm (rename : α → β) : LTerm α → LTerm β
  | .var key => .var (rename key)
  | .konst value => .konst value
  | .add left right => .add (renameTerm rename left) (renameTerm rename right)
  | .sub left right => .sub (renameTerm rename left) (renameTerm rename right)
  | .scale coefficient term => .scale coefficient (renameTerm rename term)

def renameQF (rename : α → β) : QF α → QF β
  | .tru => .tru
  | .fls => .fls
  | .atom relation term => .atom relation (renameTerm rename term)
  | .conj left right => .conj (renameQF rename left) (renameQF rename right)
  | .disj left right => .disj (renameQF rename left) (renameQF rename right)

def renameProp (rename : α → β) : LProp α → LProp β
  | .tru => .tru
  | .fls => .fls
  | .le left right => .le (renameTerm rename left) (renameTerm rename right)
  | .lt left right => .lt (renameTerm rename left) (renameTerm rename right)
  | .eq left right => .eq (renameTerm rename left) (renameTerm rename right)
  | .dvd divisor term => .dvd divisor (renameTerm rename term)
  | .not body => .not (renameProp rename body)
  | .and left right => .and (renameProp rename left) (renameProp rename right)
  | .or left right => .or (renameProp rename left) (renameProp rename right)
  | .imp left right => .imp (renameProp rename left) (renameProp rename right)
  | .ex key body => .ex (rename key) (renameProp rename body)
  | .all key body => .all (rename key) (renameProp rename body)

theorem renameTerm_denote (rename : α → β) (term : LTerm α) (values : Assignment β) :
    (renameTerm rename term).denote values = term.denote (values ∘ rename) := by
  induction term <;> simp_all only [renameTerm, LTerm.denote, Function.comp_apply]

theorem renameQF_denote (rename : α → β) (formula : QF α) (values : Assignment β) :
    (renameQF rename formula).denote values ↔ formula.denote (values ∘ rename) := by
  induction formula <;> simp_all only [renameQF, QF.denote, renameTerm_denote]

/-- An injective embedding cannot capture an old key when a binder is renamed. -/
theorem bind_rename [DecidableEq α] [DecidableEq β] (rename : α → β)
    (injective : Function.Injective rename) (values : Assignment β) (key : α) (value : Int) :
    (values.bind (rename key) value) ∘ rename = Assignment.bind (values ∘ rename) key value := by
  funext other
  by_cases same : other = key
  · subst other
    simp only [Function.comp_apply, Assignment.bind, ↓reduceIte]
  · have different : rename other ≠ rename key := fun equal => same (injective equal)
    simp only [Function.comp_apply, Assignment.bind, same, different, ↓reduceIte]

theorem renameProp_denote [DecidableEq α] [DecidableEq β] (rename : α → β)
    (injective : Function.Injective rename) (formula : LProp α) (values : Assignment β) :
    (renameProp rename formula).denote values ↔ formula.denote (values ∘ rename) := by
  induction formula generalizing values with
  | tru | fls => rfl
  | le left right | lt left right | eq left right =>
      simp only [renameProp, LProp.denote, renameTerm_denote]
  | dvd divisor term => simp only [renameProp, LProp.denote, renameTerm_denote]
  | not body ih => exact not_congr (ih values)
  | and left right ihLeft ihRight => exact and_congr (ihLeft values) (ihRight values)
  | or left right ihLeft ihRight => exact or_congr (ihLeft values) (ihRight values)
  | imp left right ihLeft ihRight => exact imp_congr (ihLeft values) (ihRight values)
  | ex key body ih =>
      change (∃ value, (renameProp rename body).denote (values.bind (rename key) value)) ↔ _
      simp only [ih, bind_rename rename injective]
      rfl
  | all key body ih =>
      change (∀ value, (renameProp rename body).denote (values.bind (rename key) value)) ↔ _
      simp only [ih, bind_rename rename injective]
      rfl

/-- Substitution after a fresh-key embedding has exactly the same meaning as
    substitution before it. This includes stores into the memory summand. -/
theorem rename_subst_denote [DecidableEq α] [DecidableEq β] (rename : α → β)
    (injective : Function.Injective rename) (key : α) (replacement : LTerm α)
    (formula : QF α) (values : Assignment β) :
    (renameQF rename (formula.subst key replacement)).denote values ↔
      (renameQF rename formula).denote
        (values.bind (rename key) ((renameTerm rename replacement).denote values)) := by
  rw [renameQF_denote, subst_denote, renameQF_denote, renameTerm_denote,
    bind_rename rename injective]

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
