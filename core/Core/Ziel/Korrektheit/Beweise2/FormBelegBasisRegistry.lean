module

public import Core.Ziel.Korrektheit.Beweise2.FormBelegBasis

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Gabbro.Core.Ast Gabbro.Core.Ast.Semantik Gabbro.Core.Katalog Gabbro.Core.Waechter

/-- The family is genuinely backed by the existing registry: each form maps to a constructor of the
    root-imported `Expr` family whose complete typed `RegistryEntry` is already registered. -/
def basisFormConstructor : BasisForm → Lean.Name
  | .lit => ``Expr.lit
  | .binary => ``Expr.binary
  | .trueLit => ``Expr.trueLit
  | .falseLit => ``Expr.falseLit
  | .variable => ``Expr.variable
  | .negativeLit => ``Expr.negativeLit
  | .neg => ``Expr.neg
  | .not => ``Expr.not
  | .div => ``Expr.div
  | .compare => ``Expr.compare
  | .logic => ``Expr.logic

theorem basisForm_registry_covered (f : BasisForm) :
    Nonempty (RegistryEntry (basisFormConstructor f) (exprSchema (basisFormConstructor f))) := by
  cases f
  · exact ⟨literalEntry⟩
  · exact ⟨binaryEntry⟩
  · exact ⟨trueLitEntry⟩
  · exact ⟨falseLitEntry⟩
  · exact ⟨variableEntry⟩
  · exact ⟨negativeLitEntry⟩
  · exact ⟨negEntry⟩
  · exact ⟨notValueEntry⟩
  · exact ⟨divisionEntry⟩
  · exact ⟨comparisonEntry⟩
  · exact ⟨logicEntry⟩

/-- The registry's joint satisfiability statements are inhabited by the existing form proofs, so
    the premises of every rule in each entry hold together. -/
theorem basisForm_jointlySatisfiable (f : BasisForm) :
    Nonempty (match f with
      | .lit => LiteralErfuellbar
      | .binary => BinaryErfuellbar
      | .trueLit => trueLitJoint
      | .falseLit => falseLitJoint
      | .variable => variableJoint
      | .negativeLit => negativeLitJoint
      | .neg => negJoint
      | .not => notValueJoint
      | .div => divisionJoint
      | .compare => comparisonJoint
      | .logic => logicJoint) := by
  cases f
  · exact ⟨literal_erfuellbar⟩
  · exact ⟨binary_erfuellbar⟩
  · exact ⟨trueLit_erfuellbar⟩
  · exact ⟨falseLit_erfuellbar⟩
  · exact ⟨variable_erfuellbar⟩
  · exact ⟨negativeLit_erfuellbar⟩
  · exact ⟨neg_erfuellbar⟩
  · exact ⟨notValue_erfuellbar⟩
  · exact ⟨division_erfuellbar⟩
  · exact ⟨comparison_erfuellbar⟩
  · exact ⟨logic_erfuellbar⟩

/-- The form's instruction occurs in the witness unit's code at the exact linearisation position
    that the registry entry assigns to it. This is the unit-level counterpart of `Quellform.Realisiert`. -/
theorem basisUnit_occurrence (f : BasisForm) :
    match f with
    | .lit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.literal 0 1)
    | .binary => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.binaer .add 0)
    | .trueLit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.wahrheitswert 0 true)
    | .falseLit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.wahrheitswert 0 false)
    | .variable => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.lesen 0 0)
    | .negativeLit => (fragment Ast.Category.unit (basisUnit f)).code[0]? = some (.negativ 0 1)
    | .neg => (fragment Ast.Category.unit (basisUnit f)).code[1]? = some (.negieren 0)
    | .not => (fragment Ast.Category.unit (basisUnit f)).code[1]? = some (.verneinen 0)
    | .div => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.teilen 0)
    | .compare => (fragment Ast.Category.unit (basisUnit f)).code[2]? = some (.vergleichen .lt 0)
    | .logic => (fragment Ast.Category.unit (basisUnit f)).code[1]? = some (.springeWenn 0 false 2) := by
  cases f <;>
    first
    | rw [basisUnit_code_lit]
    | rw [basisUnit_code_binary]
    | rw [basisUnit_code_trueLit]
    | rw [basisUnit_code_falseLit]
    | rw [basisUnit_code_variable]
    | rw [basisUnit_code_negativeLit]
    | rw [basisUnit_code_neg]
    | rw [basisUnit_code_not]
    | rw [basisUnit_code_div]
    | rw [basisUnit_code_compare]
    | rw [basisUnit_code_logic]
  all_goals rfl

/-- The missing constructor ranges, proved explicitly: the thirteen `Expr` constructors outside the
    registered base family are aggregate, record, variant, text and option forms. None of them is a
    member of `BasisForm`, so this certificate does not claim to cover them. -/
theorem basisForm_nicht_arrayValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.arrayValue := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_arrayIndex (f : BasisForm) : basisFormConstructor f ≠ ``Expr.arrayIndex := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_tupleValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.tupleValue := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_tupleField (f : BasisForm) : basisFormConstructor f ≠ ``Expr.tupleField := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_recordValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.recordValue := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_recordField (f : BasisForm) : basisFormConstructor f ≠ ``Expr.recordField := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_variantValue (f : BasisForm) : basisFormConstructor f ≠ ``Expr.variantValue := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_textLiteral (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textLiteral := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_textConcat (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textConcat := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_textIndex (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textIndex := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_substring (f : BasisForm) : basisFormConstructor f ≠ ``Expr.substring := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_textLength (f : BasisForm) : basisFormConstructor f ≠ ``Expr.textLength := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]
theorem basisForm_nicht_optionIsSome (f : BasisForm) : basisFormConstructor f ≠ ``Expr.optionIsSome := by
  cases f <;> simp only [basisFormConstructor, Lean.Name.str.injEq, String.reduceEq, and_false, not_false_eq_true]

end Gabbro.Core.Ziel.Korrektheit
