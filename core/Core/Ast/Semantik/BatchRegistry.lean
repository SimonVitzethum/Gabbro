module

public import Core.Ast.Semantik.LeafObligations
public import Core.Ast.Semantik.OperatorObligations
public import Core.Ast.Semantik.StatementObligations

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Waechter

def trueLitProofs : RegistryEntry ``Expr.trueLit ⟨.surface, Quellform.statements trueLitForm trueLitJoint ``Expr.trueLit⟩ where
  realization := .surface trueLit_parse trueLit_elaboriert trueLit_realisiert
  acceptanceRule := trueLit_annahme
  idealRule := trueLit_ideal
  unitsAndCommutation := trueLit_einheit
  implementationRule := trueLit_impl
  preservation := trueLit_erhaltung
  jointlySatisfiable := trueLit_erfuellbar

def falseLitProofs : RegistryEntry ``Expr.falseLit ⟨.surface, Quellform.statements falseLitForm falseLitJoint ``Expr.falseLit⟩ where
  realization := .surface falseLit_parse falseLit_elaboriert falseLit_realisiert
  acceptanceRule := falseLit_annahme
  idealRule := falseLit_ideal
  unitsAndCommutation := falseLit_einheit
  implementationRule := falseLit_impl
  preservation := falseLit_erhaltung
  jointlySatisfiable := falseLit_erfuellbar

def variableProofs : RegistryEntry ``Expr.variable ⟨.surface, Quellform.statements variableForm variableJoint ``Expr.variable⟩ where
  realization := .surface variable_parse variable_elaboriert variable_realisiert
  acceptanceRule := variable_annahme
  idealRule := variable_ideal
  unitsAndCommutation := variable_einheit
  implementationRule := variable_impl
  preservation := variable_erhaltung
  jointlySatisfiable := variable_erfuellbar

def negativeLitProofs : RegistryEntry ``Expr.negativeLit ⟨.surface, Quellform.statements negativeLitForm negativeLitJoint ``Expr.negativeLit⟩ where
  realization := .surface negativeLit_parse negativeLit_elaboriert negativeLit_realisiert
  acceptanceRule := negativeLit_annahme
  idealRule := negativeLit_ideal
  unitsAndCommutation := negativeLit_einheit
  implementationRule := negativeLit_impl
  preservation := negativeLit_erhaltung
  jointlySatisfiable := negativeLit_erfuellbar

def negProofs : RegistryEntry ``Expr.neg ⟨.surface, Quellform.statements negForm negJoint ``Expr.neg⟩ where
  realization := .surface neg_parse neg_elaboriert neg_realisiert
  acceptanceRule := neg_annahme
  idealRule := neg_ideal
  unitsAndCommutation := neg_einheit
  implementationRule := neg_impl
  preservation := neg_erhaltung
  jointlySatisfiable := neg_erfuellbar

def notValueProofs : RegistryEntry ``Expr.not ⟨.surface, Quellform.statements notValueForm notValueJoint ``Expr.not⟩ where
  realization := .surface notValue_parse notValue_elaboriert notValue_realisiert
  acceptanceRule := notValue_annahme
  idealRule := notValue_ideal
  unitsAndCommutation := notValue_einheit
  implementationRule := notValue_impl
  preservation := notValue_erhaltung
  jointlySatisfiable := notValue_erfuellbar

def divisionProofs : RegistryEntry ``Expr.div ⟨.surface, Quellform.statements divisionForm divisionJoint ``Expr.div⟩ where
  realization := .surface division_parse division_elaboriert division_realisiert
  acceptanceRule := division_annahme
  idealRule := division_ideal
  unitsAndCommutation := division_einheit
  implementationRule := division_impl
  preservation := division_erhaltung
  jointlySatisfiable := division_erfuellbar

def comparisonProofs : RegistryEntry ``Expr.compare ⟨.surface, Quellform.statements comparisonForm comparisonJoint ``Expr.compare⟩ where
  realization := .surface comparison_parse comparison_elaboriert comparison_realisiert
  acceptanceRule := comparison_annahme
  idealRule := comparison_ideal
  unitsAndCommutation := comparison_einheit
  implementationRule := comparison_impl
  preservation := comparison_erhaltung
  jointlySatisfiable := comparison_erfuellbar

def logicProofs : RegistryEntry ``Expr.logic ⟨.surface, Quellform.statements logicForm logicJoint ``Expr.logic⟩ where
  realization := .surface logic_parse logic_elaboriert logic_realisiert
  acceptanceRule := logic_annahme
  idealRule := logic_ideal
  unitsAndCommutation := logic_einheit
  implementationRule := logic_impl
  preservation := logic_erhaltung
  jointlySatisfiable := logic_erfuellbar

def assignVarProofs : RegistryEntry ``Stmt.assignVar ⟨.surface, Quellform.statements assignVarForm assignVarJoint ``Stmt.assignVar⟩ where
  realization := .surface assignVar_parse assignVar_elaboriert assignVar_realisiert
  acceptanceRule := assignVar_annahme
  idealRule := assignVar_ideal
  unitsAndCommutation := assignVar_einheit
  implementationRule := assignVar_impl
  preservation := assignVar_erhaltung
  jointlySatisfiable := assignVar_erfuellbar

def returnValueProofs : RegistryEntry ``Stmt.ret ⟨.surface, Quellform.statements returnValueForm returnValueJoint ``Stmt.ret⟩ where
  realization := .surface returnValue_parse returnValue_elaboriert returnValue_realisiert
  acceptanceRule := returnValue_annahme
  idealRule := returnValue_ideal
  unitsAndCommutation := returnValue_einheit
  implementationRule := returnValue_impl
  preservation := returnValue_erhaltung
  jointlySatisfiable := returnValue_erfuellbar

def ifElseProofs : RegistryEntry ``Stmt.ite ⟨.surface, Quellform.statements ifElseForm ifElseJoint ``Stmt.ite⟩ where
  realization := .surface ifElse_parse ifElse_elaboriert ifElse_realisiert
  acceptanceRule := ifElse_annahme
  idealRule := ifElse_ideal
  unitsAndCommutation := ifElse_einheit
  implementationRule := ifElse_impl
  preservation := ifElse_erhaltung
  jointlySatisfiable := ifElse_erfuellbar

def bracedProofs : RegistryEntry ``BracedBlock.braces ⟨.surface, Quellform.statements bracedForm bracedJoint ``BracedBlock.braces⟩ where
  realization := .surface braced_parse braced_elaboriert braced_realisiert
  acceptanceRule := braced_annahme
  idealRule := braced_ideal
  unitsAndCommutation := braced_einheit
  implementationRule := braced_impl
  preservation := braced_erhaltung
  jointlySatisfiable := braced_erfuellbar

def subtractionProofs : RegistryEntry ``Arith.sub ⟨.surface, Quellform.statements subtractionForm subtractionJoint ``Arith.sub⟩ where
  realization := .surface subtraction_parse subtraction_elaboriert subtraction_realisiert
  acceptanceRule := subtraction_annahme
  idealRule := subtraction_ideal
  unitsAndCommutation := subtraction_einheit
  implementationRule := subtraction_impl
  preservation := subtraction_erhaltung
  jointlySatisfiable := subtraction_erfuellbar

def thenJumpProofs : RegistryEntry ``Befehl.springe ⟨.surface, Quellform.statements thenJumpForm thenJumpJoint ``Befehl.springe⟩ where
  realization := .surface thenJump_parse thenJump_elaboriert thenJump_realisiert
  acceptanceRule := thenJump_annahme
  idealRule := thenJump_ideal
  unitsAndCommutation := thenJump_einheit
  implementationRule := thenJump_impl
  preservation := thenJump_erhaltung
  jointlySatisfiable := thenJump_erfuellbar

def trueLitEntry : RegistryEntry ``Expr.trueLit (exprSchema ``Expr.trueLit) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "trueLit") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "trueLit") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact trueLitProofs

def falseLitEntry : RegistryEntry ``Expr.falseLit (exprSchema ``Expr.falseLit) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "falseLit") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "falseLit") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "falseLit") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact falseLitProofs

def variableEntry : RegistryEntry ``Expr.variable (exprSchema ``Expr.variable) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "variable") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "variable") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "variable") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "variable") (b := "falseLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact variableProofs

def negativeLitEntry : RegistryEntry ``Expr.negativeLit (exprSchema ``Expr.negativeLit) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "negativeLit") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativeLit") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativeLit") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativeLit") (b := "falseLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativeLit") (b := "variable") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact negativeLitProofs

def negEntry : RegistryEntry ``Expr.neg (exprSchema ``Expr.neg) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "neg") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "neg") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "neg") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "neg") (b := "falseLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "neg") (b := "variable") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "neg") (b := "negativeLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact negProofs

def notValueEntry : RegistryEntry ``Expr.not (exprSchema ``Expr.not) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "not") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "not") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "not") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "not") (b := "falseLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "not") (b := "variable") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "not") (b := "negativeLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "not") (b := "neg") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact notValueProofs

def divisionEntry : RegistryEntry ``Expr.div (exprSchema ``Expr.div) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "div") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "div") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "div") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "div") (b := "falseLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "div") (b := "variable") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "div") (b := "negativeLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "div") (b := "neg") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "div") (b := "not") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact divisionProofs

def comparisonEntry : RegistryEntry ``Expr.compare (exprSchema ``Expr.compare) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "compare") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "falseLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "variable") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "negativeLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "neg") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "not") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "compare") (b := "div") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact comparisonProofs

def logicEntry : RegistryEntry ``Expr.logic (exprSchema ``Expr.logic) := by
  rw [exprSchema,
    ite_eq_right (differentLabels (a := "logic") (b := "lit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "binary") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "trueLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "falseLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "variable") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "negativeLit") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "neg") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "not") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "div") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "logic") (b := "compare") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact logicProofs

def assignVarEntry : RegistryEntry ``Stmt.assignVar (stmtSchema ``Stmt.assignVar) := by
  rw [stmtSchema,
    ite_eq_right (differentLabels (a := "assignVar") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact assignVarProofs

def returnValueEntry : RegistryEntry ``Stmt.ret (stmtSchema ``Stmt.ret) := by
  rw [stmtSchema,
    ite_eq_right (differentLabels (a := "ret") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "ret") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact returnValueProofs

def ifElseEntry : RegistryEntry ``Stmt.ite (stmtSchema ``Stmt.ite) := by
  rw [stmtSchema,
    ite_eq_right (differentLabels (a := "ite") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "ite") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "ite") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact ifElseProofs

def bracedEntry : RegistryEntry ``BracedBlock.braces (bracedSchema ``BracedBlock.braces) := by
  rw [bracedSchema,
    ite_eq_left rfl]
  exact bracedProofs

end Gabbro.Core.Ast.Semantik
