/-
M6 batch 1 prover checklist

Edit only lines containing the proof placeholder. Keep signatures, definitions,
proof hints, and guard pins fixed for the handoff. Recipe numbers for syntax
refer to Core.Ast. Recipe numbers for semantics refer to the proof phase in
Core.Ast.SemantikRezept. Names under Surface belong to Core.Ast.Surface. Names
under Semantics belong to Core.Ast.Semantik.

Shared expression and block infrastructure
  Syntax 3 — Infix.token_injective, noOperatorAtClose, noOperatorAtSemicolon, noOperatorAtOpenBrace,
    ExprReads.deterministic, ExprReads.consumes, AtomReads.consumes, ExprTail.consumes
  Syntax 3 — StmtReads.let_header, AtomReads.not_assignment, StmtReads.deterministic,
    BlockItems.deterministic, StmtReads.consumes, BlockItems.consumes
  Syntax 4 — Expr.printAtom
  Syntax 4 — Stmt.printReads, Block.printItems_reads
  Semantic 1 and 4 — expr_ergebnis_typ
  Semantic 1 and 6 — wertIn_widen
  Semantic 6 — expr_keine_invarianten, stmt_keine_invarianten

true (Expr.trueLit)
  Syntax 3 — AtomReads.true_inversion
  Surface
  Syntax 4 — trueLit_print
  Syntax 5 — trueLit_reads, trueLit_erfuellbar
  Semantics
  Semantic 1 — trueLit_parse, trueLit_elaboriert, trueLit_realisiert
  Semantic 2 — trueLit_annahme, trueLit_ideal
  Semantic 3 — trueLit_einheit
  Semantic 4 — trueLit_impl
  Semantic 5 and 6 — trueLit_erhaltung
  Semantic 7 — trueLit_erfuellbar

false (Expr.falseLit)
  Syntax 3 — AtomReads.false_inversion
  Surface
  Syntax 4 — falseLit_print
  Syntax 5 — falseLit_reads, falseLit_erfuellbar
  Semantics
  Semantic 1 — falseLit_parse, falseLit_elaboriert, falseLit_realisiert
  Semantic 2 — falseLit_annahme, falseLit_ideal
  Semantic 3 — falseLit_einheit
  Semantic 4 — falseLit_impl
  Semantic 5 and 6 — falseLit_erhaltung
  Semantic 7 — falseLit_erfuellbar

local reference (Expr.variable)
  Syntax 3 — AtomReads.variable_inversion, Local.visible_unique
  Semantic 1 — local_binding_type
  Surface
  Syntax 4 — variable_print
  Syntax 5 — variable_reads, variable_erfuellbar
  Semantics
  Semantic 1 — variable_parse, variable_elaboriert, variable_realisiert
  Semantic 2 — variable_annahme, variable_ideal
  Semantic 3 — variable_einheit
  Semantic 4 — variable_impl
  Semantic 5 and 6 — variable_erhaltung
  Semantic 7 — variable_erfuellbar

negative numeral (Expr.negativeLit)
  Syntax 3 — AtomReads.negative_inversion
  Surface
  Syntax 4 — negativeLit_print
  Syntax 5 — negativeLit_reads, negativeLit_erfuellbar
  Semantics
  Semantic 1 — negativeLit_parse, negativeLit_elaboriert, negativeLit_realisiert
  Semantic 2 — negativeLit_annahme, negativeLit_ideal
  Semantic 3 — negativeLit_einheit
  Semantic 4 — negativeLit_impl
  Semantic 5 and 6 — negativeLit_erhaltung
  Semantic 7 — negativeLit_erfuellbar

unary - (Expr.neg)
  Syntax 3 — AtomReads.neg_inversion
  Surface
  Syntax 4 — neg_print
  Syntax 5 — neg_reads, neg_erfuellbar
  Semantics
  Semantic 1 — neg_parse, neg_elaboriert, neg_realisiert
  Semantic 2 — neg_annahme, neg_ideal
  Semantic 3 — neg_einheit
  Semantic 4 — neg_impl
  Semantic 5 and 6 — neg_erhaltung
  Semantic 7 — neg_erfuellbar

unary ! (Expr.not)
  Syntax 3 — AtomReads.not_inversion
  Surface
  Syntax 4 — notValue_print
  Syntax 5 — notValue_reads, notValue_erfuellbar
  Semantics
  Semantic 1 — notValue_parse, notValue_elaboriert, notValue_realisiert
  Semantic 2 — notValue_annahme, notValue_ideal
  Semantic 3 — notValue_einheit
  Semantic 4 — notValue_impl
  Semantic 5 and 6 — notValue_erhaltung
  Semantic 7 — notValue_erfuellbar

binary - (Arith.sub in Expr.binary)
  Syntax 3 — ExprTail.arith_inversion
  Surface
  Syntax 4 — subtraction_print
  Syntax 5 — subtraction_reads, subtraction_erfuellbar
  Semantics
  Semantic 1 — subtraction_parse, subtraction_elaboriert, subtraction_realisiert
  Semantic 2 — subtraction_annahme, subtraction_ideal
  Semantic 3 — subtraction_einheit
  Semantic 4 — subtraction_impl
  Semantic 5 and 6 — subtraction_erhaltung
  Semantic 7 — subtraction_erfuellbar

/ (Expr.div)
  Syntax 3 — ExprTail.div_inversion
  Semantic 1 — Zahl.div_bounds
  Semantic 2 — division_guard_exact
  Surface
  Syntax 4 — division_print
  Syntax 5 — division_reads, division_erfuellbar
  Semantics
  Semantic 1 — division_parse, division_elaboriert, division_realisiert
  Semantic 2 — division_annahme, division_ideal
  Semantic 3 — division_einheit
  Semantic 4 — division_impl
  Semantic 5 and 6 — division_erhaltung
  Semantic 7 — division_erfuellbar

==, !=, <, <=, >, >= (Expr.compare)
  Syntax 3 — ExprTail.compare_inversion
  Surface
  Syntax 4 — comparison_print
  Syntax 5 — comparison_reads, comparison_erfuellbar
  Semantics
  Semantic 1 — comparison_parse, comparison_elaboriert, comparison_realisiert
  Semantic 2 — comparison_annahme, comparison_ideal
  Semantic 3 — comparison_einheit
  Semantic 4 — comparison_impl
  Semantic 5 and 6 — comparison_erhaltung
  Semantic 7 — comparison_erfuellbar

&&, || (Expr.logic)
  Syntax 3 — ExprTail.logic_inversion
  Surface
  Syntax 4 — logic_print
  Syntax 5 — logic_reads, logic_erfuellbar
  Semantics
  Semantic 1 — logic_parse, logic_elaboriert, logic_realisiert
  Semantic 2 — logic_annahme, logic_ideal
  Semantic 3 — logic_einheit
  Semantic 4 — logic_impl
  Semantic 5 and 6 — logic_erhaltung
  Semantic 7 — logic_erfuellbar

x = e; (Stmt.assignVar)
  Syntax 3 — StmtReads.assign_inversion
  Semantic 1 and 6 — assignment_effect
  Surface
  Syntax 4 — assignVar_print
  Syntax 5 — assignVar_reads, assignVar_erfuellbar
  Semantics
  Semantic 1 — assignVar_parse, assignVar_elaboriert, assignVar_realisiert
  Semantic 2 — assignVar_annahme, assignVar_ideal
  Semantic 3 — assignVar_einheit
  Semantic 4 — assignVar_impl
  Semantic 5 and 6 — assignVar_erhaltung
  Semantic 7 — assignVar_erfuellbar

return e; (Stmt.ret)
  Syntax 3 — StmtReads.ret_inversion
  Semantic 1 and 6 — return_effect
  Surface
  Syntax 4 — returnValue_print
  Syntax 5 — returnValue_reads, returnValue_erfuellbar
  Semantics
  Semantic 1 — returnValue_parse, returnValue_elaboriert, returnValue_realisiert
  Semantic 2 — returnValue_annahme, returnValue_ideal
  Semantic 3 — returnValue_einheit
  Semantic 4 — returnValue_impl
  Semantic 5 and 6 — returnValue_erhaltung
  Semantic 7 — returnValue_erfuellbar

if c { … } else { … } (Stmt.ite)
  Syntax 3 — StmtReads.ite_inversion
  Semantic 2 — branch_effect
  Surface
  Syntax 4 — ifElse_print
  Syntax 5 — ifElse_reads, ifElse_erfuellbar
  Semantics
  Semantic 1 — ifElse_parse, ifElse_elaboriert, ifElse_realisiert
  Semantic 2 — ifElse_annahme, ifElse_ideal
  Semantic 3 — ifElse_einheit
  Semantic 4 — ifElse_impl
  Semantic 5 and 6 — ifElse_erhaltung
  Semantic 7 — ifElse_erfuellbar

{ … } (BracedBlock.braces)
  Syntax 3 — BlockReads.braced_inversion
  Semantic 1 and 6 — block_scope_extends
  Surface
  Syntax 4 — braced_print
  Syntax 5 — braced_reads, braced_erfuellbar
  Semantics
  Semantic 1 — braced_parse, braced_elaboriert, braced_realisiert
  Semantic 2 — braced_annahme, braced_ideal
  Semantic 3 — braced_einheit
  Semantic 4 — braced_impl
  Semantic 5 and 6 — braced_erhaltung
  Semantic 7 — braced_erfuellbar

internal jump over else (Befehl.springe)
  Semantics
  Semantic 1 — thenJump_parse, thenJump_elaboriert, thenJump_realisiert
  Semantic 2 — thenJump_annahme, thenJump_ideal
  Semantic 3 — thenJump_einheit
  Semantic 4 — thenJump_impl
  Semantic 5 and 6 — thenJump_erhaltung
  Semantic 7 — thenJump_erfuellbar
-/
module

public import Core.Ast.Semantik.Quellform
public import Core.Ast.BatchSurface

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Lean (Name)

abbrev StatementContext := Scope × Option (Ty .value)
abbrev ReturnContext := Scope × Ty .value

def trueLitForm (scope : Scope) : Quellform (.expression scope) (PUnit) where
  produktion := Surface.trueLit scope
  befehl := fun _ => .wahrheitswert 0 true
  position := fun _ => 0

def trueLitJoint : Prop :=
  ∀ platform start, (trueLitForm []).ErfuellbarAm platform start PUnit.unit

def falseLitForm (scope : Scope) : Quellform (.expression scope) (PUnit) where
  produktion := Surface.falseLit scope
  befehl := fun _ => .wahrheitswert 0 false
  position := fun _ => 0

def falseLitJoint : Prop :=
  ∀ platform start, (falseLitForm []).ErfuellbarAm platform start PUnit.unit

def variableForm (scope : Scope) : Quellform (.expression scope) (Surface.VariableArgs scope) where
  produktion := Surface.localValue scope
  befehl := fun args => .lesen 0 args.ref.index
  position := fun _ => 0

def variableJoint : Prop :=
  ∀ platform start, ∃ (scope : Scope) (args : Surface.VariableArgs scope), (variableForm scope).ErfuellbarAm platform start args

def negativeLitForm (scope : Scope) : Quellform (.expression scope) (Nat) where
  produktion := Surface.negativeLit scope
  befehl := fun magnitude => .negativ 0 magnitude
  position := fun _ => 0

def negativeLitJoint : Prop :=
  ∀ platform start, ∃ magnitude, 0 < magnitude ∧ (negativeLitForm []).ErfuellbarAm platform start magnitude

def negForm (scope : Scope) : Quellform (.expression scope) (Surface.NegArgs scope) where
  produktion := Surface.neg scope
  befehl := fun _ => .negieren 0
  position := fun args => (expr 0 args.operand).code.length

def negJoint : Prop :=
  ∀ platform start, ∃ args, (negForm []).ErfuellbarAm platform start args

def notValueForm (scope : Scope) : Quellform (.expression scope) (Expr scope .bool) where
  produktion := Surface.notValue scope
  befehl := fun _ => .verneinen 0
  position := fun operand => (expr 0 operand).code.length

def notValueJoint : Prop :=
  ∀ platform start, ∃ operand, (notValueForm []).ErfuellbarAm platform start operand

def divisionForm (scope : Scope) : Quellform (.expression scope) (Surface.DivisionArgs scope) where
  produktion := Surface.division scope
  befehl := fun _ => .teilen 0
  position := fun args => (expr 0 args.left).code.length + (expr 1 args.right).code.length

def divisionJoint : Prop :=
  ∀ (platform : Plattform) start (unsigned : Bool), ∃ args : Surface.DivisionArgs [],
    ((0 ≤ args.lo₁ ∧ 1 ≤ args.lo₂) ↔ unsigned = true) ∧
    (divisionForm []).ErfuellbarAm platform start args

def comparisonForm (scope : Scope) : Quellform (.expression scope) (Surface.CompareArgs scope) where
  produktion := Surface.comparison scope
  befehl := fun args => .vergleichen args.op 0
  position := fun args => (expr 0 args.left).code.length + (expr 1 args.right).code.length

def comparisonJoint : Prop :=
  ∀ platform start op, ∃ args : Surface.CompareArgs [], args.op = op ∧
    (comparisonForm []).ErfuellbarAm platform start args

def logicForm (scope : Scope) : Quellform (.expression scope) (Surface.LogicArgs scope) where
  produktion := Surface.logic scope
  befehl := fun args => .springeWenn 0 args.op.skips ((expr 0 args.right).code.length + 1)
  position := fun args => (expr 0 args.left).code.length

def logicJoint : Prop :=
  ∀ (platform : Plattform) start op (bit : Bool), ∃ args : Surface.LogicArgs [],
    args.op = op ∧ args.left = (if bit then .trueLit else .falseLit) ∧
    (logicForm []).ErfuellbarAm platform start args

def assignVarForm (ctx : StatementContext) : Quellform (.statement ctx.1 ctx.2) (Surface.AssignArgs ctx.1) where
  produktion := Surface.assignVar ctx.1 ctx.2
  befehl := fun args => .zuweisen 0 args.ref.index args.ref.binding.type
  position := fun args => (expr 0 args.value).code.length

def assignVarJoint : Prop :=
  ∀ platform start, ∃ (scope : Scope) (args : Surface.AssignArgs scope), (assignVarForm (scope, none)).ErfuellbarAm platform start args

def returnValueForm (ctx : ReturnContext) : Quellform (.statement ctx.1 (some ctx.2)) (Surface.ReturnArgs ctx.1 ctx.2) where
  produktion := Surface.returnValue ctx.1 ctx.2
  befehl := fun _ => .zurueck 0 ctx.2
  position := fun args => (expr 0 args.value).code.length

def returnValueJoint : Prop :=
  ∀ platform start, ∃ (expected : Ty .value) (args : Surface.ReturnArgs [] expected),
    (returnValueForm ([], expected)).ErfuellbarAm platform start args

def ifElseForm (ctx : StatementContext) : Quellform (.statement ctx.1 ctx.2) (Surface.IfArgs ctx.1 ctx.2) where
  produktion := Surface.ifElse ctx.1 ctx.2
  befehl := fun args => .springeWenn 0 false ((bracedBlock args.yes).code.length + 2)
  position := fun args => (expr 0 args.condition).code.length

def ifElseJoint : Prop :=
  ∀ (platform : Plattform) start (bit : Bool), ∃ args : Surface.IfArgs [] none,
    args.condition = (if bit then .trueLit else .falseLit) ∧ (ifElseForm ([], none)).ErfuellbarAm platform start args

def bracedForm (ctx : StatementContext) : Quellform (.block ctx.1 ctx.2) (Statements ctx.2 ctx.1) where
  produktion := Surface.braced ctx.1 ctx.2
  befehl := fun args => .blockEnde (args.1.length - ctx.1.length)
  position := fun args => (block args.2).code.length

def bracedJoint : Prop :=
  ∀ platform start, ∃ args, (bracedForm ([], none)).ErfuellbarAm platform start args


def subtractionForm (scope : Scope) : Quellform (.expression scope) (Surface.SubtractArgs scope) where
  produktion := Surface.subtraction scope
  befehl := fun _ => .binaer .sub 0
  position := fun args => (expr 0 args.val.left).code.length + (expr 1 args.val.right).code.length

def subtractionJoint : Prop :=
  ∀ platform start, ∃ args, (subtractionForm []).ErfuellbarAm platform start args

/-- The internal jump follows the selected then branch and its closing brace. -/
def thenJumpForm (ctx : StatementContext) :
    Quellform (.statement ctx.1 ctx.2) (Surface.IfArgs ctx.1 ctx.2) where
  produktion := Surface.ifElse ctx.1 ctx.2
  befehl := fun args => .springe ((bracedBlock args.no).code.length + 1)
  position := fun args => (expr 0 args.condition).code.length + 1 + (bracedBlock args.yes).code.length

def thenJumpJoint : Prop :=
  ∀ platform start, ∃ args : Surface.IfArgs [] none,
    args.condition = .trueLit ∧ (thenJumpForm ([], none)).ErfuellbarAm platform start args

end Gabbro.Core.Ast.Semantik
