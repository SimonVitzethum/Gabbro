module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Aggregate.Arrays
public import Core.Ast.Aggregate.Tuples

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter
open Lean (Name)

def literalForm (scope : Scope) : Quellform (.expression scope) Nat where
  produktion := Surface.literal scope
  befehl := .literal 0
  position := fun _ => 0

def binaryForm (scope : Scope) :
    Quellform (.expression scope) (Surface.BinaryArgs scope) where
  produktion := Surface.binary scope
  befehl := fun args => .binaer args.op 0
  position := fun args => (((expr 0 args.left).anhaengen (expr 1 args.right)).code).length

def letForm (scope : Scope) : Quellform (.statement scope) (Surface.LetArgs scope) where
  produktion := Surface.letValue scope
  befehl := fun args => .binden args.name 0
  position := fun args => (expr 0 args.value).code.length

def LiteralErfuellbar : Prop :=
  ∀ (platform : Plattform) start, ∃ value, (literalForm []).ErfuellbarAm platform start value

def BinaryErfuellbar : Prop :=
  ∀ (platform : Plattform) start op, ∃ args : Surface.BinaryArgs [], args.op = op ∧
    (binaryForm []).ErfuellbarAm platform start args

def LetErfuellbar : Prop :=
  ∀ (platform : Plattform) start, ∃ args, (letForm []).ErfuellbarAm platform start args

/-- Missing constructor specifications yield an uninhabitable registry entry. -/
def nichtSpezifiziert (constructor : Name) : RegistrySchema constructor :=
  ⟨.core, ⟨.core False, False, False, False, False, False, False⟩⟩

theorem differentLabels {a b : String} {left right : Name} (different : a ≠ b) :
    Name.str left a ≠ Name.str right b :=
  fun same => different (Name.str.inj same).2

def exprSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Expr.lit then
    ⟨.surface, Quellform.statements literalForm LiteralErfuellbar constructor⟩
  else if constructor = ``Expr.binary then
    ⟨.surface, Quellform.statements binaryForm BinaryErfuellbar constructor⟩
  else if constructor = ``Expr.trueLit then
    ⟨.surface, Quellform.statements trueLitForm trueLitJoint constructor⟩
  else if constructor = ``Expr.falseLit then
    ⟨.surface, Quellform.statements falseLitForm falseLitJoint constructor⟩
  else if constructor = ``Expr.variable then
    ⟨.surface, Quellform.statements variableForm variableJoint constructor⟩
  else if constructor = ``Expr.negativeLit then
    ⟨.surface, Quellform.statements negativeLitForm negativeLitJoint constructor⟩
  else if constructor = ``Expr.neg then
    ⟨.surface, Quellform.statements negForm negJoint constructor⟩
  else if constructor = ``Expr.not then
    ⟨.surface, Quellform.statements notValueForm notValueJoint constructor⟩
  else if constructor = ``Expr.div then
    ⟨.surface, Quellform.statements divisionForm divisionJoint constructor⟩
  else if constructor = ``Expr.compare then
    ⟨.surface, Quellform.statements comparisonForm comparisonJoint constructor⟩
  else if constructor = ``Expr.logic then
    ⟨.surface, Quellform.statements logicForm logicJoint constructor⟩
  else if constructor = ``Expr.arrayValue then
    ⟨.surface, Quellform.statements arrayValueForm ArrayValueErfuellbarAmAussage constructor⟩
  else if constructor = ``Expr.arrayIndex then
    ⟨.surface, Quellform.statements arrayIndexForm ArrayIndexErfuellbarAmAussage constructor⟩
  else if constructor = ``Expr.tupleValue then
    ⟨.surface, Quellform.statements tupleValueForm TupleValueErfuellbarAmAussage constructor⟩
  else if constructor = ``Expr.tupleField then
    ⟨.surface, Quellform.statements tupleFieldForm TupleFieldErfuellbarAmAussage constructor⟩
  else nichtSpezifiziert constructor

def stmtSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Stmt.letValue then
    ⟨.surface, Quellform.statements letForm LetErfuellbar constructor⟩
  else if constructor = ``Stmt.assignVar then
    ⟨.surface, Quellform.statements assignVarForm assignVarJoint constructor⟩
  else if constructor = ``Stmt.ret then
    ⟨.surface, Quellform.statements returnValueForm returnValueJoint constructor⟩
  else if constructor = ``Stmt.ite then
    ⟨.surface, Quellform.statements ifElseForm ifElseJoint constructor⟩
  else if constructor = ``Stmt.retVoid then
    ⟨.surface, Quellform.statements (Context := PUnit) (fun _ => returnVoidForm [] none) returnVoidJoint constructor⟩
  else if constructor = ``Stmt.letMutable then
    ⟨.surface, Quellform.statements (fun (ctx : StatementContext) => mutableLocalForm ctx.1 ctx.2) mutableLocalJoint constructor⟩
  else if constructor = ``Stmt.directCall then
    ⟨.surface, Quellform.statements (fun (ctx : StatementContext) => directCallForm ctx.1 ctx.2) directCallJoint constructor⟩
  else if constructor = ``Stmt.bindDirect then
    ⟨.surface, Quellform.statements (fun (ctx : StatementContext) => bindDirectForm ctx.1 ctx.2) bindDirectJoint constructor⟩
  else if constructor = ``Stmt.whileBounded then
    ⟨.surface, Quellform.statements (fun (ctx : StatementContext) => boundedWhileForm ctx.1 ctx.2) boundedWhileJoint constructor⟩
  else if constructor = ``Stmt.forRange then
    ⟨.surface, Quellform.statements (fun (ctx : StatementContext) => forRangeForm ctx.1 ctx.2) forRangeJoint constructor⟩
  else nichtSpezifiziert constructor

def declSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Decl.constant then
    ⟨.surface, Quellform.statements constantForm constantJoint constructor⟩
  else if constructor = ``Decl.function then
    ⟨.surface, Quellform.statements functionForm functionJoint constructor⟩
  else nichtSpezifiziert constructor

def bracedSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``BracedBlock.braces then
    ⟨.surface, Quellform.statements bracedForm bracedJoint constructor⟩
  else nichtSpezifiziert constructor

end Gabbro.Core.Ast.Semantik
