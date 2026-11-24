module

public import Core.Ast.Semantik.Quellform

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter
open Lean (Name)

def literalForm (scope : Scope) : Quellform (.expression scope .integer) Nat where
  produktion := Surface.literal scope
  befehl := .literal 0
  position := fun _ => 0

def binaryForm (scope : Scope) :
    Quellform (.expression scope .integer) (Surface.BinaryArgs scope) where
  produktion := Surface.binary scope
  befehl := fun args => .binaer args.op 0
  position := fun args => (((expr 0 args.left).anhaengen (expr 1 args.right)).code).length

def letForm (scope : Scope) : Quellform (.statement scope) (Surface.LetArgs scope) where
  produktion := Surface.letValue scope
  befehl := fun args => .binden args.name 0
  position := fun args => (expr 0 args.value).code.length

def LiteralErfuellbar : Prop :=
  ∀ start, ∃ value, (literalForm []).ErfuellbarAm .x86_64 start value

def BinaryErfuellbar : Prop :=
  ∀ start op, ∃ args : Surface.BinaryArgs [], args.op = op ∧
    (binaryForm []).ErfuellbarAm .x86_64 start args

def LetErfuellbar : Prop :=
  ∀ start, ∃ args, (letForm []).ErfuellbarAm .x86_64 start args

/-- Missing constructor specifications yield an uninhabitable registry entry. -/
def nichtSpezifiziert (constructor : Name) : RegistrySchema constructor :=
  ⟨.core, ⟨.core False, False, False, False, False, False, False⟩⟩

def exprSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Expr.lit then ⟨.surface, Quellform.statements literalForm LiteralErfuellbar constructor⟩
  else if constructor = ``Expr.binary then
    ⟨.surface, Quellform.statements binaryForm BinaryErfuellbar constructor⟩
  else nichtSpezifiziert constructor

def stmtSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Stmt.letValue then ⟨.surface, Quellform.statements letForm LetErfuellbar constructor⟩
  else nichtSpezifiziert constructor

end Gabbro.Core.Ast.Semantik
