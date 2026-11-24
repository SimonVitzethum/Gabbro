module

public import Core.Ast.Aggregate.Types

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

def textLiteral (scope : Scope) : Rule (.expression scope) (List Char) where
  tree := fun decoded => (Expr.textLiteral decoded).typed
  production := fun decoded tokens => tokens = [.string decoded]

structure TextConcatArgs (scope : Scope) where
  a : Nat
  b : Nat
  left : Expr scope (.text a)
  right : Expr scope (.text b)

def TextConcatArgs.expression (arg : TextConcatArgs scope) : Expr scope (.text (arg.a + arg.b)) :=
  .textConcat arg.left arg.right

def textConcat (scope : Scope) : Rule (.expression scope) (TextConcatArgs scope) where
  tree := fun arg => arg.expression.typed
  production := fun arg => postfixProduction fun input rest =>
    ∃ rhs, ExprReads scope (Arith.add.precedence + 1) input arg.left (Arith.add.token :: rhs) ∧
      ExprReads scope (Arith.add.precedence + 1) rhs arg.right rest

structure TextIndexArgs (scope : Scope) where
  capacity : Nat
  lo : Int
  hi : Int
  base : Expr scope (.text capacity)
  offset : Expr scope (.int lo hi)

def TextIndexArgs.expression (arg : TextIndexArgs scope) : Expr scope (.int 0 255) :=
  .textIndex arg.base arg.offset

def textIndex (scope : Scope) : Rule (.expression scope) (TextIndexArgs scope) where
  tree := fun arg => arg.expression.typed
  production := fun arg => postfixProduction fun input rest =>
    ∃ offset, ExprReads scope 8 input arg.base (openBracket :: offset) ∧
      ExprReads scope 0 offset arg.offset (closeBracket :: rest)

structure SubstringArgs (scope : Scope) where
  capacity : Nat
  firstLo : Int
  firstHi : Int
  lastLo : Int
  lastHi : Int
  base : Expr scope (.text capacity)
  first : Expr scope (.int firstLo firstHi)
  last : Expr scope (.int lastLo lastHi)

def SubstringArgs.expression (arg : SubstringArgs scope) : Expr scope (.text arg.capacity) :=
  .substring arg.base arg.first arg.last

def substring (scope : Scope) : Rule (.expression scope) (SubstringArgs scope) where
  tree := fun arg => arg.expression.typed
  production := fun arg => postfixProduction fun input rest =>
    ∃ first last, ExprReads scope 8 input arg.base (openBracket :: first) ∧
      ExprReads scope 0 first arg.first (sliceRange :: last) ∧
      ExprReads scope 0 last arg.last (closeBracket :: rest)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

def textLiteralForm (scope : Scope) : Quellform (.expression scope) (List Char) where
  produktion := Surface.textLiteral scope
  befehl := .textLiteral 0
  position := fun _ => 0

def textConcatForm (scope : Scope) : Quellform (.expression scope) (Surface.TextConcatArgs scope) where
  produktion := Surface.textConcat scope
  befehl := fun a => .textConcat 0 a.a a.b
  position := fun a => (expr 0 a.left).code.length + (expr 1 a.right).code.length

def textIndexForm (scope : Scope) : Quellform (.expression scope) (Surface.TextIndexArgs scope) where
  produktion := Surface.textIndex scope
  befehl := fun a => .textIndex 0 a.capacity
  position := fun a => (expr 0 a.base).code.length + (expr 1 a.offset).code.length

def substringForm (scope : Scope) : Quellform (.expression scope) (Surface.SubstringArgs scope) where
  produktion := Surface.substring scope
  befehl := fun a => .substring 0 a.capacity
  position := fun a => (expr 0 a.base).code.length + (expr 1 a.first).code.length + (expr 2 a.last).code.length

def textTypeUse : WrittenType → Prop
  | .text _ => True
  | _ => False

/-- Local forms have no outside answer action and never commit an answer in
    their own trace. Environmental arrivals are separate machine steps. -/
def RegelAntwortSicher (p : Fragment) (platform : Plattform) (b : Befehl) : Prop :=
  ∀ t c s (choice : PUnit) stepPlan u spur next,
    (p.einheit platform).system.kopf s c = some b →
    (b.regel).impl c s choice [stepPlan] u →
    FuehrtSchrittAus (p.einheit platform).einrichtung t c s u stepPlan spur next →
    (∀ answer : AntwortEreignis, stepPlan.aktion ≠ .verbrauche answer) ∧
      ∀ answer : AntwortEreignis, Ereignis.antwort answer ∉ spur.aussen

/-- M9's observable data at the source instruction. The two trace projections
    are empty and the logical instruction contributes one unit of work. -/
def TextInstructionCost (p : Fragment) (platform : Plattform) (b : Befehl) : Prop :=
  ∀ t c s (choice : PUnit) stepPlan u spur next,
    (p.einheit platform).system.kopf s c = some b →
    (b.regel).impl c s choice [stepPlan] u →
    FuehrtSchrittAus (p.einheit platform).einrichtung t c s u stepPlan spur next →
    spur.speicher = [] ∧ spur.aussen = [] ∧
      (p.einheit platform).stotterLaenge b + [stepPlan].length = 1

/-- The joint case visits the instruction and produces a live result. A
    rejecting guard or a source that stops before the form cannot inhabit it. -/
def Quellform.TextErfuellbar (form : Quellform category Args) (platform : Plattform)
    (start : AussenStart) (args : Args) : Prop :=
  let E := form.einheit platform args
  let b := form.befehl args
  ∃ (text : Text.RawText) (s : Zustand),
    Ast.Parse text (form.produktion.tree args) ∧ Elaboriert platform (form.produktion.tree args) E ∧
    E.system.IErreichbar (I.start E start).2 s ∧ Realisiert form platform args s ∧
    (∀ g : Bedarf, b.guard (s.lokal eintritt) = some g → Annahme.waechterBedarf g.1 g.2) ∧
    let next := b.nach eintritt s
    (next.lokal eintritt).stopp = none ∧ ((next.lokal eintritt).temp 0).isSome = true

end Gabbro.Core.Ast.Semantik
