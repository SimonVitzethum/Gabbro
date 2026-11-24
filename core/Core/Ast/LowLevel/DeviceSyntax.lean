module

public import Core.Ast.LowLevel.Device
public import Core.Ast.LowLevel.Syntax
public import Core.Ast.Semantik.Arithmetik

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Gabbro.Core.Text Katalog Maschine

structure RegisterName where
  device : Identifier
  field : Identifier

def RegisterName.tokens (name : RegisterName) : List Token :=
  [.word name.device.val, dot, .word name.field.val]

def RegisterName.printPieces (name : RegisterName) : List PrintedToken :=
  [name.device.print, printDot, name.field.print]

/-- The source carries names and a typed value expression. Offsets, register
    classes, promises, and device identity come from the selected declaration. -/
inductive Source (scope : Scope) where
  | read (destination : Identifier) (register : RegisterName)
  | fallibleRead (destination : Identifier) (register : RegisterName) (handler : Identifier)
  | write (register : RegisterName) (value : Expr scope (.int lo hi))
  | transition (name : Identifier)

def Source.printPieces : Source scope → List PrintedToken
  | .read destination register =>
    [letName.print, destination.print, printAssignment] ++ register.printPieces ++ [printSemicolon]
  | .fallibleRead destination register handler =>
    [letName.print, destination.print, printAssignment] ++ register.printPieces ++
      [lowWord 'e' "lse", handler.print, printSemicolon]
  | .write register value =>
    register.printPieces ++ [printDot, lowWord 'w' "rite", printOpen] ++
      value.printPieces ++ [printClose, printSemicolon]
  | .transition name => [lowWord 't' "ransition", name.print, printSemicolon]

inductive Reads (scope : Scope) : List Token → Source scope → Prop where
  | read (destination : Identifier) (register : RegisterName) :
    Reads scope ([letKeyword, .word destination.val, assignment] ++ register.tokens ++ [semicolon])
      (.read destination register)
  | fallibleRead (destination : Identifier) (register : RegisterName) (handler : Identifier) :
    Reads scope ([letKeyword, .word destination.val, assignment] ++ register.tokens ++
      [keyword "else", .word handler.val, semicolon]) (.fallibleRead destination register handler)
  | write (register : RegisterName) :
    ExprReads scope 0 input (value : Expr scope (.int lo hi)) [closeParen, semicolon] →
    Reads scope (register.tokens ++ [dot, keyword "write", openParen] ++ input)
      (.write register value)
  | transition (name : Identifier) :
    Reads scope [keyword "transition", .word name.val, semicolon] (.transition name)

def Parse (text : RawText) (tree : Source scope) : Prop :=
  Text.Parse (tokenGrammar (Reads scope)) text tree

/-- A declaration contributes only names selected from the same device row. -/
structure RegisterDeclaration (k : Katalog) where
  binding : Binding k
  row : Register
  described : binding.row.register row.offset = some row
  promise : Option ReadRange

structure TransitionDeclaration (k : Katalog) where
  binding : Binding k
  row : Register
  described : binding.row.register row.offset = some row
  data : Nat
  legal : row.write = true ∧ data < row.grenze
  changes : RegisterTransition k binding

structure SourceScope (k : Katalog) where
  register : RegisterName → Option (RegisterDeclaration k)
  transition : Identifier → Option (TransitionDeclaration k)

inductive Denotation (k : Katalog) (scope : Scope) where
  | read (destination : Identifier) (binding : Binding k) (offset : Nat)
  | fallibleRead (destination : Identifier) (binding : Binding k) (offset : Nat) (promise : ReadRange)
      (handler : Identifier)
  | write (binding : Binding k) (offset : Nat) (value : Expr scope (.int lo hi))
  | transition (decl : TransitionDeclaration k)

def elaborate (names : SourceScope k) : Source scope → Option (Denotation k scope)
  | .read destination reg => do
    let desc ← names.register reg
    if desc.row.read && desc.promise.isNone then some (.read destination desc.binding desc.row.offset) else none
  | .fallibleRead destination reg handler => do
    let desc ← names.register reg
    let range ← desc.promise
    if desc.row.read then some (.fallibleRead destination desc.binding desc.row.offset range handler) else none
  | .write (lo := lo) (hi := hi) reg expression => do
    let desc ← names.register reg
    if desc.row.write && decide (0 ≤ lo ∧ hi < (desc.row.grenze : Int)) then
      some (.write desc.binding desc.row.offset expression)
    else none
  | .transition name => (names.transition name).map .transition

def Denotation.rule (locals : Ast.Umgebung scope) : Denotation k scope → Regel State Plan PUnit
  | .read _ binding offset => registerRule binding (.read offset)
  | .fallibleRead _ binding offset promise _ => registerRule binding (.fallibleRead offset promise)
  | .write binding offset value => registerRule binding (.write offset (value.wert locals).wert.toNat)
  | .transition decl => transitionRule decl.binding decl.row.offset decl.data decl.changes

inductive Continuation where
  | bind (destination : Identifier) (value : Nat)
  | branch (handler : Identifier)
  | proceed
  | failure (result : Result)

def Denotation.resume (denotation : Denotation k scope) (result : Result) : Continuation :=
  match denotation, result with
  | .read destination _ _, .value value
  | .fallibleRead destination _ _ _ _, .value value => .bind destination value
  | .fallibleRead _ _ _ _ handler, .readOutOfRange _
  | .fallibleRead _ _ _ _ handler, .refused _ => .branch handler
  | .write .., .written | .transition _, .written => .proceed
  | _, _ => .failure result

end Gabbro.Core.Ast.LowLevel.Device

