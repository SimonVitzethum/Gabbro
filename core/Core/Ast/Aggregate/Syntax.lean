module

public import Core.Ast.Aggregate.Surface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

def ArrayValueInversionAussage : Prop :=
  ∀ {scope input type} {tree : Expr scope type} {rest},
    AtomReads scope (openBracket :: input) tree rest →
    ∃ (args : ArrayValueArgs scope), ItemsRead scope closeBracket input args.items rest ∧
      tree.typed = args.expression.typed

def ArrayValueSuffixAussage : Prop :=
  ∀ {scope input type} {tree : Expr scope type} {rest},
    AtomReads scope (openBracket :: input) tree rest → rest <:+ input

def ArrayValueDerivationAussage : Prop :=
  ∀ scope, (arrayValue scope).Entry

def ArrayValueElementSoundAussage : Prop :=
  ∀ {types element}, arrayElement types = some element →
    ∀ i : Fin types.length, Fits (types.get i) element

def ArrayIndexInversionAussage : Prop :=
  ∀ {scope element count minimum input type}
    {base : Expr scope (.array element count)} {tree : Expr scope type} {rest},
    minimum ≤ Infix.index.precedence →
    ExprTail scope minimum base (openBracket :: input) tree rest →
    ∃ (lo hi : Int) (i : Expr scope (.int lo hi)) (more : List Token)
      (lower : 0 ≤ lo) (upper : hi < (count : Int)),
      ExprReads scope 0 input i (closeBracket :: more) ∧
      ExprTail scope minimum (.arrayIndex base i lower upper) more tree rest

def ArrayIndexSuffixAussage : Prop :=
  ∀ {scope element count minimum input type}
    {base : Expr scope (.array element count)} {tree : Expr scope type} {rest},
    minimum ≤ Infix.index.precedence →
    ExprTail scope minimum base (openBracket :: input) tree rest → rest <:+ input

def ArrayIndexDerivationAussage : Prop :=
  ∀ scope, (arrayIndex scope).Entry

def TupleValueInversionAussage : Prop :=
  ∀ {scope input type firstType secondInput} {tree : Expr scope type} {rest}
    {first : Expr scope firstType},
    ExprReads scope 0 input first (comma :: secondInput) →
    AtomReads scope (openParen :: input) tree rest →
    ∃ (args : TupleValueArgs scope) (more : List Token),
      first.typed = args.first.typed ∧ ExprReads scope 0 secondInput args.second more ∧
      ItemsTail scope closeParen more args.tail rest ∧ tree.typed = args.expression.typed

def TupleValueSuffixAussage : Prop :=
  ∀ {scope input types} {items : ExprItems scope types} {rest},
    ItemsTail scope closeParen input items rest → rest <:+ input

def TupleValueDerivationAussage : Prop :=
  ∀ scope, (tupleValue scope).Entry

def TupleFieldInversionAussage : Prop :=
  ∀ {scope first second types minimum n input type}
    {base : Expr scope (tupleType (first :: second :: types))} {tree : Expr scope type} {rest},
    minimum ≤ Infix.projection.precedence →
    ExprTail scope minimum base (dot :: .natural n :: input) tree rest →
    ∃ i : Fin (first :: second :: types).length, i.val = n ∧
      ExprTail scope minimum (.tupleField base i) input tree rest

def TupleFieldSuffixAussage : Prop :=
  ∀ {scope first second types minimum n input type}
    {base : Expr scope (tupleType (first :: second :: types))} {tree : Expr scope type} {rest},
    minimum ≤ Infix.projection.precedence →
    ExprTail scope minimum base (dot :: .natural n :: input) tree rest → rest <:+ input

def TupleFieldDerivationAussage : Prop :=
  ∀ scope, (tupleField scope).Entry

end Gabbro.Core.Ast.Surface
