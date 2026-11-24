module

public import Core.Ast.Tree
public import Core.Text.Token

@[expose] public section

namespace Gabbro.Core.Ast.ProbeTwo

open Gabbro.Core.Text

def minusP : Token := .punctuation ['-']
def bangP : Token := .punctuation ['.']
def trueKeywordP : Token := .word "true".toList
def falseKeywordP : Token := .word "false".toList

def PrimaryStart (tokens : List Token) : Prop := ∀ tail, tokens ≠ minusP :: tail ∧ tokens ≠ bangP :: tail
def NegationStart (tokens : List Token) : Prop := PrimaryStart tokens ∧ ∀ n tail, tokens ≠ .natural n :: tail

mutual
inductive ExprReads (scope : Scope) : Nat → List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | atom : AtomReads scope input first more → ExprTail scope minimum first more tree rest → ExprReads scope minimum input tree rest
inductive AtomReads (scope : Scope) : List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | lit : AtomReads scope (.natural value :: rest) (.lit value) rest
  | trueLit : AtomReads scope (trueKeywordP :: rest) .trueLit rest
  | falseLit : AtomReads scope (falseKeywordP :: rest) .falseLit rest
  | variable (ref : Local scope type) (visible : ref.visible) (ordinary : ordinaryLocal ref.binding.name) :
      AtomReads scope (.word ref.binding.name.val :: rest) (.variable ref visible ordinary) rest
  | neg : NegationStart input → AtomReads scope input operand rest → AtomReads scope (minusP :: input) (.neg operand) rest
inductive ExprTail (scope : Scope) : Nat → {inputType : Ty .value} → Expr scope inputType → List Token → {resultType : Ty .value} → Expr scope resultType → List Token → Prop where
  | stop : ¬ True → ExprTail scope minimum left rest left rest
end

theorem probe (ordinary : word ≠ "true".toList ∧ word ≠ "false".toList)
    (read : AtomReads scope (.word word :: rest) tree suffix) :
    ∃ (ref : Local scope type) (visible : ref.visible) (o : ordinaryLocal ref.binding.name),
      ref.binding.name.val = word ∧ tree.typed = (Expr.variable ref visible o).typed ∧ suffix = rest := by
  cases read with
  | trueLit => exact (ordinary.1 rfl).elim
  | falseLit => exact (ordinary.2 rfl).elim
  | `variable ref vis ord => exact ⟨ref, vis, ord, rfl, rfl, rfl⟩
  | _ => cases read

end Gabbro.Core.Ast.ProbeTwo
