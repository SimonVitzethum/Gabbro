module

public import Core.Ast.Tree
public import Core.Text.Token

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def openParenP : Token := .punctuation ['(']
def closeParenP : Token := .punctuation [')']
def semicolonP : Token := .punctuation [';']
def openBraceP : Token := .punctuation ['{']
def closeBraceP : Token := .punctuation ['}']
def assignmentP : Token := .punctuation ['=']
def letKeywordP : Token := .word "let".toList
def trueKeywordP : Token := .word "true".toList
def falseKeywordP : Token := .word "false".toList
def minusP : Token := .punctuation ['-']
def bangP : Token := .punctuation ['!']

def Arith.token : Arith → Token
  | .add => .punctuation ['+']
  | .mul => .punctuation ['*']
  | .sub => .punctuation ['-']
def Arith.precedence : Arith → Nat | .add | .sub => 5 | .mul => 6
def Compare.spelling : Compare → String | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
def Logic.spelling : Logic → String | .and => "&&" | .or => "||"

inductive Infix where | arith (op : Arith) | div | compare (op : Compare) | logic (op : Logic)
def Infix.token : Infix → Token
  | .arith op => op.token | .div => .punctuation ['/'] | .compare op => .punctuation op.spelling.toList | .logic op => .punctuation op.spelling.toList
def Infix.precedence : Infix → Nat | .arith op => op.precedence | .div => 6 | .compare _ => 3 | .logic .and => 2 | .logic .or => 1
def Infix.follows : Infix → List Token → Prop | .compare _, rest => ∀ op tail, rest ≠ Infix.token (.compare op) :: tail | _, _ => True

def Continues (minimum : Nat) (input : List Token) : Prop := ∃ op : Infix, ∃ more, input = op.token :: more ∧ minimum ≤ op.precedence
def PrimaryStart (tokens : List Token) : Prop := ∀ tail, tokens ≠ minusP :: tail ∧ tokens ≠ bangP :: tail
def NegationStart (tokens : List Token) : Prop := PrimaryStart tokens ∧ ∀ n tail, tokens ≠ .natural n :: tail

mutual
inductive ExprReads (scope : Scope) : Nat → List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | atom : AtomReads scope input first more → ExprTail scope minimum first more tree rest → ExprReads scope minimum input tree rest
inductive AtomReads (scope : Scope) : List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | lit : AtomReads scope (.natural value :: rest) (.lit value) rest
  | grouped : ExprReads scope 0 input tree (closeParenP :: rest) → AtomReads scope (openParenP :: input) tree rest
  | trueLit : AtomReads scope (trueKeywordP :: rest) .trueLit rest
  | falseLit : AtomReads scope (falseKeywordP :: rest) .falseLit rest
  | variable (ref : Local scope type) (visible : ref.visible) (ordinary : ordinaryLocal ref.binding.name) : AtomReads scope (.word ref.binding.name.val :: rest) (.variable ref visible ordinary) rest
  | negativeLit : AtomReads scope (minusP :: .natural value :: rest) (.negativeLit value) rest
  | neg : NegationStart input → AtomReads scope input operand rest → AtomReads scope (minusP :: input) (.neg operand) rest
  | not : PrimaryStart input → AtomReads scope input operand rest → AtomReads scope (bangP :: input) (.not operand) rest
inductive ExprTail (scope : Scope) : Nat → {inputType : Ty .value} → Expr scope inputType → List Token → {resultType : Ty .value} → Expr scope resultType → List Token → Prop where
  | stop : ¬ Continues minimum rest → ExprTail scope minimum left rest left rest
  | binary (op : Arith) : minimum ≤ op.precedence → ExprReads scope (op.precedence + 1) input right more → ExprTail scope minimum (.binary op left right) more tree rest → ExprTail scope minimum left (op.token :: input) tree rest
  | div : minimum ≤ Infix.div.precedence → ExprReads scope (Infix.div.precedence + 1) input (right : Expr scope (.int lo hi)) more → (nonzero : Divisor lo hi) → ExprTail scope minimum (.div left right nonzero) more tree rest → ExprTail scope minimum left (Infix.div.token :: input) tree rest
  | compare (op : Compare) : minimum ≤ (Infix.compare op).precedence → ExprReads scope ((Infix.compare op).precedence + 1) input right more → (Infix.compare op).follows more → ExprTail scope minimum (.compare op left right) more tree rest → ExprTail scope minimum left ((Infix.compare op).token :: input) tree rest
  | logic (op : Logic) : minimum ≤ (Infix.logic op).precedence → ExprReads scope ((Infix.logic op).precedence + 1) input right more → ExprTail scope minimum (.logic op left right) more tree rest → ExprTail scope minimum left ((Infix.logic op).token :: input) tree rest
end

theorem probe_det (left : ExprReads scope minimum input a rest) : True := by
  refine ExprReads.rec
    (motive_1 := fun min input _ a rest _ => True)
    (motive_2 := fun input _ a rest _ => True)
    (motive_3 := fun min _ first input _ a rest _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  all_goals trace_state; trivial

theorem probe_atom_inv (read : AtomReads scope (trueKeywordP :: rest) tree suffix) : True := by
  cases read <;> trace_state <;> trivial

theorem probe_tail_inv (read : ExprTail scope minimum (left : Expr scope (.int lo₁ hi₁)) (op.token :: input) tree rest) : True := by
  cases read <;> trace_state <;> trivial

end Gabbro.Core.Ast
