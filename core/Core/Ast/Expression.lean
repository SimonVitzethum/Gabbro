module

public import Core.Ast.Tree

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def Arith.token : Arith → Token
  | .add => .punctuation ['+']
  | .mul => .punctuation ['*']

def Arith.precedence : Arith → Nat
  | .add => 1
  | .mul => 2

theorem Arith.token_injective {a b : Arith} (same : a.token = b.token) : a = b := by
  cases a <;> cases b <;> first | rfl | cases same

def openParen : Token := .punctuation ['(']
def closeParen : Token := .punctuation [')']
def semicolon : Token := .punctuation [';']
def openBrace : Token := .punctuation ['{']
def closeBrace : Token := .punctuation ['}']
def assignment : Token := .punctuation ['=']
def letKeyword : Token := .word ['l', 'e', 't']

def Continues (minimum : Nat) (input : List Token) : Prop :=
  ∃ op : Arith, ∃ more, input = op.token :: more ∧ minimum ≤ op.precedence

theorem noOperatorAtEnd : ¬ Continues minimum [] := by
  rintro ⟨op, more, equality, _⟩
  cases equality

theorem noOperatorAtClose : ¬ Continues minimum (closeParen :: more) := by
  rintro ⟨op, _, equality, _⟩
  have head := (List.cons.inj equality).1
  cases op <;> cases head

theorem noOperatorAtSemicolon : ¬ Continues minimum (semicolon :: more) := by
  rintro ⟨op, _, equality, _⟩
  have head := (List.cons.inj equality).1
  cases op <;> cases head

mutual

/-- An expression consumes an atom and its maximal continuation at the given precedence. -/
inductive ExprReads (scope : Scope) :
    Nat → List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | atom : AtomReads scope input first more → ExprTail scope minimum first more tree rest →
      ExprReads scope minimum input tree rest

/-- Atom rules own their leading token. Parentheses group an expression without adding an AST node. -/
inductive AtomReads (scope : Scope) :
    List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | lit : AtomReads scope (.natural value :: rest) (.lit value) rest
  | grouped : ExprReads scope 0 input tree (closeParen :: rest) →
      AtomReads scope (openParen :: input) tree rest

/-- Higher-precedence operators stay in the right operand. A same-precedence operator
    belongs to the outer continuation, giving left associativity. -/
inductive ExprTail (scope : Scope) :
    Nat → {type : Ty .value} → Expr scope type → List Token → Expr scope type → List Token → Prop where
  | stop : ¬ Continues minimum rest → ExprTail scope minimum left rest left rest
  | binary (op : Arith) : minimum ≤ op.precedence →
      ExprReads scope (op.precedence + 1) input right more →
      ExprTail scope minimum (.binary op left right) more tree rest →
      ExprTail scope minimum left (op.token :: input) tree rest

end

/-- Inverting the atom production recovers both the literal and its complete suffix. -/
theorem AtomReads.lit_inversion
    (read : AtomReads scope (.natural value :: rest) tree suffix) :
    tree = .lit value ∧ suffix = rest := by
  cases read
  exact ⟨rfl, rfl⟩

/-- One precedence proof for all registered infix operators. Adding an operator
    only extends the token and precedence tables and the token injectivity proof. -/
theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
    (right : ExprReads scope minimum input b rest') : a = b ∧ rest = rest' := by
  revert b rest'
  refine ExprReads.rec
    (motive_1 := fun min input _ a rest _ =>
      ∀ {b rest'}, ExprReads scope min input b rest' → a = b ∧ rest = rest')
    (motive_2 := fun input _ a rest _ =>
      ∀ {b rest'}, AtomReads scope input b rest' → a = b ∧ rest = rest')
    (motive_3 := fun min _ first input a rest _ =>
      ∀ {b rest'}, ExprTail scope min first input b rest' → a = b ∧ rest = rest')
    ?_ ?_ ?_ ?_ ?_ left
  · intro _ _ _ _ _ _ _ _ _ atomDet tailDet _ _ other
    cases other with
    | atom atom tail =>
      obtain ⟨rfl, rfl⟩ := atomDet atom
      exact tailDet tail
  · intro _ _ _ _ other
    obtain ⟨rfl, rfl⟩ := other.lit_inversion
    exact ⟨rfl, rfl⟩
  · intro _ _ _ _ _ insideDet _ _ other
    cases other with
    | grouped inside =>
      obtain ⟨same, suffix⟩ := insideDet inside
      exact ⟨same, (List.cons.inj suffix).2⟩
  · intro _ _ _ _ blocked _ _ other
    cases other with
    | stop => exact ⟨rfl, rfl⟩
    | binary op allowed => exact (blocked ⟨op, _, rfl, allowed⟩).elim
  · intro _ input _ _ _ _ _ op allowed _ _ operandDet tailDet _ _ other
    generalize h : op.token = token at other
    cases other with
    | stop blocked => exact (blocked ⟨op, input, congrArg (· :: input) h.symm, allowed⟩).elim
    | binary op' _ operand tail =>
      have same := Arith.token_injective h
      subst op'
      obtain ⟨rfl, rfl⟩ := operandDet operand
      exact tailDet tail

/-- The suffix index delimits an exact source slice, including for grouped and infix children. -/
theorem ExprReads.consumes (read : ExprReads scope minimum input tree rest) : rest <:+ input := by
  refine ExprReads.rec
    (motive_1 := fun _ input _ _ rest _ => rest <:+ input)
    (motive_2 := fun input _ _ rest _ => rest <:+ input)
    (motive_3 := fun _ _ _ input _ rest _ => rest <:+ input)
    ?_ ?_ ?_ ?_ ?_ read
  · intro _ _ _ _ _ _ _ _ _ atom tail
    exact tail.trans atom
  · intro _ _
    exact List.suffix_cons _ _
  · intro input _ _ rest _ child
    exact ((List.suffix_cons closeParen rest).trans child).trans (List.suffix_cons openParen input)
  · intro _ rest _ _ _
    exact List.suffix_refl rest
  · intro _ input _ _ _ _ _ op _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons op.token input)

end Gabbro.Core.Ast
