module

public import Core.Ast.Tree

@[expose] public section

namespace Gabbro.Core.Ast.Probe

open Gabbro.Core.Text

def Arith.token : Arith → Token
  | .add => .punctuation ['+']
  | .mul => .punctuation ['*']
  | .sub => .punctuation ['-']

def Arith.precedence : Arith → Nat
  | .add | .sub => 5
  | .mul => 6

theorem Arith.token_injective {a b : Arith} (same : a.token = b.token) : a = b := by
  cases a <;> cases b <;> first | rfl | cases same

def Compare.spelling : Compare → String
  | .eq => "=="
  | .ne => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

def Logic.spelling : Logic → String
  | .and => "&&"
  | .or => "||"

def openParen : Token := .punctuation ['(']
def closeParen : Token := .punctuation [')']
def semicolon : Token := .punctuation [';']
def openBrace : Token := .punctuation ['{']
def closeBrace : Token := .punctuation ['}']
def assignment : Token := .punctuation ['=']
def letKeyword : Token := .word "let".toList
def trueKeyword : Token := .word "true".toList
def falseKeyword : Token := .word "false".toList
def ifKeyword : Token := .word "if".toList
def elseKeyword : Token := .word "else".toList
def returnKeyword : Token := .word "return".toList
def minus : Token := .punctuation ['-']
def bang : Token := .punctuation ['!']

inductive Infix where
  | arith (op : Arith)
  | div
  | compare (op : Compare)
  | logic (op : Logic)

def Infix.token : Infix → Token
  | .arith op => op.token
  | .div => .punctuation ['/']
  | .compare op => .punctuation op.spelling.toList
  | .logic op => .punctuation op.spelling.toList

def Infix.precedence : Infix → Nat
  | .arith op => op.precedence
  | .div => 6
  | .compare _ => 3
  | .logic .and => 2
  | .logic .or => 1

def Infix.follows : Infix → List Token → Prop
  | .compare _, rest => ∀ op tail, rest ≠ Infix.token (.compare op) :: tail
  | _, _ => True

-- Mirror Arith.token_injective across the four operator families.
theorem Infix.token_injective {a b : Infix} (same : a.token = b.token) : a = b := by
  cases a with
  | arith op =>
    cases b with
    | arith op' => exact congrArg Infix.arith (Arith.token_injective (by simpa only [Infix.token] using same))
    | div => cases op <;> cases same
    | compare op' => cases op <;> cases op' <;> cases same
    | logic op' => cases op <;> cases op' <;> cases same
  | div =>
    cases b with
    | arith op => cases op <;> cases same
    | div => rfl
    | compare op' => cases op' <;> cases same
    | logic op' => cases op' <;> cases same
  | compare op =>
    cases b with
    | arith op' => cases op <;> cases op' <;> cases same
    | div => cases op <;> cases same
    | compare op' => exact congrArg Infix.compare (by
        cases op <;> cases op' <;> first | rfl | cases same)
    | logic op' => cases op <;> cases op' <;> cases same
  | logic op =>
    cases b with
    | arith op' => cases op <;> cases op' <;> cases same
    | div => cases op <;> cases same
    | compare op' => cases op <;> cases op' <;> cases same
    | logic op' => exact congrArg Infix.logic (by
        cases op <;> cases op' <;> first | rfl | cases same)

def Continues (minimum : Nat) (input : List Token) : Prop :=
  ∃ op : Infix, ∃ more, input = op.token :: more ∧ minimum ≤ op.precedence

theorem noOperatorAtEnd : ¬ Continues minimum [] := by
  rintro ⟨op, more, equality, _⟩
  cases equality

-- Mirror the arithmetic case of noOperatorAtClose for the new token families.
theorem noOperatorAtClose : ¬ Continues minimum (closeParen :: more) := by
  rintro ⟨op, tail, equality, _⟩
  have head := (List.cons.inj equality).1
  cases op with
  | arith a => cases a <;> cases head
  | div => cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head

-- Mirror noOperatorAtClose.
theorem noOperatorAtSemicolon : ¬ Continues minimum (semicolon :: more) := by
  rintro ⟨op, tail, equality, _⟩
  have head := (List.cons.inj equality).1
  cases op with
  | arith a => cases a <;> cases head
  | div => cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head

-- Mirror noOperatorAtClose.
theorem noOperatorAtOpenBrace : ¬ Continues minimum (openBrace :: more) := by
  rintro ⟨op, tail, equality, _⟩
  have head := (List.cons.inj equality).1
  cases op with
  | arith a => cases a <;> cases head
  | div => cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head

/-- The operand of a single unary prefix starts at a primary. -/
def PrimaryStart (tokens : List Token) : Prop :=
  ∀ tail, tokens ≠ minus :: tail ∧ tokens ≠ bang :: tail

/-- Minus followed by a numeral belongs to the negative-literal production. -/
def NegationStart (tokens : List Token) : Prop :=
  PrimaryStart tokens ∧ ∀ n tail, tokens ≠ .natural n :: tail

mutual

/-- An expression consumes an atom and its maximal continuation at the given precedence. -/
inductive ExprReads (scope : Scope) :
    Nat → List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | atom : AtomReads scope input first more → ExprTail scope minimum first more tree rest →
      ExprReads scope minimum input tree rest

/-- Parentheses group an expression without adding an AST node. -/
inductive AtomReads (scope : Scope) :
    List Token → {type : Ty .value} → Expr scope type → List Token → Prop where
  | lit : AtomReads scope (.natural value :: rest) (.lit value) rest
  | grouped : ExprReads scope 0 input tree (closeParen :: rest) →
      AtomReads scope (openParen :: input) tree rest
  | trueLit : AtomReads scope (trueKeyword :: rest) .trueLit rest
  | falseLit : AtomReads scope (falseKeyword :: rest) .falseLit rest
  | variable (ref : Local scope type) (visible : ref.visible) (ordinary : ordinaryLocal ref.binding.name) :
      AtomReads scope (.word ref.binding.name.val :: rest) (.variable ref visible ordinary) rest
  | negativeLit : AtomReads scope (minus :: .natural value :: rest) (.negativeLit value) rest
  | neg : NegationStart input → AtomReads scope input operand rest →
      AtomReads scope (minus :: input) (.neg operand) rest
  | not : PrimaryStart input → AtomReads scope input operand rest →
      AtomReads scope (bang :: input) (.not operand) rest

/-- The right operand takes higher-precedence operators. A comparison also
    refuses a comparison at the head of its continuation. -/
inductive ExprTail (scope : Scope) :
    Nat → {inputType : Ty .value} → Expr scope inputType → List Token →
      {resultType : Ty .value} → Expr scope resultType → List Token → Prop where
  | stop : ¬ Continues minimum rest → ExprTail scope minimum left rest left rest
  | binary (op : Arith) : minimum ≤ op.precedence →
      ExprReads scope (op.precedence + 1) input right more →
      ExprTail scope minimum (.binary op left right) more tree rest →
      ExprTail scope minimum left (op.token :: input) tree rest
  | div : minimum ≤ Infix.div.precedence →
      ExprReads scope (Infix.div.precedence + 1) input (right : Expr scope (.int lo hi)) more →
      (nonzero : Divisor lo hi) → ExprTail scope minimum (.div left right nonzero) more tree rest →
      ExprTail scope minimum left (Infix.div.token :: input) tree rest
  | compare (op : Compare) : minimum ≤ (Infix.compare op).precedence →
      ExprReads scope ((Infix.compare op).precedence + 1) input right more →
      (Infix.compare op).follows more → ExprTail scope minimum (.compare op left right) more tree rest →
      ExprTail scope minimum left ((Infix.compare op).token :: input) tree rest
  | logic (op : Logic) : minimum ≤ (Infix.logic op).precedence →
      ExprReads scope ((Infix.logic op).precedence + 1) input right more →
      ExprTail scope minimum (.logic op left right) more tree rest →
      ExprTail scope minimum left ((Infix.logic op).token :: input) tree rest

end


theorem probe_det (left : ExprReads scope minimum input a rest)
    (right : ExprReads scope minimum input b rest') : a.typed = b.typed ∧ rest = rest' := by
  revert b rest'
  refine ExprReads.rec
    (motive_1 := fun min input _ a rest _ =>
      ∀ {otherType} {b : Expr scope otherType} {rest'}, ExprReads scope min input b rest' → a.typed = b.typed ∧ rest = rest')
    (motive_2 := fun input _ a rest _ =>
      ∀ {otherType} {b : Expr scope otherType} {rest'}, AtomReads scope input b rest' → a.typed = b.typed ∧ rest = rest')
    (motive_3 := fun min _ first input _ a rest _ =>
      ∀ {otherType} {b : Expr scope otherType} {rest'}, ExprTail scope min first input b rest' → a.typed = b.typed ∧ rest = rest')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  all_goals intros; trace_state; try rfl

end Gabbro.Core.Ast.Probe
