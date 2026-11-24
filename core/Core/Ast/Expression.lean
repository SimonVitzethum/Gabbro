module

public import Core.Ast.Tree

@[expose] public section

namespace Gabbro.Core.Ast

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
def openBracket : Token := .punctuation ['[']
def closeBracket : Token := .punctuation [']']
def dot : Token := .punctuation ['.']
def comma : Token := .punctuation [',']
def colon : Token := .punctuation [':']

inductive Infix where
  | arith (op : Arith)
  | div
  | compare (op : Compare)
  | logic (op : Logic)
  | index
  | projection

def Infix.token : Infix → Token
  | .arith op => op.token
  | .div => .punctuation ['/']
  | .compare op => .punctuation op.spelling.toList
  | .logic op => .punctuation op.spelling.toList
  | .index => openBracket
  | .projection => dot

def Infix.precedence : Infix → Nat
  | .arith op => op.precedence
  | .div => 6
  | .compare _ => 3
  | .logic .and => 2
  | .index | .projection => 7
  | .logic .or => 1

def Infix.follows : Infix → List Token → Prop
  | .compare _, rest => ∀ op tail, rest ≠ Infix.token (.compare op) :: tail
  | _, _ => True

-- Mirror Arith.token_injective across the four operator families.
theorem Infix.token_injective {a b : Infix} (same : a.token = b.token) : a = b := by
  sorry

def Continues (minimum : Nat) (input : List Token) : Prop :=
  ∃ op : Infix, ∃ more, input = op.token :: more ∧ minimum ≤ op.precedence

theorem noOperatorAtEnd : ¬ Continues minimum [] := by
  rintro ⟨op, more, equality, _⟩
  cases equality

-- Mirror the arithmetic case of noOperatorAtClose for the new token families.
theorem noOperatorAtClose : ¬ Continues minimum (closeParen :: more) := by
  sorry

-- Mirror noOperatorAtClose.
theorem noOperatorAtSemicolon : ¬ Continues minimum (semicolon :: more) := by
  sorry

-- Mirror noOperatorAtClose.
theorem noOperatorAtOpenBrace : ¬ Continues minimum (openBrace :: more) := by
  sorry

/-- The operand of a single unary prefix starts at a primary. -/
def PrimaryStart (tokens : List Token) : Prop :=
  ∀ tail, tokens ≠ minus :: tail ∧ tokens ≠ bang :: tail

/-- Minus followed by a numeral belongs to the negative-literal production. -/
def NegationStart (tokens : List Token) : Prop :=
  PrimaryStart tokens ∧ ∀ n tail, tokens ≠ .natural n :: tail

theorem Infix.token_ne_delimiter (op : Infix) :
    op.token ≠ comma ∧ op.token ≠ closeBracket := by
  cases op <;> (try (rename_i operation; cases operation)) <;>
    constructor <;> intro same <;>
      simp [Infix.token, Arith.token, Compare.spelling, Logic.spelling, comma, closeBracket,
        openBracket, dot] at same

theorem noOperatorAtComma : ¬ Continues minimum (comma :: more) := by
  rintro ⟨op, _, same, _⟩
  exact op.token_ne_delimiter.1 (List.cons.inj same).1.symm

theorem noOperatorAtCloseBracket : ¬ Continues minimum (closeBracket :: more) := by
  rintro ⟨op, _, same, _⟩
  exact op.token_ne_delimiter.2 (List.cons.inj same).1.symm

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
  | arrayValue (principal : arrayElement types = some element)
      (fits : ∀ i : Fin types.length, Fits (types.get i) element) :
      ItemsRead scope closeBracket input items rest →
      AtomReads scope (openBracket :: input) (.arrayValue items principal fits) rest
  | tupleValue : ExprReads scope 0 input first (comma :: secondInput) →
      ExprReads scope 0 secondInput second more →
      ItemsTail scope closeParen more items rest →
      AtomReads scope (openParen :: input) (.tupleValue first second items) rest
  | recordValue (ref : RecordRef scope labels types)
      (fields : RecordArguments labels types actualLabels actualTypes)
      (fits : ∀ i, Fits (actualTypes.get (fields.slot i)) (types.get i)) :
      LabeledItemsRead scope input args rest →
      AtomReads scope (.word ref.name.val :: openParen :: input) (.recordValue ref args fields fits) rest
  | variantValue (ref : VariantRef scope labels payloads) (label : Identifier)
      (index : Fin payloads.length) (written : labels[index.val]? = some label)
      (ordinary : ordinaryLocal label) (available : availableCase scope label)
      (payload : CasePayload scope (payloads.get index)) :
      CasePayloadRead scope input payload rest →
      AtomReads scope (.word label.val :: input) (.variantValue ref label index written ordinary available payload) rest

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
  | arrayIndex (base : Expr scope (.array element count)) (lower : 0 ≤ (lo : Int)) (upper : (hi : Int) < (count : Int)) :
      minimum ≤ Infix.index.precedence →
      ExprReads scope 0 input (index : Expr scope (.int lo hi)) (closeBracket :: more) →
      ExprTail scope minimum (.arrayIndex base index lower upper) more tree rest →
      ExprTail scope minimum base (openBracket :: input) tree rest
  | tupleField (base : Expr scope (tupleType (first :: second :: types)))
      (index : Fin (first :: second :: types).length) :
      minimum ≤ Infix.projection.precedence →
      ExprTail scope minimum (.tupleField base index) input tree rest →
      ExprTail scope minimum base (dot :: .natural index.val :: input) tree rest
  | recordField (base : Expr scope (recordValueType name labels types)) (field : Identifier)
      (index : Fin types.length) (written : RecordFieldAt labels field index.val) :
      minimum ≤ Infix.projection.precedence →
      ExprTail scope minimum (.recordField base field index written) input tree rest →
      ExprTail scope minimum base (dot :: .word field.val :: input) tree rest

/-- A comma-delimited expression sequence consumes the caller's closing delimiter. -/
inductive ItemsRead (scope : Scope) : Token →
    List Token → {types : List (Ty .value)} → ExprItems scope types → List Token → Prop where
  | close : ItemsRead scope close (close :: rest) .empty rest
  | next : ExprReads scope 0 input head more → ItemsTail scope close more tail rest →
      ItemsRead scope close input (.next head tail) rest

inductive ItemsTail (scope : Scope) : Token →
    List Token → {types : List (Ty .value)} → ExprItems scope types → List Token → Prop where
  | close : ItemsTail scope close (close :: rest) .empty rest
  | comma {types : List (Ty .value)} {tail : ExprItems scope types} : (types ≠ [] ∨ close = closeBracket) → ItemsRead scope close input tail rest → ItemsTail scope close (comma :: input) tail rest

/-- A record call uses only labelled actuals and consumes its closing parenthesis. -/
inductive LabeledItemsRead (scope : Scope) :
    List Token → {labels : List Identifier} → {types : List (Ty .value)} →
    LabeledItems scope labels types → List Token → Prop where
  | close : LabeledItemsRead scope (closeParen :: rest) .empty rest
  | next (name : Identifier) : ExprReads scope 0 input value more →
      LabeledItemsTail scope more remaining rest →
      LabeledItemsRead scope (.word name.val :: colon :: input) (.next name value remaining) rest

inductive LabeledItemsTail (scope : Scope) :
    List Token → {labels : List Identifier} → {types : List (Ty .value)} →
    LabeledItems scope labels types → List Token → Prop where
  | close : LabeledItemsTail scope (closeParen :: rest) .empty rest
  | comma (label : Identifier) (value : Expr scope type) (remaining : LabeledItems scope labels types) :
      LabeledItemsRead scope input (.next label value remaining) rest →
      LabeledItemsTail scope (comma :: input) (.next label value remaining) rest

inductive CasePayloadRead (scope : Scope) :
    List Token → {type : Option (Ty .value)} → CasePayload scope type → List Token → Prop where
  | bare (closed : ∀ tail, rest ≠ openParen :: tail) :
      CasePayloadRead scope rest (.nullary false) rest
  | empty : CasePayloadRead scope (openParen :: closeParen :: rest) (.nullary true) rest
  | value : ExprReads scope 0 input expression (closeParen :: rest) →
      CasePayloadRead scope (openParen :: input) (.value expression) rest

end

/-- Inverting the atom production recovers both the literal and its complete suffix. -/
theorem AtomReads.lit_inversion
    (read : AtomReads scope (.natural value :: rest) tree suffix) :
    tree.typed = (Expr.lit (scope := scope) value).typed ∧ suffix = rest := by
  cases read
  exact ⟨rfl, rfl⟩

-- Mirror AtomReads.lit_inversion and eliminate the ordinaryLocal exclusion.
theorem AtomReads.true_inversion (read : AtomReads scope (trueKeyword :: rest) tree suffix) :
    tree.typed = (Expr.trueLit (scope := scope)).typed ∧ suffix = rest := by
  sorry

-- Mirror AtomReads.true_inversion.
theorem AtomReads.false_inversion (read : AtomReads scope (falseKeyword :: rest) tree suffix) :
    tree.typed = (Expr.falseLit (scope := scope)).typed ∧ suffix = rest := by
  sorry

-- Mirror AtomReads.lit_inversion, leaving the lookup evidence existential.
theorem AtomReads.variable_inversion (ordinary : word ≠ "true".toList ∧ word ≠ "false".toList)
    (read : AtomReads scope (.word word :: rest) tree suffix) :
    ∃ (ref : Local scope type) (visible : ref.visible) (ordinary : ordinaryLocal ref.binding.name),
      ref.binding.name.val = word ∧ tree.typed = (Expr.variable ref visible ordinary).typed ∧ suffix = rest := by
  sorry

-- Mirror AtomReads.lit_inversion and exclude the unary minus via NegationStart.
theorem AtomReads.negative_inversion
    (read : AtomReads scope (minus :: .natural value :: rest) tree suffix) :
    tree.typed = (Expr.negativeLit (scope := scope) value).typed ∧ suffix = rest := by
  sorry

-- Mirror AtomReads.lit_inversion, retaining the operand derivation.
theorem AtomReads.neg_inversion (start : NegationStart input)
    (read : AtomReads scope (minus :: input) tree rest) :
    ∃ (lo hi : Int) (operand : Expr scope (.int lo hi)),
      AtomReads scope input operand rest ∧ tree.typed = (Expr.neg operand).typed := by
  sorry

-- Mirror AtomReads.neg_inversion and keep the Boolean type.
theorem AtomReads.not_inversion (read : AtomReads scope (bang :: input) tree rest) :
    ∃ operand : Expr scope .bool, PrimaryStart input ∧
      AtomReads scope input operand rest ∧ tree.typed = (Expr.not operand).typed := by
  sorry

-- Mirror Arith.token_injective by inducting on the two typed indices.
theorem Local.visible_unique (a : Local scope type) (b : Local scope type')
    (visibleA : a.visible) (visibleB : b.visible) (same : a.binding.name.val = b.binding.name.val) :
    (⟨type, a⟩ : (t : Ty .value) × Local scope t) = ⟨type', b⟩ := by
  sorry

-- Extend the original mutual ExprReads.deterministic recursor with the new atom and tail branches.
theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
    (right : ExprReads scope minimum input b rest') : a.typed = b.typed ∧ rest = rest' := by
  sorry

-- Extend the original ExprReads.consumes recursor with List.suffix_cons for each new prefix.
theorem ExprReads.consumes (read : ExprReads scope minimum input tree rest) : rest <:+ input := by
  sorry

-- Mirror AtomReads.lit_inversion at the shared arithmetic tail constructor.
theorem ExprTail.arith_inversion (allowed : minimum ≤ op.precedence)
    (read : ExprTail scope minimum (left : Expr scope (.int lo₁ hi₁)) (op.token :: input) tree rest) :
    ∃ (lo₂ hi₂ : Int) (right : Expr scope (.int lo₂ hi₂)) (more : List Token),
      ExprReads scope (op.precedence + 1) input right more ∧
      ExprTail scope minimum (.binary op left right) more tree rest := by
  sorry

-- Mirror ExprTail.arith_inversion and recover the divisor-range evidence.
theorem ExprTail.div_inversion (allowed : minimum ≤ Infix.div.precedence)
    (read : ExprTail scope minimum (left : Expr scope (.int lo₁ hi₁)) (Infix.div.token :: input) tree rest) :
    ∃ (lo₂ hi₂ : Int) (right : Expr scope (.int lo₂ hi₂)) (more : List Token) (nonzero : Divisor lo₂ hi₂),
      ExprReads scope (Infix.div.precedence + 1) input right more ∧
      ExprTail scope minimum (.div left right nonzero) more tree rest := by
  sorry

-- Mirror ExprTail.arith_inversion and recover the guard against an ungrouped comparison.
theorem ExprTail.compare_inversion (allowed : minimum ≤ (Infix.compare op).precedence)
    (read : ExprTail scope minimum (left : Expr scope (.int lo₁ hi₁))
      ((Infix.compare op).token :: input) tree rest) :
    ∃ (lo₂ hi₂ : Int) (right : Expr scope (.int lo₂ hi₂)) (more : List Token),
      ExprReads scope ((Infix.compare op).precedence + 1) input right more ∧
      (Infix.compare op).follows more ∧ ExprTail scope minimum (.compare op left right) more tree rest := by
  sorry

-- Mirror ExprTail.arith_inversion keeping both operands at Boolean type.
theorem ExprTail.logic_inversion (allowed : minimum ≤ (Infix.logic op).precedence)
    (read : ExprTail scope minimum (left : Expr scope .bool)
      ((Infix.logic op).token :: input) tree rest) :
    ∃ (right : Expr scope .bool) (more : List Token),
      ExprReads scope ((Infix.logic op).precedence + 1) input right more ∧
      ExprTail scope minimum (.logic op left right) more tree rest := by
  sorry

-- Mirror ExprReads.consumes with the atom motive of the mutual recursor.
theorem AtomReads.consumes (read : AtomReads scope input tree rest) : rest <:+ input := by
  sorry

-- Mirror ExprReads.consumes with the tail motive of the mutual recursor.
theorem ExprTail.consumes (read : ExprTail scope minimum first input tree rest) : rest <:+ input := by
  sorry

end Gabbro.Core.Ast
