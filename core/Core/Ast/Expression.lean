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
  cases a with
  | arith op =>
    cases b with
    | arith op' => exact congrArg Infix.arith (Arith.token_injective (by simpa only [Infix.token] using same))
    | div => cases op <;> cases same
    | compare op' => cases op <;> cases op' <;> cases same
    | logic op' => cases op <;> cases op' <;> cases same
    | index => cases op <;> cases same
    | projection => cases op <;> cases same
  | div =>
    cases b with
    | arith op => cases op <;> cases same
    | div => rfl
    | compare op' => cases op' <;> cases same
    | logic op' => cases op' <;> cases same
    | index => cases same
    | projection => cases same
  | compare op =>
    cases b with
    | arith op' => cases op <;> cases op' <;> cases same
    | div => cases op <;> cases same
    | compare op' => exact congrArg Infix.compare (by
        cases op <;> cases op' <;> first | rfl | cases same)
    | logic op' => cases op <;> cases op' <;> cases same
    | index => cases op <;> cases same
    | projection => cases op <;> cases same
  | logic op =>
    cases b with
    | arith op' => cases op <;> cases op' <;> cases same
    | div => cases op <;> cases same
    | compare op' => cases op <;> cases op' <;> cases same
    | logic op' => exact congrArg Infix.logic (by
        cases op <;> cases op' <;> first | rfl | cases same)
    | index => cases op <;> cases same
    | projection => cases op <;> cases same
  | index =>
    cases b with
    | arith op => cases op <;> cases same
    | div => cases same
    | compare op' => cases op' <;> cases same
    | logic op' => cases op' <;> cases same
    | index => rfl
    | projection => cases same
  | projection =>
    cases b with
    | arith op => cases op <;> cases same
    | div => cases same
    | compare op' => cases op' <;> cases same
    | logic op' => cases op' <;> cases same
    | index => cases same
    | projection => rfl

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
  | index => cases head
  | projection => cases head

-- Mirror noOperatorAtClose.
theorem noOperatorAtSemicolon : ¬ Continues minimum (semicolon :: more) := by
  rintro ⟨op, tail, equality, _⟩
  have head := (List.cons.inj equality).1
  cases op with
  | arith a => cases a <;> cases head
  | div => cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head
  | index => cases head
  | projection => cases head

-- Mirror noOperatorAtClose.
theorem noOperatorAtOpenBrace : ¬ Continues minimum (openBrace :: more) := by
  rintro ⟨op, tail, equality, _⟩
  have head := (List.cons.inj equality).1
  cases op with
  | arith a => cases a <;> cases head
  | div => cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head
  | index => cases head
  | projection => cases head

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
      simp only [Infix.token, Arith.token, Compare.spelling, Logic.spelling, comma, closeBracket,
        openBracket, dot, Token.punctuation.injEq, String.reduceToList, List.cons.injEq,
        Char.reduceEq, false_and, and_false] at same

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
  change AtomReads scope (.word "true".toList :: rest) tree suffix at read
  generalize hs : "true".toList = word at read
  cases read with
  | trueLit => exact ⟨rfl, rfl⟩
  | falseLit => exfalso; cases hs
  | _ =>
      exfalso
      rename_i ref visible ordinary
      exact ordinary.1 hs.symm

-- Mirror AtomReads.true_inversion.
theorem AtomReads.false_inversion (read : AtomReads scope (falseKeyword :: rest) tree suffix) :
    tree.typed = (Expr.falseLit (scope := scope)).typed ∧ suffix = rest := by
  change AtomReads scope (.word "false".toList :: rest) tree suffix at read
  generalize hs : "false".toList = word at read
  cases read with
  | falseLit => exact ⟨rfl, rfl⟩
  | trueLit => exfalso; cases hs
  | _ =>
      exfalso
      rename_i ref visible ordinary
      exact ordinary.2 hs.symm

-- Mirror AtomReads.lit_inversion, leaving the lookup evidence existential.
theorem AtomReads.variable_inversion {scope : Scope} {word : List Char} {rest suffix : List Token}
    {type : Ty .value} {tree : Expr scope type}
    (ordinary : word ≠ "true".toList ∧ word ≠ "false".toList)
    (read : @AtomReads scope (.word word :: rest) type tree suffix) :
    ∃ (ref : Local scope type) (visible : ref.visible) (ordinary : ordinaryLocal ref.binding.name),
      ref.binding.name.val = word ∧ tree.typed = (Expr.variable ref visible ordinary).typed ∧ suffix = rest := by
  cases read
  case trueLit => exact (ordinary.1 rfl).elim
  case falseLit => exact (ordinary.2 rfl).elim
  case _ =>
    rename_i ref vis ord
    exact ⟨ref, vis, ord, rfl, rfl, rfl⟩

theorem AtomReads.negative_inversion
    (read : AtomReads scope (minus :: .natural value :: rest) tree suffix) :
    tree.typed = (Expr.negativeLit (scope := scope) value).typed ∧ suffix = rest := by
  cases read with
  | negativeLit => exact ⟨rfl, rfl⟩
  | _ =>
      exfalso
      rename_i start child
      exact start.2 _ _ rfl

-- Mirror AtomReads.lit_inversion, retaining the operand derivation.
theorem AtomReads.neg_inversion (start : NegationStart input)
    (read : AtomReads scope (minus :: input) tree rest) :
    ∃ (lo hi : Int) (operand : Expr scope (.int lo hi)),
      AtomReads scope input operand rest ∧ tree.typed = (Expr.neg operand).typed := by
  cases read with
  | neg start' child => exact ⟨_, _, _, child, rfl⟩
  | _ =>
      exfalso
      exact start.2 _ _ rfl

-- Mirror AtomReads.neg_inversion and keep the Boolean type.
theorem AtomReads.not_inversion (read : AtomReads scope (bang :: input) tree rest) :
    ∃ operand : Expr scope .bool, PrimaryStart input ∧
      AtomReads scope input operand rest ∧ tree.typed = (Expr.not operand).typed := by
  cases read with
  | not primary child => exact ⟨_, primary, child, rfl⟩

-- Mirror Arith.token_injective by inducting on the two typed indices.
theorem Local.visible_unique (a : Local scope type) (b : Local scope type')
    (visibleA : a.visible) (visibleB : b.visible) (same : a.binding.name.val = b.binding.name.val) :
    (⟨type, a⟩ : (t : Ty .value) × Local scope t) = ⟨type', b⟩ := by
  induction a with
  | here =>
    cases b with
    | here => rfl
    | there b' => exact (visibleB.1 same).elim
  | there a' ih =>
    cases b with
    | here => exact (visibleA.1 same.symm).elim
    | there b' =>
      have eq := ih b' visibleA.2 visibleB.2 same
      cases eq
      rfl

-- Extend the original mutual ExprReads.deterministic recursor with the new atom and tail branches.
theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
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
  · intros
    rename_i input firstType first more minimum treeType tree rest atomRead tailRead atomDet tailDet otherType b rest' otherRead
    cases otherRead with
    | atom atom tail =>
      obtain ⟨same, rfl⟩ := atomDet atom
      cases same
      exact tailDet tail
  · intros
    rename_i _ _ value rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.lit_inversion
    exact ⟨same.symm, suffix.symm⟩
  · intros
    rename_i _ _ input _ tree rest insideRead insideDet _ _ _ otherRead
    cases otherRead with
    | grouped inside =>
      obtain ⟨same, suffix⟩ := insideDet inside
      exact ⟨same, (List.cons.inj suffix).2⟩
  · intros
    rename_i _ _ rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.true_inversion
    exact ⟨same.symm, suffix.symm⟩
  · intros
    rename_i _ _ rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.false_inversion
    exact ⟨same.symm, suffix.symm⟩
  · intros
    rename_i _ _ _ rest ref vis ord _ _ _ otherRead
    obtain ⟨ref', vis', ord', nameEq, sameTree, suffix⟩ := otherRead.variable_inversion ord
    have eqRef : (⟨_, ref⟩ : (t : Ty .value) × Local scope t) = ⟨_, ref'⟩ :=
      Local.visible_unique ref ref' vis vis' nameEq.symm
    cases eqRef
    cases sameTree
    exact ⟨rfl, suffix.symm⟩
  · intros
    rename_i _ _ value rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.negative_inversion
    exact ⟨same.symm, suffix.symm⟩
  · intros
    rename_i _ _ input _ _ operand rest start child childDet _ _ _ otherRead
    obtain ⟨_, _, operand', read', sameTree⟩ := otherRead.neg_inversion start
    cases sameTree
    obtain ⟨same, suffix⟩ := childDet read'
    cases same
    exact ⟨rfl, suffix⟩
  · intros
    rename_i _ _ input operand rest _ child childDet _ _ _ otherRead
    obtain ⟨operand', primary, read', sameTree⟩ := otherRead.not_inversion
    cases sameTree
    obtain ⟨same, suffix⟩ := childDet read'
    cases same
    exact ⟨rfl, suffix⟩
  · intros
    rename_i _ _ _ rest _ left blocked _ _ _ otherRead
    cases otherRead with
    | stop => exact ⟨rfl, rfl⟩
    | binary op allowed => exact (blocked ⟨.arith op, _, rfl, allowed⟩).elim
    | div allowed => exact (blocked ⟨.div, _, rfl, allowed⟩).elim
    | compare op allowed => exact (blocked ⟨.compare op, _, rfl, allowed⟩).elim
    | logic op allowed => exact (blocked ⟨.logic op, _, rfl, allowed⟩).elim
  · intros
    rename_i _ _ _ input _ _ _ _ _ _ _ _ _ _ op allowed _ _ rightDet tailDet _ _ _ otherRead
    generalize h : op.token = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.arith op, input, by simpa only [Infix.token] using congrArg (· :: input) h.symm, allowed⟩).elim
    | binary op' _ rightRead tail =>
      have eq : op = op' := Arith.token_injective h
      cases eq
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail
    | div _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .arith op) (b := .div) h
      cases eq
    | compare op' _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .arith op) (b := .compare op') h
      cases eq
  · intros
    rename_i _ _ _ input _ _ _ _ _ _ _ _ _ _ allowed _ _ _ rightDet tailDet _ _ _ otherRead
    generalize h : Infix.token .div = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.div, input, congrArg (· :: input) h.symm, allowed⟩).elim
    | binary op' _ rightRead tail =>
      have eq := Infix.token_injective (a := .div) (b := .arith op') h
      cases eq
    | div _ rightRead _ tail' =>
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail'
    | compare op' _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .div) (b := .compare op') h
      cases eq
  · intros
    rename_i _ _ _ input _ _ _ _ _ _ _ _ _ _ op allowed _ _ _ rightDet tailDet _ _ _ otherRead
    generalize h : Infix.token (.compare op) = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.compare op, input, congrArg (· :: input) h.symm, allowed⟩).elim
    | binary op' _ rightRead tail =>
      have eq := Infix.token_injective (a := .compare op) (b := .arith op') h
      cases eq
    | div _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .compare op) (b := .div) h
      cases eq
    | compare op' _ rightRead _ tail' =>
      have eq := Infix.token_injective (a := .compare op) (b := .compare op') h
      cases eq
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail'
  · intros
    rename_i _ _ _ input _ _ _ _ _ _ op allowed _ _ rightDet tailDet _ _ _ otherRead
    generalize h : Infix.token (.logic op) = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.logic op, input, congrArg (· :: input) h.symm, allowed⟩).elim
    | logic op' _ rightRead tail' =>
      have eq := Infix.token_injective (a := .logic op) (b := .logic op') h
      cases eq
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail'
-- Extend the original ExprReads.consumes recursor with List.suffix_cons for each new prefix.
theorem ExprReads.consumes (read : ExprReads scope minimum input tree rest) : rest <:+ input := by
  refine ExprReads.rec
    (motive_1 := fun _ input _ _ rest _ => rest <:+ input)
    (motive_2 := fun input _ _ rest _ => rest <:+ input)
    (motive_3 := fun _ _ _ input _ _ rest _ => rest <:+ input)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ read
  · intro _ _ _ _ _ _ _ _ _ _ atom tail
    exact tail.trans atom
  · intro _ _
    exact List.suffix_cons _ _
  · intro input _ _ rest _ child
    exact ((List.suffix_cons closeParen rest).trans child).trans (List.suffix_cons openParen input)
  · intro _
    exact List.suffix_cons _ _
  · intro _
    exact List.suffix_cons _ _
  · intro _ _ _ _ _
    exact List.suffix_cons _ _
  · intro _ _
    exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ start child ihChild
    exact ihChild.trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ ihChild
    exact ihChild.trans (List.suffix_cons _ _)
  · intro _ rest _ _ _
    exact List.suffix_refl rest
  · intro _ input _ _ _ _ _ _ _ _ _ _ op _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ input _ _ _ _ _ _ _ _ _ _ _ _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ input _ _ _ _ _ _ _ _ _ _ op _ _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ _ _ _ op _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)

end Gabbro.Core.Ast
