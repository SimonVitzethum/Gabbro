module

public import Core.Ast.Surface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

structure VariableArgs (scope : Scope) where
  {type : Ty .value}
  ref : Local scope type
  visible : ref.visible
  ordinary : ordinaryLocal ref.binding.name

structure NegArgs (scope : Scope) where
  {lo hi : Int}
  operand : Expr scope (.int lo hi)

structure DivisionArgs (scope : Scope) where
  {lo₁ hi₁ lo₂ hi₂ : Int}
  left : Expr scope (.int lo₁ hi₁)
  right : Expr scope (.int lo₂ hi₂)
  nonzero : Divisor lo₂ hi₂

structure CompareArgs (scope : Scope) where
  op : Compare
  {lo₁ hi₁ lo₂ hi₂ : Int}
  left : Expr scope (.int lo₁ hi₁)
  right : Expr scope (.int lo₂ hi₂)

structure LogicArgs (scope : Scope) where
  op : Logic
  left : Expr scope .bool
  right : Expr scope .bool

structure AssignArgs (scope : Scope) where
  {lo hi valueLo valueHi : Int}
  ref : Local scope (.int lo hi)
  visible : ref.visible
  writable : ref.binding.mutable = true
  value : Expr scope (.int valueLo valueHi)
  fits : Fits (.int valueLo valueHi) (.int lo hi)

structure ReturnArgs (scope : Scope) (expected : Ty .value) where
  {type : Ty .value}
  value : Expr scope type
  fits : Fits type expected

structure IfArgs (scope : Scope) (result : Option (Ty .value)) where
  condition : Expr scope .bool
  yes : BracedBlock result scope
  no : BracedBlock result scope

def infixStep (left : Expr scope leftType) (op : Infix) (right : Expr scope rightType)
    (input rest : List Token) : Prop :=
  ∃ operand, AtomReads scope input left (op.token :: operand) ∧
    ExprReads scope (op.precedence + 1) operand right rest ∧ op.follows rest

def infixProduction (left : Expr scope leftType) (op : Infix) (right : Expr scope rightType)
    (tokens : List Token) : Prop :=
  infixStep left op right tokens [] ∨
    ∃ inner, tokens = openParen :: inner ∧ infixStep left op right inner [closeParen]

def trueLit (scope : Scope) : Rule (.expression scope) PUnit where
  tree := fun _ => (Expr.trueLit (scope := scope)).typed
  production := fun _ tokens => tokens = [trueKeyword]

-- Mirror literal_print for the declared spelling.
theorem trueLit_print (scope : Scope) (args : PUnit) :
    (trueLit scope).production args (((Category.expression scope).printPieces ((trueLit scope).tree args)).map PrintedToken.value) := by
  rfl

-- Mirror literal_entry by applying the new production and its child proofs.
theorem trueLit_reads (scope : Scope) (args : PUnit)
    (read : (trueLit scope).production args tokens) : (Category.expression scope).reads tokens ((trueLit scope).tree args) := by
  change tokens = [trueKeyword] at read
  subst tokens
  exact .atom .trueLit (.stop noOperatorAtEnd)

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem trueLit_erfuellbar (scope : Scope) : (trueLit scope).Satisfiable := by
  exact Rule.satisfiableOfPrint PUnit.unit (trueLit_print scope PUnit.unit)

theorem trueLit_entry (scope : Scope) : (trueLit scope).Entry where
  reads := fun a _ => trueLit_reads scope a
  prints := trueLit_print (scope := scope)
  erfuellbar := trueLit_erfuellbar scope

def falseLit (scope : Scope) : Rule (.expression scope) PUnit where
  tree := fun _ => (Expr.falseLit (scope := scope)).typed
  production := fun _ tokens => tokens = [falseKeyword]

-- Mirror literal_print for the declared spelling.
theorem falseLit_print (scope : Scope) (args : PUnit) :
    (falseLit scope).production args (((Category.expression scope).printPieces ((falseLit scope).tree args)).map PrintedToken.value) := by
  rfl

-- Mirror literal_entry by applying the new production and its child proofs.
theorem falseLit_reads (scope : Scope) (args : PUnit)
    (read : (falseLit scope).production args tokens) : (Category.expression scope).reads tokens ((falseLit scope).tree args) := by
  change tokens = [falseKeyword] at read
  subst tokens
  exact .atom .falseLit (.stop noOperatorAtEnd)

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem falseLit_erfuellbar (scope : Scope) : (falseLit scope).Satisfiable := by
  exact Rule.satisfiableOfPrint PUnit.unit (falseLit_print scope PUnit.unit)

theorem falseLit_entry (scope : Scope) : (falseLit scope).Entry where
  reads := fun a _ => falseLit_reads scope a
  prints := falseLit_print (scope := scope)
  erfuellbar := falseLit_erfuellbar scope

def localValue (scope : Scope) : Rule (.expression scope) (VariableArgs scope) where
  tree := fun a => (Expr.variable a.ref a.visible a.ordinary).typed
  production := fun a tokens => tokens = [.word a.ref.binding.name.val]

-- Mirror literal_print for the declared spelling.
theorem variable_print (args : VariableArgs scope) :
    (localValue scope).production args (((Category.expression scope).printPieces ((localValue scope).tree args)).map PrintedToken.value) := by
  rfl

-- Mirror literal_entry by applying the new production and its child proofs.
theorem variable_reads (scope : Scope) (args : VariableArgs scope)
    (read : (localValue scope).production args tokens) : (Category.expression scope).reads tokens ((localValue scope).tree args) := by
  change tokens = [.word args.ref.binding.name.val] at read
  subst tokens
  exact .atom (.variable args.ref args.visible args.ordinary) (.stop noOperatorAtEnd)

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem variable_erfuellbar  : ∃ scope, (localValue scope).Satisfiable := by
  let name : Identifier := keywordName 'x' [] (by decide) (by intro c h; cases h)
  let scope : Scope := [⟨name, .bool, false⟩]
  let ordinary : ordinaryLocal name := by
    change ['x'] ≠ "true".toList ∧ ['x'] ≠ "false".toList
    simp
  let args : VariableArgs scope := ⟨.here, trivial, ordinary⟩
  exact ⟨scope, Rule.satisfiableOfPrint args (variable_print args)⟩

def negativeLit (scope : Scope) : Rule (.expression scope) Nat where
  tree := fun n => (Expr.negativeLit (scope := scope) n).typed
  production := fun n tokens => tokens = [minus, .natural n]

-- Mirror literal_print for the declared spelling.
theorem negativeLit_print (scope : Scope) (args : Nat) :
    (negativeLit scope).production args (((Category.expression scope).printPieces ((negativeLit scope).tree args)).map PrintedToken.value) := by
  rfl

-- Mirror literal_entry by applying the new production and its child proofs.
theorem negativeLit_reads (scope : Scope) (args : Nat)
    (read : (negativeLit scope).production args tokens) : (Category.expression scope).reads tokens ((negativeLit scope).tree args) := by
  change tokens = [minus, .natural args] at read
  subst tokens
  exact .atom .negativeLit (.stop noOperatorAtEnd)

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem negativeLit_erfuellbar (scope : Scope) : (negativeLit scope).Satisfiable := by
  exact Rule.satisfiableOfPrint 0 (negativeLit_print scope 0)

theorem negativeLit_entry (scope : Scope) : (negativeLit scope).Entry where
  reads := fun a _ => negativeLit_reads scope a
  prints := negativeLit_print (scope := scope)
  erfuellbar := negativeLit_erfuellbar scope

def neg (scope : Scope) : Rule (.expression scope) (NegArgs scope) where
  tree := fun a => (Expr.neg a.operand).typed
  production := fun a tokens => ∃ input, tokens = minus :: input ∧
    NegationStart input ∧ AtomReads scope input a.operand []

-- Mirror literal_print for the declared spelling.
theorem neg_print (args : NegArgs scope) :
    (neg scope).production args (((Category.expression scope).printPieces ((neg scope).tree args)).map PrintedToken.value) := by
  change (neg scope).production args (Expr.neg args.operand).printTokens
  unfold neg
  refine ⟨openParen :: args.operand.printTokens ++ [closeParen], ?_, ?_, ?_⟩
  · change Arith.sub.token :: Token.punctuation "(".toList :: (args.operand.printTokens ++ [Token.punctuation ")".toList]) = minus :: openParen :: (args.operand.printTokens ++ [closeParen])
    simp only [Arith.token, minus, openParen, closeParen, String.reduceToList]
  · refine ⟨?_, ?_⟩
    · intro tail
      constructor <;> intro h <;> cases h
    · intro n tail h
      cases h
  · exact .grouped (args.operand.printReads (rest := [closeParen]) noOperatorAtClose)

-- Mirror literal_entry by applying the new production and its child proofs.
theorem neg_reads (scope : Scope) (args : NegArgs scope)
    (read : (neg scope).production args tokens) : (Category.expression scope).reads tokens ((neg scope).tree args) := by
  obtain ⟨input, rfl, start, atomRead⟩ := read
  exact .atom (.neg start atomRead) (.stop noOperatorAtEnd)

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem neg_erfuellbar (scope : Scope) : (neg scope).Satisfiable := by
  let args : NegArgs scope := ⟨.lit 1⟩
  exact Rule.satisfiableOfPrint args (neg_print args)

theorem neg_entry (scope : Scope) : (neg scope).Entry where
  reads := fun a _ => neg_reads scope a
  prints := neg_print
  erfuellbar := neg_erfuellbar scope

def notValue (scope : Scope) : Rule (.expression scope) (Expr scope .bool) where
  tree := fun a => (Expr.not a).typed
  production := fun a tokens => ∃ input, tokens = bang :: input ∧
    PrimaryStart input ∧ AtomReads scope input a []

-- Mirror literal_print for the declared spelling.
theorem notValue_print (args : Expr scope .bool) :
    (notValue scope).production args (((Category.expression scope).printPieces ((notValue scope).tree args)).map PrintedToken.value) := by
  change (notValue scope).production args (Expr.not args).printTokens
  unfold notValue
  refine ⟨openParen :: args.printTokens ++ [closeParen], ?_, ?_, ?_⟩
  · change Token.punctuation "!".toList :: Token.punctuation "(".toList :: (args.printTokens ++ [Token.punctuation ")".toList]) = bang :: openParen :: (args.printTokens ++ [closeParen])
    simp only [bang, openParen, closeParen, String.reduceToList]
  · intro tail
    constructor <;> intro h <;> cases h
  · exact .grouped (args.printReads (rest := [closeParen]) noOperatorAtClose)

-- Mirror literal_entry by applying the new production and its child proofs.
theorem notValue_reads (scope : Scope) (args : Expr scope .bool)
    (read : (notValue scope).production args tokens) : (Category.expression scope).reads tokens ((notValue scope).tree args) := by
  obtain ⟨input, rfl, primary, atomRead⟩ := read
  exact .atom (.not primary atomRead) (.stop noOperatorAtEnd)

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem notValue_erfuellbar (scope : Scope) : (notValue scope).Satisfiable := by
  let args : Expr scope .bool := .trueLit
  exact Rule.satisfiableOfPrint args (notValue_print args)

theorem notValue_entry (scope : Scope) : (notValue scope).Entry where
  reads := fun a _ => notValue_reads scope a
  prints := notValue_print
  erfuellbar := notValue_erfuellbar scope

def division (scope : Scope) : Rule (.expression scope) (DivisionArgs scope) where
  tree := fun a => (Expr.div a.left a.right a.nonzero).typed
  production := fun a tokens => infixProduction a.left .div a.right tokens

-- Mirror binary_print for the declared spelling.
theorem division_print (args : DivisionArgs scope) :
    (division scope).production args (((Category.expression scope).printPieces ((division scope).tree args)).map PrintedToken.value) := by
  change (division scope).production args (Expr.div args.left args.right args.nonzero).printTokens
  unfold division infixProduction infixStep
  simp only [Expr.printTokens, Expr.printPieces, PrintedToken.slash, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
  refine Or.inr ⟨_, rfl, ?_⟩
  refine ⟨args.right.printTokens ++ [closeParen], ?_, ?_, by trivial⟩
  · exact args.left.printAtom (Infix.div.token :: args.right.printTokens ++ [closeParen])
  · exact ExprReads.atom (args.right.printAtom [closeParen]) (.stop noOperatorAtClose)

-- Mirror BinaryArgs.readStep_sound by applying the new production and its child proofs.
theorem division_reads (scope : Scope) (args : DivisionArgs scope)
    (read : (division scope).production args tokens) : (Category.expression scope).reads tokens ((division scope).tree args) := by
  unfold division infixProduction at read
  rcases read with plain | ⟨inner, rfl, grouped⟩
  · obtain ⟨operand, atomRead, exprRead, follows⟩ := plain
    exact .atom atomRead (.div (Nat.zero_le _) exprRead args.nonzero (.stop noOperatorAtEnd))
  · obtain ⟨operand, atomRead, exprRead, follows⟩ := grouped
    apply ExprReads.atom _ (.stop noOperatorAtEnd)
    exact .grouped (.atom atomRead (.div (Nat.zero_le _) exprRead args.nonzero (.stop noOperatorAtClose)))

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem division_erfuellbar (scope : Scope) : (division scope).Satisfiable := by
  let args : DivisionArgs scope := ⟨.lit 1, .lit 2, Or.inl (by decide)⟩
  exact Rule.satisfiableOfPrint args (division_print args)

theorem division_entry (scope : Scope) : (division scope).Entry where
  reads := fun a _ => division_reads scope a
  prints := division_print
  erfuellbar := division_erfuellbar scope

def comparison (scope : Scope) : Rule (.expression scope) (CompareArgs scope) where
  tree := fun a => (Expr.compare a.op a.left a.right).typed
  production := fun a tokens => infixProduction a.left (.compare a.op) a.right tokens

-- Mirror binary_print for the declared spelling.
theorem comparison_print (args : CompareArgs scope) :
    (comparison scope).production args (((Category.expression scope).printPieces ((comparison scope).tree args)).map PrintedToken.value) := by
  change (comparison scope).production args (Expr.compare args.op args.left args.right).printTokens
  unfold comparison infixProduction infixStep
  simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, Compare.print, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
  refine Or.inr ⟨_, rfl, ?_⟩
  refine ⟨args.right.printTokens ++ [closeParen], ?_, ?_, ?_⟩
  · exact args.left.printAtom ((Infix.compare args.op).token :: args.right.printTokens ++ [closeParen])
  · exact ExprReads.atom (args.right.printAtom [closeParen]) (.stop noOperatorAtClose)
  · intro op tail h
    cases h

-- Mirror BinaryArgs.readStep_sound by applying the new production and its child proofs.
theorem comparison_reads (scope : Scope) (args : CompareArgs scope)
    (read : (comparison scope).production args tokens) : (Category.expression scope).reads tokens ((comparison scope).tree args) := by
  unfold comparison infixProduction at read
  rcases read with plain | ⟨inner, rfl, grouped⟩
  · obtain ⟨operand, atomRead, exprRead, follows⟩ := plain
    exact .atom atomRead (.compare args.op (Nat.zero_le _) exprRead follows (.stop noOperatorAtEnd))
  · obtain ⟨operand, atomRead, exprRead, follows⟩ := grouped
    apply ExprReads.atom _ (.stop noOperatorAtEnd)
    exact .grouped (.atom atomRead (.compare args.op (Nat.zero_le _) exprRead follows (.stop noOperatorAtClose)))

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem comparison_erfuellbar (scope : Scope) : ∀ op, ∃ a text pieces, a.op = op ∧ Lexed text pieces ∧ (comparison scope).production a (canonicalTokens pieces) := by
  intro op
  let args : CompareArgs scope := ⟨op, .lit 1, .lit 2⟩
  obtain ⟨a, text, pieces, lexical, production⟩ := Rule.satisfiableOfPrint args (comparison_print args)
  exact ⟨a, text, pieces, by change args.op = op; rfl, lexical, production⟩

theorem comparison_entry (scope : Scope) : (comparison scope).Entry where
  reads := fun a _ => comparison_reads scope a
  prints := comparison_print
  erfuellbar := by
    obtain ⟨a, text, pieces, _, lexical, read⟩ := comparison_erfuellbar scope .eq
    exact ⟨a, text, pieces, lexical, read⟩

def logic (scope : Scope) : Rule (.expression scope) (LogicArgs scope) where
  tree := fun a => (Expr.logic a.op a.left a.right).typed
  production := fun a tokens => infixProduction a.left (.logic a.op) a.right tokens

-- Mirror binary_print for the declared spelling.
theorem logic_print (args : LogicArgs scope) :
    (logic scope).production args (((Category.expression scope).printPieces ((logic scope).tree args)).map PrintedToken.value) := by
  change (logic scope).production args (Expr.logic args.op args.left args.right).printTokens
  unfold logic infixProduction infixStep
  simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, Logic.print, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
  refine Or.inr ⟨_, rfl, ?_⟩
  refine ⟨args.right.printTokens ++ [closeParen], ?_, ?_, by trivial⟩
  · exact args.left.printAtom ((Infix.logic args.op).token :: args.right.printTokens ++ [closeParen])
  · exact ExprReads.atom (args.right.printAtom [closeParen]) (.stop noOperatorAtClose)

-- Mirror BinaryArgs.readStep_sound by applying the new production and its child proofs.
theorem logic_reads (scope : Scope) (args : LogicArgs scope)
    (read : (logic scope).production args tokens) : (Category.expression scope).reads tokens ((logic scope).tree args) := by
  unfold logic infixProduction at read
  rcases read with plain | ⟨inner, rfl, grouped⟩
  · obtain ⟨operand, atomRead, exprRead, follows⟩ := plain
    exact .atom atomRead (.logic args.op (Nat.zero_le _) exprRead (.stop noOperatorAtEnd))
  · obtain ⟨operand, atomRead, exprRead, follows⟩ := grouped
    apply ExprReads.atom _ (.stop noOperatorAtEnd)
    exact .grouped (.atom atomRead (.logic args.op (Nat.zero_le _) exprRead (.stop noOperatorAtClose)))

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem logic_erfuellbar (scope : Scope) : ∀ op, ∃ a text pieces, a.op = op ∧ Lexed text pieces ∧ (logic scope).production a (canonicalTokens pieces) := by
  intro op
  let args : LogicArgs scope := ⟨op, .trueLit, .falseLit⟩
  obtain ⟨a, text, pieces, lexical, production⟩ := Rule.satisfiableOfPrint args (logic_print args)
  exact ⟨a, text, pieces, by change args.op = op; rfl, lexical, production⟩

theorem logic_entry (scope : Scope) : (logic scope).Entry where
  reads := fun a _ => logic_reads scope a
  prints := logic_print
  erfuellbar := by
    obtain ⟨a, text, pieces, _, lexical, read⟩ := logic_erfuellbar scope .and
    exact ⟨a, text, pieces, lexical, read⟩

def assignVar (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (AssignArgs scope) where
  tree := fun a => ⟨scope, .assignVar a.ref a.visible a.writable a.value a.fits⟩
  production := fun a tokens => ∃ input,
    tokens = .word a.ref.binding.name.val :: assignment :: input ∧
    ExprReads scope 0 input a.value [semicolon]

-- Mirror letValue_print for the declared spelling.
theorem assignVar_print (args : AssignArgs scope) :
    (assignVar scope result).production args (((Category.statement scope result).printPieces ((assignVar scope result).tree args)).map PrintedToken.value) := by
  change (assignVar scope result).production args
    (Stmt.assignVar args.ref args.visible args.writable args.value args.fits).printTokens
  unfold assignVar
  simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]
  exact ⟨_, rfl, args.value.printReads (rest := [semicolon]) noOperatorAtSemicolon⟩

-- Mirror letValue_entry by applying the new production and its child proofs.
theorem assignVar_reads (scope : Scope) (result : Option (Ty .value)) (args : AssignArgs scope)
    (read : (assignVar scope result).production args tokens) : (Category.statement scope result).reads tokens ((assignVar scope result).tree args) := by
  obtain ⟨input, rfl, read⟩ := read
  exact .assignVar args.ref args.visible args.writable args.fits read

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem assignVar_erfuellbar  : ∃ (scope : Scope) (result : Option (Ty .value)), (assignVar scope result).Satisfiable := by
  let name : Identifier := keywordName 'x' [] (by decide) (by intro c h; cases h)
  let scope : Scope := [⟨name, .int 1 1, true⟩]
  let args : AssignArgs scope := ⟨.here, trivial, rfl, .lit 1, ⟨by decide, by decide⟩⟩
  exact ⟨scope, none, Rule.satisfiableOfPrint args (assignVar_print args)⟩

def returnValue (scope : Scope) (expected : Ty .value) : Rule (.statement scope (some expected)) (ReturnArgs scope expected) where
  tree := fun a => ⟨scope, .ret rfl a.value a.fits⟩
  production := fun a tokens => ∃ input,
    tokens = returnKeyword :: input ∧ ExprReads scope 0 input a.value [semicolon]

-- Mirror letValue_print for the declared spelling.
theorem returnValue_print (args : ReturnArgs scope expected) :
    (returnValue scope expected).production args (((Category.statement scope (some expected)).printPieces ((returnValue scope expected).tree args)).map PrintedToken.value) := by
  change (returnValue scope expected).production args (Stmt.ret rfl args.value args.fits).printTokens
  unfold returnValue
  simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]
  exact ⟨_, rfl, args.value.printReads (rest := [semicolon]) noOperatorAtSemicolon⟩

-- Mirror letValue_entry by applying the new production and its child proofs.
theorem returnValue_reads (scope : Scope) (expected : Ty .value) (args : ReturnArgs scope expected)
    (read : (returnValue scope expected).production args tokens) : (Category.statement scope (some expected)).reads tokens ((returnValue scope expected).tree args) := by
  obtain ⟨input, rfl, read⟩ := read
  exact .ret rfl args.fits read

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem returnValue_erfuellbar  : ∃ (scope : Scope) (expected : Ty .value), (returnValue scope expected).Satisfiable := by
  let args : ReturnArgs [] (.int 1 1) := ⟨.lit 1, ⟨by decide, by decide⟩⟩
  exact ⟨[], .int 1 1, Rule.satisfiableOfPrint args (returnValue_print args)⟩

def ifElse (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (IfArgs scope result) where
  tree := fun a => ⟨scope, .ite a.condition a.yes a.no⟩
  production := fun a tokens => ∃ input first more,
    tokens = ifKeyword :: input ∧ ExprReads scope 0 input a.condition first ∧
    BlockReads result scope first a.yes (elseKeyword :: more) ∧ BlockReads result scope more a.no []

-- Mirror Block.printItems_reads for the declared spelling.
theorem ifElse_print (args : IfArgs scope result) :
    (ifElse scope result).production args (((Category.statement scope result).printPieces ((ifElse scope result).tree args)).map PrintedToken.value) := by
  change (ifElse scope result).production args (Stmt.ite args.condition args.yes args.no).printTokens
  unfold ifElse
  simp only [Stmt.printTokens, Stmt.printPieces, BracedBlock.printPieces, Expr.printTokens,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
  refine ⟨args.condition.printTokens ++ args.yes.printPieces.map PrintedToken.value ++
      elseKeyword :: args.no.printPieces.map PrintedToken.value,
    args.yes.printPieces.map PrintedToken.value ++ elseKeyword :: args.no.printPieces.map PrintedToken.value,
    args.no.printPieces.map PrintedToken.value, rfl, ?_, ?_, ?_⟩
  · apply args.condition.printReads
    cases args.yes with
    | braces body =>
      simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append]
      exact noOperatorAtOpenBrace
  · exact args.yes.printReads _
  · exact args.no.printReads []

-- Mirror BracedBlock.printReads by applying the new production and its child proofs.
theorem ifElse_reads (scope : Scope) (result : Option (Ty .value)) (args : IfArgs scope result)
    (read : (ifElse scope result).production args tokens) : (Category.statement scope result).reads tokens ((ifElse scope result).tree args) := by
  obtain ⟨input, first, more, rfl, condRead, yesRead, noRead⟩ := read
  exact .ite condRead yesRead noRead

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem ifElse_erfuellbar (scope : Scope) (result : Option (Ty .value)) : (ifElse scope result).Satisfiable := by
  let args : IfArgs scope result := ⟨.trueLit, .braces .done, .braces .done⟩
  exact Rule.satisfiableOfPrint args (ifElse_print args)

theorem ifElse_entry (scope : Scope) (result : Option (Ty .value)) : (ifElse scope result).Entry where
  reads := fun a _ => ifElse_reads scope result a
  prints := ifElse_print
  erfuellbar := ifElse_erfuellbar scope result

def braced (scope : Scope) (result : Option (Ty .value)) : Rule (.block scope result) (Statements result scope) where
  tree := fun body => .braces body.2
  production := fun body tokens => ∃ input, tokens = openBrace :: input ∧ BlockItems result scope input body []

-- Mirror Block.printItems_reads for the declared spelling.
theorem braced_print (args : Statements result scope) :
    (braced scope result).production args (((Category.block scope result).printPieces ((braced scope result).tree args)).map PrintedToken.value) := by
  change (braced scope result).production args (.braces args.2).printPieces.map PrintedToken.value
  unfold braced
  simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  exact ⟨args.2.printItems.map PrintedToken.value, rfl, Block.printItems_reads args.2 []⟩

-- Mirror BracedBlock.printReads by applying the new production and its child proofs.
theorem braced_reads (scope : Scope) (result : Option (Ty .value)) (args : Statements result scope)
    (read : (braced scope result).production args tokens) : (Category.block scope result).reads tokens ((braced scope result).tree args) := by
  obtain ⟨input, rfl, read⟩ := read
  exact .braced read

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem braced_erfuellbar (scope : Scope) (result : Option (Ty .value)) : (braced scope result).Satisfiable := by
  let args : Statements result scope := ⟨scope, .done⟩
  exact Rule.satisfiableOfPrint args (braced_print args)

theorem braced_entry (scope : Scope) (result : Option (Ty .value)) : (braced scope result).Entry where
  reads := fun a _ => braced_reads scope result a
  prints := braced_print
  erfuellbar := braced_erfuellbar scope result


abbrev SubtractArgs (scope : Scope) := {a : BinaryArgs scope // a.op = .sub}

def subtraction (scope : Scope) : Rule (.expression scope) (SubtractArgs scope) where
  tree := fun args => (binary scope).tree args.val
  production := fun args tokens => (binary scope).production args.val tokens

-- Mirror binary_print with Arith.sub and its token spelling.
theorem subtraction_print (args : SubtractArgs scope) :
    (subtraction scope).production args
      (((Category.expression scope).printPieces ((subtraction scope).tree args)).map PrintedToken.value) := by
  exact binary_print args.val

-- Mirror BinaryArgs.readStep_sound with Arith.sub.
theorem subtraction_reads (scope : Scope) (args : SubtractArgs scope)
    (read : (subtraction scope).production args tokens) :
    (Category.expression scope).reads tokens ((subtraction scope).tree args) := by
  exact (binary_entry scope).reads args.val tokens read

-- Mirror binary_erfuellbar using the token sequence 5 - 2.
theorem subtraction_erfuellbar (scope : Scope) : (subtraction scope).Satisfiable := by
  obtain ⟨args, text, pieces, lexical, production⟩ := binary_erfuellbar scope
  exact ⟨⟨args, rfl⟩, text, pieces, lexical, production⟩

theorem subtraction_entry (scope : Scope) : (subtraction scope).Entry where
  reads := fun a _ => subtraction_reads scope a
  prints := subtraction_print
  erfuellbar := subtraction_erfuellbar scope

theorem variable_entry (args : VariableArgs scope) : (localValue scope).Entry where
  reads := fun a _ => variable_reads scope a
  prints := variable_print
  erfuellbar := Rule.satisfiableOfPrint args (variable_print args)

theorem assignVar_entry (args : AssignArgs scope) (result : Option (Ty .value)) :
    (assignVar scope result).Entry where
  reads := fun a _ => assignVar_reads scope result a
  prints := assignVar_print
  erfuellbar := Rule.satisfiableOfPrint args (assignVar_print args)

theorem returnValue_entry (args : ReturnArgs scope expected) : (returnValue scope expected).Entry where
  reads := fun a _ => returnValue_reads scope expected a
  prints := returnValue_print
  erfuellbar := Rule.satisfiableOfPrint args (returnValue_print args)

end Gabbro.Core.Ast.Surface
