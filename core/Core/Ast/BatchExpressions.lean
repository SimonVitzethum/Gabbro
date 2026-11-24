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
  · simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation,
      PrintedToken.unquoted, Arith.print_value, String.reduceToList, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    rfl
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
  · simp only [Expr.printTokens, Expr.printPieces, printBang, printOpen, printClose,
      printPunctuation, PrintedToken.unquoted, String.reduceToList, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    rfl
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
    have head := (List.cons.inj h).1
    cases op <;> simp only [Infix.token, Compare.spelling, String.reduceToList] at head <;> cases head

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
  let toks := (Category.expression scope).printPieces ((comparison scope).tree args)
  obtain ⟨pieces, lexical, alignment⟩ := PrintedToken.renderLexed 0 toks
  refine ⟨args, PrintedToken.render toks, pieces, rfl, lexical, ?_⟩
  exact alignment.symm ▸ comparison_print args

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
  let toks := (Category.expression scope).printPieces ((logic scope).tree args)
  obtain ⟨pieces, lexical, alignment⟩ := PrintedToken.renderLexed 0 toks
  refine ⟨args, PrintedToken.render toks, pieces, rfl, lexical, ?_⟩
  exact alignment.symm ▸ logic_print args

theorem logic_entry (scope : Scope) : (logic scope).Entry where
  reads := fun a _ => logic_reads scope a
  prints := logic_print
  erfuellbar := by
    obtain ⟨a, text, pieces, _, lexical, read⟩ := logic_erfuellbar scope .and
    exact ⟨a, text, pieces, lexical, read⟩

end Gabbro.Core.Ast.Surface
