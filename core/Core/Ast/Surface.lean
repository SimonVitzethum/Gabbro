module

public import Core.Ast.Grammar
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text
open Gabbro.Core.Ast

/-- The syntax portion of a surface constructor's registry schema, with its
    actual constructor application and declarative production premises. -/
structure Rule (category : Category) (Arguments : Type) where
  tree : Arguments → category.Tree
  production : Arguments → List Token → Prop

def Rule.Satisfiable {category : Category} {Arguments : Type} (rule : Rule category Arguments) : Prop :=
  ∃ args text pieces, Lexed text pieces ∧ rule.production args (canonicalTokens pieces)

structure Rule.Entry {category : Category} {Arguments : Type} (rule : Rule category Arguments) : Prop where
  reads : ∀ args tokens, rule.production args tokens → category.reads tokens (rule.tree args)
  prints : ∀ args, rule.production args ((category.printPieces (rule.tree args)).map PrintedToken.value)
  erfuellbar : rule.Satisfiable

theorem Rule.Entry.parse {rule : Rule category Arguments} (entry : rule.Entry)
    (lexical : Lexed text pieces) (production : rule.production args (canonicalTokens pieces)) :
    Ast.Parse text (rule.tree args) :=
  category.syntax.parse_iff.mpr ⟨pieces, lexical, entry.reads args _ production⟩

theorem Rule.satisfiableOfPrint {rule : Rule category Arguments} (args : Arguments)
    (prints : rule.production args ((category.printPieces (rule.tree args)).map PrintedToken.value)) :
    rule.Satisfiable := by
  obtain ⟨pieces, lexical, alignment⟩ :=
    PrintedToken.renderLexed 0 (category.printPieces (rule.tree args))
  exact ⟨args, _, pieces, lexical, alignment.symm ▸ prints⟩

/-- Inventory key `surface.SExpr.lit`. -/
def literal (scope : Scope) : Rule (.expression scope .integer) Nat where
  tree := Expr.lit
  production := fun value tokens => tokens = [.natural value]

theorem literal_print (scope : Scope) (value : Nat) :
    (literal scope).production value
      (((Category.expression scope .integer).printPieces (.lit value)).map PrintedToken.value) :=
  rfl

theorem literal_erfuellbar (scope : Scope) : (literal scope).Satisfiable :=
  Rule.satisfiableOfPrint 0 (literal_print scope 0)

theorem literal_entry (scope : Scope) : (literal scope).Entry where
  reads := by
    intro value tokens same
    change tokens = [.natural value] at same
    subst tokens
    exact .atom .lit (.stop noOperatorAtEnd)
  prints := literal_print scope
  erfuellbar := literal_erfuellbar scope

structure BinaryArgs (scope : Scope) where
  op : Arith
  left : Expr scope .integer
  right : Expr scope .integer

/-- The production for a left atom and one precedence-sensitive infix step. -/
def BinaryArgs.readStep (args : BinaryArgs scope) (input rest : List Token) : Prop :=
  ∃ operand, AtomReads scope input args.left (args.op.token :: operand) ∧
    ExprReads scope (args.op.precedence + 1) operand args.right rest

theorem BinaryArgs.readStep_sound (args : BinaryArgs scope) (read : args.readStep input rest)
    (blocked : ¬ Continues 0 rest) : ExprReads scope 0 input (.binary args.op args.left args.right) rest := by
  obtain ⟨_, left, right⟩ := read
  exact .atom left (.binary args.op (Nat.zero_le _) right (.stop blocked))

/-- Inventory key `surface.SExpr.bin`. Includes ordinary infix and canonical grouping. -/
def binary (scope : Scope) : Rule (.expression scope .integer) (BinaryArgs scope) where
  tree := fun args => .binary args.op args.left args.right
  production := fun args tokens =>
    args.readStep tokens [] ∨ ∃ inner, tokens = openParen :: inner ∧ args.readStep inner [closeParen]

theorem binary_print (args : BinaryArgs scope) :
    (binary scope).production args
      (((Category.expression scope .integer).printPieces (.binary args.op args.left args.right)).map
        PrintedToken.value) := by
  change (binary scope).production args (Expr.binary args.op args.left args.right).printTokens
  unfold binary
  simp only [Expr.printTokens_binary, List.append_assoc, List.singleton_append]
  refine Or.inr ⟨_, rfl, _, args.left.printAtom _, ?_⟩
  exact ExprReads.atom (args.right.printAtom [closeParen]) (.stop noOperatorAtClose)

theorem binary_erfuellbar (scope : Scope) : (binary scope).Satisfiable := by
  let args : BinaryArgs scope := ⟨.add, .lit 1, .binary .mul (.lit 2) (.lit 3)⟩
  let words := [printInteger 1, Arith.add.print, printInteger 2, Arith.mul.print, printInteger 3]
  obtain ⟨pieces, lexical, alignment⟩ := PrintedToken.renderLexed 0 words
  refine ⟨args, _, pieces, lexical, ?_⟩
  rw [alignment]
  apply Or.inl
  refine ⟨_, AtomReads.lit, .atom .lit (.binary .mul ?_ ?_ (.stop noOperatorAtEnd))⟩
  · exact Nat.le_refl _
  · exact .atom .lit (.stop noOperatorAtEnd)

theorem binary_entry (scope : Scope) : (binary scope).Entry where
  reads := by
    intro args tokens production
    rcases production with plain | ⟨inner, rfl, grouped⟩
    · exact args.readStep_sound plain noOperatorAtEnd
    · exact .atom (.grouped (args.readStep_sound grouped noOperatorAtClose)) (.stop noOperatorAtEnd)
  prints := binary_print
  erfuellbar := binary_erfuellbar scope

structure LetArgs (scope : Scope) where
  name : Identifier
  ordinary : name.val ≠ "mut".toList
  value : Expr scope .integer

/-- The ordinary immutable unannotated production of inventory key `surface.SAnw.bind`. -/
def letValue (scope : Scope) : Rule (.statement scope) (LetArgs scope) where
  tree := fun args => ⟨_, .letValue args.name args.ordinary args.value⟩
  production := fun args tokens => ∃ initializer,
    tokens = letKeyword :: .word args.name.val :: assignment :: initializer ∧
    ExprReads scope 0 initializer args.value [semicolon]

theorem letValue_print (args : LetArgs scope) :
    (letValue scope).production args
      (((Category.statement scope).printPieces ((letValue scope).tree args)).map PrintedToken.value) := by
  change (letValue scope).production args
    (Stmt.letValue args.name args.ordinary args.value).printTokens
  unfold letValue
  simp only [Stmt.printTokens_let, List.cons_append, List.nil_append]
  exact ⟨_, rfl, args.value.printReads noOperatorAtSemicolon⟩

theorem letValue_erfuellbar (scope : Scope) : (letValue scope).Satisfiable := by
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : name.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro same
    cases same
  exact Rule.satisfiableOfPrint ⟨name, ordinary, .lit 1⟩ (letValue_print ⟨name, ordinary, .lit 1⟩)

theorem letValue_entry (scope : Scope) : (letValue scope).Entry where
  reads := by
    rintro args _ ⟨initializer, rfl, read⟩
    exact .letBinding args.name args.ordinary read .plain
  prints := letValue_print
  erfuellbar := letValue_erfuellbar scope

end Gabbro.Core.Ast.Surface
