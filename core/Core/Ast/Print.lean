module

public import Core.Ast.Statement
public import Core.Text.Printing
import Init.Data.Nat.ToString
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def printInteger (value : Nat) : PrintedToken :=
  PrintedToken.unquoted (Nat.toDigits 10 value) (.decimalInteger (Numeral.print value)) (by
    intro c head
    obtain ⟨first, _, spelling, digit⟩ := (Numeral.print value).decimalFirst
    rw [spelling] at head
    obtain rfl := Option.some.inj head
    exact UnquotedStart.ofCodepoint digit.1 (digitNotSpace digit))

def Identifier.print (name : Identifier) : PrintedToken :=
  PrintedToken.unquoted (value := .word name.val) name.val (by
    obtain ⟨first, rest, same, start, all⟩ := name.property
    rw [same]
    exact .word start all) (by
    intro c head
    obtain ⟨first, rest, same, start, _⟩ := name.property
    rw [same] at head
    obtain rfl := Option.some.inj head
    exact nameStart_unquoted start)

def printPunctuation (word : String) (member : word ∈ punctuation)
    (normal : ∀ c, word.toList.head? = some c → UnquotedStart c) : PrintedToken :=
  PrintedToken.unquoted word.toList (.punctuation member) normal

theorem tokenHead (same : [c].head? = some first) (normal : UnquotedStart c) :
    UnquotedStart first :=
  (Option.some.inj same) ▸ normal

theorem punctuationHead (member : c ∈ ['+', '*', '(', ')', '=', ';', '{', '}']) : UnquotedStart c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | (simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true])
    | (intro h; cases h)
def Arith.print : Arith → PrintedToken
  | .add => printPunctuation "+" (by
      simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
      (fun _ same => tokenHead same (punctuationHead List.mem_cons_self))
  | .mul => printPunctuation "*" (by
      simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
      (fun _ same => tokenHead same (punctuationHead (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem Arith.print_value (op : Arith) : op.print.value = op.token := by
  cases op <;> rfl

def printOpen : PrintedToken := printPunctuation "(" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ same => tokenHead (c := '(') same (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def printClose : PrintedToken := printPunctuation ")" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ same => tokenHead (c := ')') same (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def printAssignment : PrintedToken := printPunctuation "=" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ same => tokenHead (c := '=') same (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def printSemicolon : PrintedToken := printPunctuation ";" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ same => tokenHead (c := ';') same (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def printOpenBrace : PrintedToken := printPunctuation "{" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ same => tokenHead (c := '{') same (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def printCloseBrace : PrintedToken := printPunctuation "}" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ same => tokenHead (c := '}') same (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def letName : Identifier := ⟨['l', 'e', 't'], 'l', ['e', 't'], rfl, by
  exact Or.inl (Or.inl ⟨by change 97 ≤ 108; omega, by change 108 ≤ 122; omega⟩), by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl (Or.inl (Or.inl ⟨by change 97 ≤ 101; omega, by change 101 ≤ 122; omega⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨by change 97 ≤ 116; omega, by change 116 ≤ 122; omega⟩))⟩

/-- Parenthesise each binary node. This gives a canonical, precedence-independent
    rendering of a tree, while the grammar also admits ordinary infix spelling. -/
def Expr.printPieces : Expr scope type → List PrintedToken
  | .lit value => [printInteger value]
  | .binary op left right =>
    [printOpen] ++ left.printPieces ++ [op.print] ++ right.printPieces ++ [printClose]

def Expr.printTokens (tree : Expr scope type) : List Token :=
  tree.printPieces.map PrintedToken.value

theorem Expr.printTokens_binary (op : Arith) (left right : Expr scope .integer) :
    (Expr.binary op left right).printTokens =
      [openParen] ++ left.printTokens ++ [op.token] ++ right.printTokens ++ [closeParen] := by
  simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil,
    Arith.print_value]
  rfl

theorem Expr.printAtom (tree : Expr scope type) (rest : List Token) :
    AtomReads scope (tree.printTokens ++ rest) tree rest := by
  induction tree generalizing rest with
  | lit value => exact .lit
  | binary op left right leftIH rightIH =>
    simp only [Expr.printTokens_binary, List.append_assoc, List.singleton_append]
    apply AtomReads.grouped
    apply ExprReads.atom (leftIH (op.token :: right.printTokens ++ closeParen :: rest))
    exact .binary op (Nat.zero_le _) (.atom (rightIH (closeParen :: rest))
      (.stop noOperatorAtClose)) (.stop noOperatorAtClose)

theorem Expr.printReads (tree : Expr scope type) (blocked : ¬ Continues minimum rest) :
    ExprReads scope minimum (tree.printTokens ++ rest) tree rest :=
  .atom (tree.printAtom rest) (.stop blocked)

def Stmt.printPieces : Stmt before after → List PrintedToken
  | .letValue name _ value =>
    [letName.print, name.print, printAssignment] ++ value.printPieces ++ [printSemicolon]

def Stmt.printTokens (tree : Stmt before after) : List Token :=
  tree.printPieces.map PrintedToken.value

theorem Stmt.printTokens_let (name : Identifier) (ordinary : name.val ≠ "mut".toList)
    (value : Expr scope .integer) :
    (Stmt.letValue name ordinary value).printTokens =
      [letKeyword, .word name.val, assignment] ++ value.printTokens ++ [semicolon] := by
  simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append,
    List.map_cons, List.map_nil]
  rfl

theorem Stmt.printReads (tree : Stmt before after) (rest : List Token) :
    StmtReads before (tree.printTokens ++ rest) ⟨after, tree⟩ rest := by
  cases tree with
  | letValue name ordinary value =>
    simp only [Stmt.printTokens_let, List.append_assoc, List.cons_append, List.nil_append]
    exact .letValue name ordinary (value.printReads noOperatorAtSemicolon)

end Gabbro.Core.Ast
