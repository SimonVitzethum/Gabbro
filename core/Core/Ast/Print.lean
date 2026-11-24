module

public import Core.Ast.Expression
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

theorem punctuationHead
    (member : c ∈ ['+', '*', '(', ')', '=', ';', '{', '}', '-', '!', '<', '>', '&', '|', '[', ']', '.', ',', ':']) :
    UnquotedStart c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
  | .sub => printPunctuation "-" (by
      simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
      (fun _ same => tokenHead (c := '-') same (punctuationHead (by
        simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

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

def printBang : PrintedToken := printPunctuation "!" (by
    simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ same => tokenHead (c := '!') same (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def Compare.print (op : Compare) : PrintedToken := printPunctuation op.spelling
  (by cases op <;> simp only [Compare.spelling, punctuation, List.mem_cons,
    String.reduceEq, true_or, false_or]) (by
    intro c head
    apply punctuationHead
    cases op <;> simp only [Compare.spelling, String.reduceToList, List.head?_cons] at head <;>
      obtain rfl := Option.some.inj head <;>
      simp only [List.mem_cons, Char.reduceEq, true_or, false_or])

def Logic.print (op : Logic) : PrintedToken := printPunctuation op.spelling
  (by cases op <;> simp only [Logic.spelling, punctuation, List.mem_cons,
    String.reduceEq, true_or, false_or]) (by
    intro c head
    apply punctuationHead
    cases op <;> simp only [Logic.spelling, String.reduceToList, List.head?_cons] at head <;>
      obtain rfl := Option.some.inj head <;>
      simp only [List.mem_cons, Char.reduceEq, true_or, false_or])

def keywordName (c : Char) (rest : List Char) (lower : 'a' ≤ c ∧ c ≤ 'z')
    (lowers : ∀ a ∈ rest, 'a' ≤ a ∧ a ≤ 'z') : Identifier :=
  ⟨c :: rest, c, rest, rfl, .inl (.inl lower),
    fun a member => .inl (.inl (.inl (lowers a member)))⟩

def letName : Identifier := keywordName 'l' ['e', 't']
  (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide)

def trueName : Identifier := keywordName 't' ['r', 'u', 'e']
  (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide)

def falseName : Identifier := keywordName 'f' ['a', 'l', 's', 'e']
  (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide)

def ifName : Identifier := keywordName 'i' ['f']
  (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl <;> decide)

def elseName : Identifier := keywordName 'e' ['l', 's', 'e']
  (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide)

def returnName : Identifier := keywordName 'r' ['e', 't', 'u', 'r', 'n']
  (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)

def printOpenBracket : PrintedToken := printPunctuation "[" (by decide)
  (fun _ same => tokenHead (c := '[') same (punctuationHead (by decide)))

def printCloseBracket : PrintedToken := printPunctuation "]" (by decide)
  (fun _ same => tokenHead (c := ']') same (punctuationHead (by decide)))

def printDot : PrintedToken := printPunctuation "." (by decide)
  (fun _ same => tokenHead (c := '.') same (punctuationHead (by decide)))

def printComma : PrintedToken := printPunctuation "," (by decide)
  (fun _ same => tokenHead (c := ',') same (punctuationHead (by decide)))

def printColon : PrintedToken := printPunctuation ":" (by decide)
  (fun _ same => tokenHead (c := ':') same (punctuationHead (by decide)))

mutual

/-- Parenthesise each binary node. This gives a canonical, precedence-independent
    rendering of a tree, while the grammar also admits ordinary infix spelling. -/
def Expr.printPieces : Expr scope type → List PrintedToken
  | .lit value => [printInteger value]
  | .binary op left right =>
    [printOpen] ++ left.printPieces ++ [op.print] ++ right.printPieces ++ [printClose]
  | .trueLit => [trueName.print]
  | .falseLit => [falseName.print]
  | .variable ref _ _ => [ref.binding.name.print]
  | .negativeLit magnitude => [Arith.sub.print, printInteger magnitude]
  | .neg operand => [Arith.sub.print, printOpen] ++ operand.printPieces ++ [printClose]
  | .not operand => [printBang, printOpen] ++ operand.printPieces ++ [printClose]
  | .div left right _ =>
    [printOpen] ++ left.printPieces ++ [PrintedToken.slash] ++ right.printPieces ++ [printClose]
  | .compare op left right =>
    [printOpen] ++ left.printPieces ++ [op.print] ++ right.printPieces ++ [printClose]
  | .logic op left right =>
    [printOpen] ++ left.printPieces ++ [op.print] ++ right.printPieces ++ [printClose]
  | .arrayValue items _ _ => printOpenBracket :: items.printPieces ++ [printCloseBracket]
  | .arrayIndex base index _ _ =>
    [printOpen] ++ base.printPieces ++ [printOpenBracket] ++ index.printPieces ++
      [printCloseBracket, printClose]
  | .tupleValue first second rest =>
    [printOpen] ++ first.printPieces ++ [printComma] ++ second.printPieces ++
      rest.printTail ++ [printClose]
  | .tupleField base index =>
    [printOpen] ++ base.printPieces ++ [printDot, printInteger index.val, printClose]
  | .recordValue ref args _ _ => [ref.name.print, printOpen] ++ args.printPieces ++ [printClose]
  | .recordField base field _ _ =>
    [printOpen] ++ base.printPieces ++ [printDot, field.print, printClose]

def ExprItems.printPieces : ExprItems scope types → List PrintedToken
  | .empty => []
  | .next head tail => head.printPieces ++ tail.printTail

def ExprItems.printTail : ExprItems scope types → List PrintedToken
  | .empty => []
  | .next head tail => printComma :: head.printPieces ++ tail.printTail

def LabeledItems.printPieces : LabeledItems scope labels types → List PrintedToken
  | .empty => []
  | .next name value tail => [name.print, printColon] ++ value.printPieces ++ tail.printTail

def LabeledItems.printTail : LabeledItems scope labels types → List PrintedToken
  | .empty => []
  | .next name value tail =>
    [printComma, name.print, printColon] ++ value.printPieces ++ tail.printTail

end

def Expr.printTokens (tree : Expr scope type) : List Token :=
  tree.printPieces.map PrintedToken.value

theorem Expr.printTokens_binary (op : Arith) (left : Expr scope (.int lo₁ hi₁))
    (right : Expr scope (.int lo₂ hi₂)) :
    (Expr.binary op left right).printTokens =
      [openParen] ++ left.printTokens ++ [op.token] ++ right.printTokens ++ [closeParen] := by
  simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil,
    Arith.print_value]
  rfl

-- Extend the original Expr.printAtom using the leaf or grouped productions.
theorem Expr.printAtom (tree : Expr scope type) (rest : List Token) :
    AtomReads scope (tree.printTokens ++ rest) tree rest := by
  sorry

theorem Expr.printReads (tree : Expr scope type) (blocked : ¬ Continues minimum rest) :
    ExprReads scope minimum (tree.printTokens ++ rest) tree rest :=
  .atom (tree.printAtom rest) (.stop blocked)

end Gabbro.Core.Ast
