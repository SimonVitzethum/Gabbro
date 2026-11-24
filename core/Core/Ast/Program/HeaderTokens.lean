module

public import Core.Ast.Print

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def arrow : Token := .punctuation "->".toList
def closedRange : Token := .punctuation "..".toList
def openRange : Token := .punctuation "..<".toList

def keyword (word : String) : Token := .word word.toList

theorem programPunctuationHead (member : c ∈ [':', ',', '-', '.']) : UnquotedStart c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true]
    | intro h
      cases h

def printArrow : PrintedToken := printPunctuation "->" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same; obtain rfl : '-' = c := Option.some.inj (by simpa using same)
  exact programPunctuationHead (by
    simp only [List.mem_cons, List.not_mem_nil, Char.reduceEq, true_or, false_or]))
def printClosedRange : PrintedToken := printPunctuation ".." (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same; obtain rfl : '.' = c := Option.some.inj (by simpa using same)
  exact programPunctuationHead (by
    simp only [List.mem_cons, List.not_mem_nil, Char.reduceEq, true_or, false_or]))
def printOpenRange : PrintedToken := printPunctuation "..<" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same; obtain rfl : '.' = c := Option.some.inj (by simpa using same)
  exact programPunctuationHead (by
    simp only [List.mem_cons, List.not_mem_nil, Char.reduceEq, true_or, false_or]))

/-- The finite keywords used by these productions are unquoted words. -/
def printProgramWord (head : Char) (tail : List Char) (first : 'a' ≤ head ∧ head ≤ 'z')
    (rest : ∀ c ∈ tail, 'a' ≤ c ∧ c ≤ 'z') : PrintedToken :=
  (keywordName head tail first rest).print

-- Mirror returnName and the punctuationHead lemma for each new terminal.
def printConst : PrintedToken := printProgramWord 'c' ['o', 'n', 's', 't'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide)
def printFn : PrintedToken := printProgramWord 'f' ['n'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printBoolType : PrintedToken := printProgramWord 'b' ['o', 'o', 'l'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide)
def printIn : PrintedToken := printProgramWord 'i' ['n'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printMut : PrintedToken := printProgramWord 'm' ['u', 't'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printWhile : PrintedToken := printProgramWord 'w' ['h', 'i', 'l', 'e'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide)
def printBounded : PrintedToken := printProgramWord 'b' ['o', 'u', 'n', 'd', 'e', 'd'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
def printOps : PrintedToken := printProgramWord 'o' ['p', 's'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printFor : PrintedToken := printProgramWord 'f' ['o', 'r'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printDecreases : PrintedToken :=
  printProgramWord 'd' ['e', 'c', 'r', 'e', 'a', 's', 'e', 's'] (by decide) (by
    intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

-- Mirror Identifier.print with an underscore allowed in the tail.
def printOnExceeded : PrintedToken :=
  Identifier.print ⟨"on_exceeded".toList, 'o', "n_exceeded".toList, rfl, by
    exact .inl (.inl ⟨by decide, by decide⟩), by
    intro c member; simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact .inl (.inr rfl) | exact .inl (.inl (.inl ⟨by decide, by decide⟩))⟩

end Gabbro.Core.Ast
