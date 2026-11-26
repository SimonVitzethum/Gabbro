module

public import Core.Ast.Aggregate.Types.Model
public import Core.Ast.Expression.Grammar
public import Core.Ast.LowLevel.TypeTokens
public import Core.Ast.Tree.Root
public import Core.Ast.Tree.Statement

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def intSpelling (signed : Bool) (width : Nat) : List Char :=
  (if signed then 'i' else 'u') :: (toString width).toList

-- Mirror printInteger.lexeme using the decimal digit tail of the width.
def intTypeName (signed : Bool) (width : Nat) : Identifier :=
  ⟨intSpelling signed width, (if signed then 'i' else 'u'), (toString width).toList, rfl, by
    cases signed <;> exact .inl (.inl ⟨by decide, by decide⟩), by
    intro c member
    right; change IsDecimalDigit c
    have member' : c ∈ Nat.toDigits 10 width := by simpa only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] using member
    have digit : c.isDigit := Nat.isDigit_of_mem_toDigits (n := width) (b := 10) (Nat.zero_lt_succ _) (Nat.le_refl _) (c := c) member'
    simpa only [IsDecimalDigit, Char.le_def, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using digit⟩

def signedPieces (number : Int) : List PrintedToken :=
  if number < 0 then [Arith.sub.print, printInteger number.natAbs] else [printInteger number.natAbs]

def printStringType : PrintedToken := printProgramWord 's' ['t', 'r', 'i', 'n', 'g']
  (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl | rfl | rfl | rfl) <;> decide)

def printMax : PrintedToken := printProgramWord 'm' ['a', 'x'] (by decide)
  (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl) <;> decide)

def printIndex : PrintedToken := printProgramWord 'i' ['n', 'd', 'e', 'x'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl | rfl) <;> decide)

def printInto : PrintedToken := printProgramWord 'i' ['n', 't', 'o'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl) <;> decide)

def printOption : PrintedToken := printProgramWord 'o' ['p', 't', 'i', 'o', 'n'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl | rfl | rfl) <;> decide)

def printPtr : PrintedToken := printProgramWord 'p' ['t', 'r'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl) <;> decide)

/-- The printed rights of a pointer type: `r`, `w`, or `rw`. -/
def PtrRecht.print : PtrRecht → PrintedToken
  | .r => printProgramWord 'r' [] (by decide) (by
      intro c absent; exact (List.not_mem_nil absent).elim)
  | .w => printProgramWord 'w' [] (by decide) (by
      intro c absent; exact (List.not_mem_nil absent).elim)
  | .rw => printProgramWord 'r' ['w'] (by decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl) <;> decide)

theorem PtrRecht.printTokens (recht : PtrRecht) : recht.print.value = recht.token := by
  cases recht <;> rfl

mutual


def WrittenType.printPieces : WrittenType → List PrintedToken
  | .bool => [printBoolType]
  | .integer signed width none => [(intTypeName signed width).print]
  | .integer signed width (some (lo, hi)) =>
    [(intTypeName signed width).print, printIn] ++ signedPieces lo ++ [printClosedRange] ++ signedPieces hi
  | .array element count => [printOpenBracket] ++ element.printPieces ++
      [printSemicolon, printInteger count, printCloseBracket]
  | .tuple first second rest => [printOpen] ++ first.printPieces ++ [printComma] ++
      second.printPieces ++ rest.printTail ++ [printClose]
  | .text capacity => [printStringType, printMax, printInteger capacity]
  | .index carrier _ => [printIndex, printInto, carrier.print]
  | .indexOption carrier _ => [printOption, printIndex, printInto, carrier.print]
  | .address space => space.printPieces
  | .ownedRegion => LowLevel.printOwnedRegion
  | .ptr space recht referent => [printPtr, Compare.lt.print, space.print, printComma,
      recht.print, Compare.gt.print] ++ referent.printPieces

def WrittenTypes.printTail : WrittenTypes → List PrintedToken
  | .empty => []
  | .next head tail => printComma :: head.printPieces ++ tail.printTail

end

inductive SignedReads : List Token → Int → List Token → Prop where
  | positive : SignedReads (.natural n :: rest) n rest
  | negative : SignedReads (minus :: .natural n :: rest) (-(n : Int)) rest

mutual

inductive TypeReads (scope : Scope) : List Token → WrittenType → List Token → Prop where
  | bool : TypeReads scope (keyword "bool" :: rest) .bool rest
  | integer (valid : (WrittenType.integer signed width none).valid scope)
      (closed : ∀ more, rest ≠ keyword "in" :: more) :
      TypeReads scope (.word (intSpelling signed width) :: rest) (.integer signed width none) rest
  | interval (valid : (WrittenType.integer signed width (some (lo, hi))).valid scope) :
      SignedReads input lo (closedRange :: more) → SignedReads more hi rest →
      TypeReads scope (.word (intSpelling signed width) :: keyword "in" :: input)
        (.integer signed width (some (lo, hi))) rest
  | array (count : Nat) (bound : Expr [] (.int count count)) :
      TypeReads scope input element (semicolon :: boundInput) →
      ExprReads [] 0 boundInput bound (closeBracket :: rest) →
      TypeReads scope (openBracket :: input) (.array element count) rest
  | tuple : TypeReads scope input first (comma :: secondInput) → TypeReads scope secondInput second more →
      TypeItemsTail scope more tail rest → TypeReads scope (openParen :: input) (.tuple first second tail) rest
  | text : TypeReads scope (keyword "string" :: keyword "max" :: .natural capacity :: rest) (.text capacity) rest
  | index (carrier : Identifier) (resolved : scope.carrierCount carrier = some count) :
      TypeReads scope (keyword "index" :: keyword "into" :: .word carrier.val :: rest) (.index carrier count) rest
  | indexOption (carrier : Identifier) (resolved : scope.carrierCount carrier = some count) :
      TypeReads scope (keyword "option" :: keyword "index" :: keyword "into" :: .word carrier.val :: rest)
        (.indexOption carrier count) rest
  | address (space : LowLevel.AddressSpace) :
      TypeReads scope (keyword "address" :: .punctuation ['<'] ::
        keyword space.name :: .punctuation ['>'] :: rest) (.address space) rest
  | ownedRegion : TypeReads scope
      (keyword "region" :: .punctuation ['<'] :: keyword "normal" :: comma ::
        keyword "rw" :: .punctuation ['>'] :: rest) .ownedRegion rest
  /-- `ptr<space, recht> referent`: the referent is a full written type.
      Only `r`, `w` and `rw` parse as rights; `x` and `own@…` have no arm. -/
  | ptr (valid : (WrittenType.ptr space recht referent).valid scope)
      (read : TypeReads scope input referent rest) :
      TypeReads scope (keyword "ptr" :: .punctuation ['<'] ::
        keyword space.name :: comma :: recht.token :: .punctuation ['>'] :: input)
        (.ptr space recht referent) rest

inductive TypeItemsTail (scope : Scope) : List Token → WrittenTypes → List Token → Prop where
  | close : TypeItemsTail scope (closeParen :: rest) .empty rest
  | comma : TypeReads scope input head more → TypeItemsTail scope more tail rest →
      TypeItemsTail scope (comma :: input) (.next head tail) rest

end

-- Mirror AtomReads.lit_inversion and exclude the signed arm by token kind.
theorem SignedReads.deterministic (left : SignedReads input a rest) (right : SignedReads input b more) :
    a = b ∧ rest = more := by
  cases left with
  | positive => cases right with | positive => exact ⟨rfl, rfl⟩
  | negative => cases right with | negative => exact ⟨rfl, rfl⟩

end Gabbro.Core.Ast
