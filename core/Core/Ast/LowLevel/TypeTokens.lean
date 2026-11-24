module

public import Core.Ast.Program.HeaderTokens

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

namespace LowLevel

/-- Build the ordinary word token for a closed vocabulary whose spelling is
    checked against the same character grammar as a user-written identifier. -/
def word (head : Char) (tail : List Char) (first : isNameStart head)
    (others : ∀ c ∈ tail, isNamePart c) : PrintedToken :=
  Identifier.print ⟨head :: tail, head, tail, rfl, first, others⟩

macro "lowWord" head:char tail:str : term =>
  `(word $head ($tail).toList
    (.inl (.inl (by
      simp only [Char.le_def, UInt32.le_iff_toNat_le, UInt32.reduceToNat] <;> decide)))
    (by
      simp only [String.reduceToList, List.forall_mem_cons, List.forall_mem_nil, and_true]
      repeat' apply And.intro
      all_goals first
      | intro c absent; exact (List.not_mem_nil absent).elim
      | exact Or.inl (Or.inr rfl)
      | apply Or.inl; apply Or.inl; apply Or.inl
        simp only [Char.le_def, UInt32.le_iff_toNat_le, UInt32.reduceToNat] <;> decide
      | apply Or.inr
        simp only [Char.le_def, UInt32.le_iff_toNat_le, UInt32.reduceToNat] <;> decide))

def AddressSpace.print : AddressSpace → PrintedToken
  | .physical => lowWord 'p' "hysical"
  | .virtual => lowWord 'v' "irtual"
  | .port => lowWord 'p' "ort"
  | .guestPhysical => lowWord 'g' "uest_physical"
  | .ioVirtual => lowWord 'i' "o_virtual"

def AddressSpace.tokens (space : AddressSpace) : List Token :=
  [keyword "address", .punctuation ['<'], keyword space.name, .punctuation ['>']]

def AddressSpace.printPieces (space : AddressSpace) : List PrintedToken :=
  [lowWord 'a' "ddress", Compare.lt.print, space.print, Compare.gt.print]

theorem AddressSpace.printTokens (space : AddressSpace) :
    space.printPieces.map PrintedToken.value = space.tokens := by
  cases space <;> rfl

def ownedRegionTokens : List Token :=
  [keyword "region", .punctuation ['<'], keyword "normal", comma, keyword "rw", .punctuation ['>']]

def printOwnedRegion : List PrintedToken :=
  [lowWord 'r' "egion", Compare.lt.print, lowWord 'n' "ormal", printComma,
    lowWord 'r' "w", Compare.gt.print]

end LowLevel

end Gabbro.Core.Ast
