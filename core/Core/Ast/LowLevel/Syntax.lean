module

public import Core.Ast.ProgramHeader
public import Core.Text.Syntax
public import Core.Katalog.FirmwareNamen

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog

/-- The space indexes inert address data. Arithmetic and executable operands
    have separate rules; this index never carries authority. -/
inductive AddressSpace where
  | physical
  | virtual
  | port
  | guestPhysical
  | ioVirtual
  deriving DecidableEq, Repr

def AddressSpace.name : AddressSpace → String
  | .physical => "physical"
  | .virtual => "virtual"
  | .port => "port"
  | .guestPhysical => "guest_physical"
  | .ioVirtual => "io_virtual"

inductive Form where
  | addressType
  | regionAddress
  | view
  | environment
  deriving DecidableEq

/-- Low-level leaves of the reference AST. The category index keeps the type,
    expression and declaration entry points distinct during their development. -/
inductive Tree : Form → Type where
  /-- `address<S>`, with bounds from the named space on the selected target. -/
  | addressType (space : AddressSpace) : Tree .addressType
  /-- `r.address()`, the inert physical start of the held region `r`. -/
  | regionAddress (region : Identifier) : Tree .regionAddress
  /-- `r.view as T`, which borrows a normal region under the checked layout of `T`. -/
  | view (region : Identifier) (type : WrittenType) : Tree .view
  /-- `environment name abi ABI = catalogue ROW;`, with no contract in the source tree. -/
  | environment (name : Identifier) (abi : DienstAbi) (row : FirmwareZeile) : Tree .environment

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

def printFirmwareRow : FirmwareZeile → PrintedToken
  | .biosServices => lowWord 'b' "ios_services"
  | .uefi210 => lowWord 'u' "efi_2_10"
  | .psci => lowWord 'p' "sci"
  | .sbi => lowWord 's' "bi"

def printFirmwareAbi : DienstAbi → PrintedToken
  | .biosInterrupt => lowWord 'b' "ios_int"
  | .efiX64 => lowWord 'u' "efi_x64"
  | .efiAapcs => lowWord 'u' "efi_aapcs"
  | .psciSmc => lowWord 'p' "sci_smc"
  | .sbiEcall => lowWord 's' "bi_ecall"

def Tree.printPieces : Tree form → List PrintedToken
  | .addressType space => [lowWord 'a' "ddress", (Compare.lt).print, space.print, (Compare.gt).print]
  | .regionAddress region => [region.print, printDot, lowWord 'a' "ddress", printOpen, printClose]
  | .view region type => [region.print, printDot, lowWord 'v' "iew", lowWord 'a' "s"] ++ type.printPieces
  | .environment name abi row =>
    [lowWord 'e' "nvironment", name.print, lowWord 'a' "bi", printFirmwareAbi abi,
      printAssignment, lowWord 'c' "atalogue", printFirmwareRow row, printSemicolon]

/-- Exact productions over canonical tokens. The type in a view uses the
    existing type grammar rather than a second interpretation of type syntax. -/
def Tree.production : Tree form → List Token → Prop
  | .addressType space => fun tokens =>
      tokens = [keyword "address", .punctuation ['<'], keyword space.name, .punctuation ['>']]
  | .regionAddress region => fun tokens =>
      tokens = [.word region.val, dot, keyword "address", openParen, closeParen]
  | .view region type => fun tokens =>
      ∃ input, tokens = [.word region.val, dot, keyword "view", keyword "as"] ++ input ∧
        TypeReads [] input type []
  | .environment name abi row => fun tokens =>
      tokens = [keyword "environment", .word name.val, keyword "abi", keyword abi.name,
        assignment, keyword "catalogue", keyword row.name, semicolon]

def Parse (text : RawText) (tree : Tree form) : Prop :=
  Text.Parse (tokenGrammar (fun tokens (tree : Tree form) => tree.production tokens)) text tree

def Tree.print (tree : Tree form) : RawText := PrintedToken.render tree.printPieces

end Gabbro.Core.Ast.LowLevel
