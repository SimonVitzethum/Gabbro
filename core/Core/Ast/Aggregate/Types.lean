module

public import Core.Ast.Aggregate.Forms

@[expose] public section

namespace Gabbro.Core.Ast
open Gabbro.Core.Text

def ArrayTypeInversionAussage : Prop :=
  ∀ {input type rest}, TypeReads (openBracket :: input) type rest →
    ∃ element count, TypeReads input element (semicolon :: .natural count :: closeBracket :: rest) ∧
      type = .array element count

def ArrayTypeSuffixAussage : Prop :=
  ∀ {input type rest}, TypeReads (openBracket :: input) type rest → rest <:+ input

def ArrayTypeDerivationAussage : Prop :=
  ∀ (element : WrittenType) (count : Nat) (rest : List Token), element.valid →
    TypeReads ((WrittenType.array element count).printPieces.map PrintedToken.value ++ rest)
      (.array element count) rest

def ArrayTypeIndexAussage : Prop :=
  ∀ (element : WrittenType) count, (WrittenType.array element count).type = .array element.type count

def ArrayTypeErfuellbarAmAussage : Prop :=
  ∃ (element : WrittenType) count text pieces,
    (WrittenType.array element count).valid ∧ Lexed text pieces ∧
      TypeReads (canonicalTokens pieces) (.array element count) []

def ArrayTypeProofPacket : Prop :=
  ArrayTypeInversionAussage ∧ ArrayTypeSuffixAussage ∧ ArrayTypeDerivationAussage ∧
    ArrayTypeIndexAussage ∧ ArrayTypeErfuellbarAmAussage

def TupleTypeInversionAussage : Prop :=
  ∀ {input type rest}, TypeReads (openParen :: input) type rest →
    ∃ first second tail secondInput more,
      TypeReads input first (comma :: secondInput) ∧ TypeReads secondInput second more ∧
        TypeItemsTail more tail rest ∧ type = .tuple first second tail

def TupleTypeSuffixAussage : Prop :=
  ∀ {input type rest}, TypeReads (openParen :: input) type rest → rest <:+ input

def TupleTypeDerivationAussage : Prop :=
  ∀ (first second : WrittenType) (tail : WrittenTypes) (rest : List Token),
    (WrittenType.tuple first second tail).valid →
      TypeReads ((WrittenType.tuple first second tail).printPieces.map PrintedToken.value ++ rest)
        (.tuple first second tail) rest

def TupleTypeIndexAussage : Prop :=
  ∀ (first second : WrittenType) (tail : WrittenTypes),
    (WrittenType.tuple first second tail).type = tupleType (first.type :: second.type :: tail.types)

def TupleTypeErfuellbarAmAussage : Prop :=
  ∃ (first second : WrittenType) tail text pieces,
    (WrittenType.tuple first second tail).valid ∧ Lexed text pieces ∧
      TypeReads (canonicalTokens pieces) (.tuple first second tail) []

def TupleTypeProofPacket : Prop :=
  TupleTypeInversionAussage ∧ TupleTypeSuffixAussage ∧ TupleTypeDerivationAussage ∧
    TupleTypeIndexAussage ∧ TupleTypeErfuellbarAmAussage

end Gabbro.Core.Ast
