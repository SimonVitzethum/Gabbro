module

public import Core.Ast.Aggregate.Forms
public import Core.Ast.Semantik.ProgramForms

@[expose] public section

namespace Gabbro.Core.Ast
open Gabbro.Core.Text

def ArrayTypeInversionAussage : Prop :=
  ∀ {input type rest}, TypeReads (openBracket :: input) type rest →
    ∃ (element : WrittenType) (count : Nat) (bound : Expr [] (.int count count)) (boundInput : List Token),
      TypeReads input element (semicolon :: boundInput) ∧
        ExprReads [] 0 boundInput bound (closeBracket :: rest) ∧ type = .array element count

def ArrayTypeSuffixAussage : Prop :=
  ∀ {input type rest}, TypeReads (openBracket :: input) type rest → rest <:+ input

def ArrayTypeDerivationAussage : Prop :=
  ∀ (element : WrittenType) (count : Nat) (rest : List Token), element.valid →
    TypeReads ((WrittenType.array element count).printPieces.map PrintedToken.value ++ rest)
      (.array element count) rest

def ArrayTypeIndexAussage : Prop :=
  ∀ (element : WrittenType) count, (WrittenType.array element count).type = .array element.type count

def ArrayTypeSyntaxErfuellbarAussage : Prop :=
  ∃ (element : WrittenType) (count : Nat) (text : RawText) (pieces : List Piece),
    (WrittenType.array element count).valid ∧ Lexed text pieces ∧
      TypeReads (canonicalTokens pieces) (.array element count) []

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

def TupleTypeSyntaxErfuellbarAussage : Prop :=
  ∃ (first second : WrittenType) (tail : WrittenTypes) (text : RawText) (pieces : List Piece),
    (WrittenType.tuple first second tail).valid ∧ Lexed text pieces ∧
      TypeReads (canonicalTokens pieces) (.tuple first second tail) []

end Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Semantik

/-- Type forms are exercised where a local declaration gives the type a use.
    The ordinary binding rule supplies its instruction and initializer. -/
def typeUseForm (ctx : Scope × Option (Ty .value)) (belongs : WrittenType → Prop) :
    Quellform (.statement ctx.1 ctx.2)
      {args : Surface.MutableLocalArgs ctx.1 ctx.2 // belongs args.written} :=
  let binding := mutableLocalForm ctx.1 ctx.2
  { produktion := ⟨fun args => binding.produktion.tree args.val,
                   fun args => binding.produktion.production args.val⟩
    befehl := fun args => binding.befehl args.val
    position := fun args => binding.position args.val }

def arrayTypeUse : WrittenType → Prop
  | .array .. => True
  | _ => False

def ArrayTypeParseAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).ParseAussage

def ArrayTypeElaboriertAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).ElaboriertAussage

def ArrayTypeRealisiertAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).RealisiertAussage

def ArrayTypeAnnahmeAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).AnnahmeAussage

def ArrayTypeIdealAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).IdealAussage

def ArrayTypeEinheitAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).EinheitAussage

def ArrayTypeImplAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).ImplAussage

def ArrayTypeErhaltungAussage : Prop :=
  ∀ ctx, (typeUseForm ctx arrayTypeUse).ErhaltungsAussage

def ArrayTypeRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := typeUseForm ctx arrayTypeUse
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def ArrayTypeErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (typeUseForm ([], none) arrayTypeUse).ErfuellbarAm platform start args

def ArrayTypeProofPacket : Prop :=
  ArrayTypeInversionAussage ∧
  ArrayTypeSuffixAussage ∧
  ArrayTypeDerivationAussage ∧
  ArrayTypeIndexAussage ∧
  ArrayTypeSyntaxErfuellbarAussage ∧
  ArrayTypeParseAussage ∧
  ArrayTypeElaboriertAussage ∧
  ArrayTypeRealisiertAussage ∧
  ArrayTypeAnnahmeAussage ∧
  ArrayTypeIdealAussage ∧
  ArrayTypeEinheitAussage ∧
  ArrayTypeImplAussage ∧
  ArrayTypeErhaltungAussage ∧
  ArrayTypeRegelSicherAussage ∧
  ArrayTypeErfuellbarAmAussage

def tupleTypeUse : WrittenType → Prop
  | .tuple .. => True
  | _ => False

def TupleTypeParseAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).ParseAussage

def TupleTypeElaboriertAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).ElaboriertAussage

def TupleTypeRealisiertAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).RealisiertAussage

def TupleTypeAnnahmeAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).AnnahmeAussage

def TupleTypeIdealAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).IdealAussage

def TupleTypeEinheitAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).EinheitAussage

def TupleTypeImplAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).ImplAussage

def TupleTypeErhaltungAussage : Prop :=
  ∀ ctx, (typeUseForm ctx tupleTypeUse).ErhaltungsAussage

def TupleTypeRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := typeUseForm ctx tupleTypeUse
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TupleTypeErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (typeUseForm ([], none) tupleTypeUse).ErfuellbarAm platform start args

def TupleTypeProofPacket : Prop :=
  TupleTypeInversionAussage ∧
  TupleTypeSuffixAussage ∧
  TupleTypeDerivationAussage ∧
  TupleTypeIndexAussage ∧
  TupleTypeSyntaxErfuellbarAussage ∧
  TupleTypeParseAussage ∧
  TupleTypeElaboriertAussage ∧
  TupleTypeRealisiertAussage ∧
  TupleTypeAnnahmeAussage ∧
  TupleTypeIdealAussage ∧
  TupleTypeEinheitAussage ∧
  TupleTypeImplAussage ∧
  TupleTypeErhaltungAussage ∧
  TupleTypeRegelSicherAussage ∧
  TupleTypeErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
