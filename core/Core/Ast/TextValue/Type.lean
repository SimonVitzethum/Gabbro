module

public import Core.Ast.TextValue.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

open Gabbro.Core.Text

def TextTypeInversionAussage : Prop :=
  ∀ {input type rest}, TypeReads (keyword "string" :: input) type rest →
    ∃ capacity, input = keyword "max" :: .natural capacity :: rest ∧ type = .text capacity

def TextTypeDerivationAussage : Prop :=
  ∀ capacity rest,
    TypeReads ((WrittenType.text capacity).printPieces.map PrintedToken.value ++ rest) (.text capacity) rest

def TextTypeWidenAussage : Prop :=
  ∀ source target (value : TextValue source), source ≤ target →
    ∃ widened : TextValue target,
      wertIn (.text target) ⟨.text source, value⟩ = some ⟨.text target, widened⟩ ∧
        widened.bytes = value.bytes

def TextTypeParseAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).ParseAussage

def TextTypeElaboriertAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).ElaboriertAussage

def TextTypeRealisiertAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).RealisiertAussage

def TextTypeAnnahmeAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).AnnahmeAussage

def TextTypeIdealAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).IdealAussage

def TextTypeEinheitAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).EinheitAussage

def TextTypeImplAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).ImplAussage

def TextTypeErhaltungAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).ErhaltungsAussage

def TextTypeKernOrtAussage : Prop :=
  ∀ ctx, (typeUseForm ctx textTypeUse).RegelAmOrt

def TextTypeRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := typeUseForm ctx textTypeUse
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TextTypeRegelAntwortSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := typeUseForm ctx textTypeUse
    RegelAntwortSicher (form.fragment args) platform (form.befehl args)

def TextTypeKostenUndSpurAussage : Prop :=
  ∀ ctx platform args,
    let form := typeUseForm ctx textTypeUse
    TextInstructionCost (form.fragment args) platform (form.befehl args)

def TextTypeErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (typeUseForm ([], none) textTypeUse).TextErfuellbar platform start args

def TextTypeProofPacket : Prop :=
  TextTypeParseAussage ∧
  TextTypeElaboriertAussage ∧
  TextTypeRealisiertAussage ∧
  TextTypeAnnahmeAussage ∧
  TextTypeIdealAussage ∧
  TextTypeEinheitAussage ∧
  TextTypeImplAussage ∧
  TextTypeErhaltungAussage ∧
  TextTypeKernOrtAussage ∧
  TextTypeRegelSicherAussage ∧
  TextTypeRegelAntwortSicherAussage ∧
  TextTypeKostenUndSpurAussage ∧
  TextTypeErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
