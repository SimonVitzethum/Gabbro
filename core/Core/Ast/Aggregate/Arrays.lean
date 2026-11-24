module

public import Core.Ast.Aggregate.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def ArrayValueParseAussage : Prop :=
  ∀ scope, (arrayValueForm scope).ParseAussage

def ArrayValueElaboriertAussage : Prop :=
  ∀ scope, (arrayValueForm scope).ElaboriertAussage

def ArrayValueRealisiertAussage : Prop :=
  ∀ scope, (arrayValueForm scope).RealisiertAussage

def ArrayValueAnnahmeAussage : Prop :=
  ∀ scope, (arrayValueForm scope).AnnahmeAussage

def ArrayValueIdealAussage : Prop :=
  ∀ scope, (arrayValueForm scope).IdealAussage

def ArrayValueEinheitAussage : Prop :=
  ∀ scope, (arrayValueForm scope).EinheitAussage

def ArrayValueImplAussage : Prop :=
  ∀ scope, (arrayValueForm scope).ImplAussage

def ArrayValueErhaltungAussage : Prop :=
  ∀ scope, (arrayValueForm scope).ErhaltungsAussage

def ArrayValueRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := arrayValueForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def ArrayValueErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (arrayValueForm []).ErfuellbarAm platform start args

def ArrayValueProofPacket : Prop :=
  Surface.ArrayValueInversionAussage ∧
  Surface.ArrayValueSuffixAussage ∧
  Surface.ArrayValueDerivationAussage ∧
  Surface.ArrayValueElementSoundAussage ∧
  ArrayValueParseAussage ∧
  ArrayValueElaboriertAussage ∧
  ArrayValueRealisiertAussage ∧
  ArrayValueAnnahmeAussage ∧
  ArrayValueIdealAussage ∧
  ArrayValueEinheitAussage ∧
  ArrayValueImplAussage ∧
  ArrayValueErhaltungAussage ∧
  ArrayValueRegelSicherAussage ∧
  ArrayValueErfuellbarAmAussage

def ArrayIndexParseAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).ParseAussage

def ArrayIndexElaboriertAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).ElaboriertAussage

def ArrayIndexRealisiertAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).RealisiertAussage

def ArrayIndexAnnahmeAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).AnnahmeAussage

def ArrayIndexIdealAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).IdealAussage

def ArrayIndexEinheitAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).EinheitAussage

def ArrayIndexImplAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).ImplAussage

def ArrayIndexErhaltungAussage : Prop :=
  ∀ scope, (arrayIndexForm scope).ErhaltungsAussage

def ArrayIndexRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := arrayIndexForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def ArrayIndexErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (arrayIndexForm []).ErfuellbarAm platform start args

def ArrayIndexProofPacket : Prop :=
  Surface.ArrayIndexInversionAussage ∧
  Surface.ArrayIndexSuffixAussage ∧
  Surface.ArrayIndexDerivationAussage ∧
  ArrayIndexParseAussage ∧
  ArrayIndexElaboriertAussage ∧
  ArrayIndexRealisiertAussage ∧
  ArrayIndexAnnahmeAussage ∧
  ArrayIndexIdealAussage ∧
  ArrayIndexEinheitAussage ∧
  ArrayIndexImplAussage ∧
  ArrayIndexErhaltungAussage ∧
  ArrayIndexRegelSicherAussage ∧
  ArrayIndexErfuellbarAmAussage ∧
  ArrayIndexGuardAussage

end Gabbro.Core.Ast.Semantik
