module

public import Core.Ast.Aggregate.RecordForms
public import Core.Ast.Aggregate.Records.Syntax

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def RecordDeclParseAussage : Prop :=
  ∀ scope, (recordDeclForm scope).ParseAussage

def RecordDeclElaboriertAussage : Prop :=
  ∀ scope, (recordDeclForm scope).ElaboriertAussage

def RecordDeclRealisiertAussage : Prop :=
  ∀ scope, (recordDeclForm scope).RealisiertAussage

def RecordDeclAnnahmeAussage : Prop :=
  ∀ scope, (recordDeclForm scope).AnnahmeAussage

def RecordDeclIdealAussage : Prop :=
  ∀ scope, (recordDeclForm scope).IdealAussage

def RecordDeclEinheitAussage : Prop :=
  ∀ scope, (recordDeclForm scope).EinheitAussage

def RecordDeclImplAussage : Prop :=
  ∀ scope, (recordDeclForm scope).ImplAussage

def RecordDeclErhaltungAussage : Prop :=
  ∀ scope, (recordDeclForm scope).ErhaltungsAussage

def RecordDeclRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := recordDeclForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def RecordDeclErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (recordDeclForm []).ErfuellbarAm platform start args

def RecordDeclProofPacket : Prop :=
  Surface.RecordDeclInversionAussage ∧
  Surface.RecordDeclSuffixAussage ∧
  Surface.RecordDeclDerivationAussage ∧
  RecordDeclParseAussage ∧
  RecordDeclElaboriertAussage ∧
  RecordDeclRealisiertAussage ∧
  RecordDeclAnnahmeAussage ∧
  RecordDeclIdealAussage ∧
  RecordDeclEinheitAussage ∧
  RecordDeclImplAussage ∧
  RecordDeclErhaltungAussage ∧
  RecordDeclRegelSicherAussage ∧
  RecordDeclErfuellbarAmAussage ∧
  RecordDeclBindingAussage

def MutableValueParseAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).ParseAussage

def MutableValueElaboriertAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).ElaboriertAussage

def MutableValueRealisiertAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).RealisiertAussage

def MutableValueAnnahmeAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).AnnahmeAussage

def MutableValueIdealAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).IdealAussage

def MutableValueEinheitAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).EinheitAussage

def MutableValueImplAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).ImplAussage

def MutableValueErhaltungAussage : Prop :=
  ∀ ctx, (mutableValueForm ctx).ErhaltungsAussage

def MutableValueRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := mutableValueForm ctx
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def MutableValueErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (mutableValueForm ([], none)).ErfuellbarAm platform start args

def MutableValueProofPacket : Prop :=
  Surface.MutableValueInversionAussage ∧
  Surface.MutableValueSuffixAussage ∧
  Surface.MutableValueDerivationAussage ∧
  MutableValueParseAussage ∧
  MutableValueElaboriertAussage ∧
  MutableValueRealisiertAussage ∧
  MutableValueAnnahmeAussage ∧
  MutableValueIdealAussage ∧
  MutableValueEinheitAussage ∧
  MutableValueImplAussage ∧
  MutableValueErhaltungAussage ∧
  MutableValueRegelSicherAussage ∧
  MutableValueErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
