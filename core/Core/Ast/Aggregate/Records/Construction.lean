module

public import Core.Ast.Aggregate.RecordForms
public import Core.Ast.Aggregate.Records.Syntax

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def RecordValueParseAussage : Prop :=
  ∀ scope, (recordValueForm scope).ParseAussage

def RecordValueElaboriertAussage : Prop :=
  ∀ scope, (recordValueForm scope).ElaboriertAussage

def RecordValueRealisiertAussage : Prop :=
  ∀ scope, (recordValueForm scope).RealisiertAussage

def RecordValueAnnahmeAussage : Prop :=
  ∀ scope, (recordValueForm scope).AnnahmeAussage

def RecordValueIdealAussage : Prop :=
  ∀ scope, (recordValueForm scope).IdealAussage

def RecordValueEinheitAussage : Prop :=
  ∀ scope, (recordValueForm scope).EinheitAussage

def RecordValueImplAussage : Prop :=
  ∀ scope, (recordValueForm scope).ImplAussage

def RecordValueErhaltungAussage : Prop :=
  ∀ scope, (recordValueForm scope).ErhaltungsAussage

def RecordValueRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := recordValueForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def RecordValueErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ scope, ∃ args, (recordValueForm scope).ErfuellbarAm platform start args

def RecordValueProofPacket : Prop :=
  Surface.RecordValueInversionAussage ∧
  Surface.RecordValueSuffixAussage ∧
  Surface.RecordValueDerivationAussage ∧
  RecordValueParseAussage ∧
  RecordValueElaboriertAussage ∧
  RecordValueRealisiertAussage ∧
  RecordValueAnnahmeAussage ∧
  RecordValueIdealAussage ∧
  RecordValueEinheitAussage ∧
  RecordValueImplAussage ∧
  RecordValueErhaltungAussage ∧
  RecordValueRegelSicherAussage ∧
  RecordValueErfuellbarAmAussage ∧
  RecordValueSlotsAussage

end Gabbro.Core.Ast.Semantik
