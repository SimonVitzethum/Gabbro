module

public import Core.Ast.Aggregate.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def TupleValueParseAussage : Prop :=
  ∀ scope, (tupleValueForm scope).ParseAussage

def TupleValueElaboriertAussage : Prop :=
  ∀ scope, (tupleValueForm scope).ElaboriertAussage

def TupleValueRealisiertAussage : Prop :=
  ∀ scope, (tupleValueForm scope).RealisiertAussage

def TupleValueAnnahmeAussage : Prop :=
  ∀ scope, (tupleValueForm scope).AnnahmeAussage

def TupleValueIdealAussage : Prop :=
  ∀ scope, (tupleValueForm scope).IdealAussage

def TupleValueEinheitAussage : Prop :=
  ∀ scope, (tupleValueForm scope).EinheitAussage

def TupleValueImplAussage : Prop :=
  ∀ scope, (tupleValueForm scope).ImplAussage

def TupleValueErhaltungAussage : Prop :=
  ∀ scope, (tupleValueForm scope).ErhaltungsAussage

def TupleValueRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := tupleValueForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TupleValueErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (tupleValueForm []).ErfuellbarAm platform start args

def TupleValueProofPacket : Prop :=
  Surface.TupleValueInversionAussage ∧
  Surface.TupleValueSuffixAussage ∧
  Surface.TupleValueDerivationAussage ∧
  TupleValueParseAussage ∧
  TupleValueElaboriertAussage ∧
  TupleValueRealisiertAussage ∧
  TupleValueAnnahmeAussage ∧
  TupleValueIdealAussage ∧
  TupleValueEinheitAussage ∧
  TupleValueImplAussage ∧
  TupleValueErhaltungAussage ∧
  TupleValueRegelSicherAussage ∧
  TupleValueErfuellbarAmAussage

def TupleFieldParseAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).ParseAussage

def TupleFieldElaboriertAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).ElaboriertAussage

def TupleFieldRealisiertAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).RealisiertAussage

def TupleFieldAnnahmeAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).AnnahmeAussage

def TupleFieldIdealAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).IdealAussage

def TupleFieldEinheitAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).EinheitAussage

def TupleFieldImplAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).ImplAussage

def TupleFieldErhaltungAussage : Prop :=
  ∀ scope, (tupleFieldForm scope).ErhaltungsAussage

def TupleFieldRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := tupleFieldForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TupleFieldErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (tupleFieldForm []).ErfuellbarAm platform start args

def TupleFieldProofPacket : Prop :=
  Surface.TupleFieldInversionAussage ∧
  Surface.TupleFieldSuffixAussage ∧
  Surface.TupleFieldDerivationAussage ∧
  TupleFieldParseAussage ∧
  TupleFieldElaboriertAussage ∧
  TupleFieldRealisiertAussage ∧
  TupleFieldAnnahmeAussage ∧
  TupleFieldIdealAussage ∧
  TupleFieldEinheitAussage ∧
  TupleFieldImplAussage ∧
  TupleFieldErhaltungAussage ∧
  TupleFieldRegelSicherAussage ∧
  TupleFieldErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
