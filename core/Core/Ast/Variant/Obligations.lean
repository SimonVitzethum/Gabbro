module

public import Core.Ast.Variant.Forms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def TaggedDeclParseAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).ParseAussage

def TaggedDeclElaboriertAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).ElaboriertAussage

def TaggedDeclRealisiertAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).RealisiertAussage

def TaggedDeclAnnahmeAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).AnnahmeAussage

def TaggedDeclIdealAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).IdealAussage

def TaggedDeclEinheitAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).EinheitAussage

def TaggedDeclImplAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).ImplAussage

def TaggedDeclErhaltungAussage : Prop :=
  ∀ scope, (taggedDeclForm scope).ErhaltungsAussage

def TaggedDeclRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := taggedDeclForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def TaggedDeclErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ args, (taggedDeclForm []).ErfuellbarAm platform start args

def TaggedDeclProofPacket : Prop :=
  Surface.TaggedDeclInversionAussage ∧
  Surface.TaggedDeclSuffixAussage ∧
  Surface.TaggedDeclDerivationAussage ∧
  TaggedDeclParseAussage ∧
  TaggedDeclElaboriertAussage ∧
  TaggedDeclRealisiertAussage ∧
  TaggedDeclAnnahmeAussage ∧
  TaggedDeclIdealAussage ∧
  TaggedDeclEinheitAussage ∧
  TaggedDeclImplAussage ∧
  TaggedDeclErhaltungAussage ∧
  TaggedDeclRegelSicherAussage ∧
  TaggedDeclErfuellbarAmAussage ∧
  TaggedDeclBindingAussage

def VariantValueParseAussage : Prop :=
  ∀ scope, (variantValueForm scope).ParseAussage

def VariantValueElaboriertAussage : Prop :=
  ∀ scope, (variantValueForm scope).ElaboriertAussage

def VariantValueRealisiertAussage : Prop :=
  ∀ scope, (variantValueForm scope).RealisiertAussage

def VariantValueAnnahmeAussage : Prop :=
  ∀ scope, (variantValueForm scope).AnnahmeAussage

def VariantValueIdealAussage : Prop :=
  ∀ scope, (variantValueForm scope).IdealAussage

def VariantValueEinheitAussage : Prop :=
  ∀ scope, (variantValueForm scope).EinheitAussage

def VariantValueImplAussage : Prop :=
  ∀ scope, (variantValueForm scope).ImplAussage

def VariantValueErhaltungAussage : Prop :=
  ∀ scope, (variantValueForm scope).ErhaltungsAussage

def VariantValueRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := variantValueForm scope
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def VariantValueErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ scope, ∃ args, (variantValueForm scope).ErfuellbarAm platform start args

def VariantValueProofPacket : Prop :=
  Surface.VariantValueInversionAussage ∧
  Surface.VariantValueSuffixAussage ∧
  Surface.VariantValueDerivationAussage ∧
  VariantValueParseAussage ∧
  VariantValueElaboriertAussage ∧
  VariantValueRealisiertAussage ∧
  VariantValueAnnahmeAussage ∧
  VariantValueIdealAussage ∧
  VariantValueEinheitAussage ∧
  VariantValueImplAussage ∧
  VariantValueErhaltungAussage ∧
  VariantValueRegelSicherAussage ∧
  VariantValueErfuellbarAmAussage ∧
  VariantValuePayloadAussage

def VariantMatchParseAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).ParseAussage

def VariantMatchElaboriertAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).ElaboriertAussage

def VariantMatchRealisiertAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).RealisiertAussage

def VariantMatchAnnahmeAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).AnnahmeAussage

def VariantMatchIdealAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).IdealAussage

def VariantMatchEinheitAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).EinheitAussage

def VariantMatchImplAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).ImplAussage

def VariantMatchErhaltungAussage : Prop :=
  ∀ ctx, (variantMatchForm ctx).ErhaltungsAussage

def VariantMatchRegelSicherAussage : Prop :=
  ∀ ctx platform args,
    let form := variantMatchForm ctx
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def VariantMatchErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ ctx, ∃ args, (variantMatchForm ctx).ErfuellbarAm platform start args

def VariantMatchProofPacket : Prop :=
  Surface.VariantMatchInversionAussage ∧
  Surface.VariantMatchSuffixAussage ∧
  Surface.VariantMatchDerivationAussage ∧
  VariantMatchParseAussage ∧
  VariantMatchElaboriertAussage ∧
  VariantMatchRealisiertAussage ∧
  VariantMatchAnnahmeAussage ∧
  VariantMatchIdealAussage ∧
  VariantMatchEinheitAussage ∧
  VariantMatchImplAussage ∧
  VariantMatchErhaltungAussage ∧
  VariantMatchRegelSicherAussage ∧
  VariantMatchErfuellbarAmAussage ∧
  VariantMatchExhaustiveAussage ∧
  VariantMatchDispatchAussage

end Gabbro.Core.Ast.Semantik
