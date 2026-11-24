module

public import Core.Ast.Aggregate.Types.CarrierTypeForms
public import Core.Ast.Variant.Values

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

def CarrierIndexOptionInversionAussage : Prop :=
  ∀ {scope input written rest}, TypeReads scope (keyword "option" :: input) written rest →
    ∃ carrier count, input = keyword "index" :: keyword "into" :: .word carrier.val :: rest ∧
      scope.carrierCount carrier = some count ∧ written = .indexOption carrier count

def CarrierIndexOptionDerivationAussage : Prop :=
  ∀ scope carrier count rest, scope.carrierCount carrier = some count →
    TypeReads scope ((WrittenType.indexOption carrier count).printPieces.map PrintedToken.value ++ rest)
      (.indexOption carrier count) rest

def CarrierIndexOptionCasesAussage : Prop :=
  ∀ count (value : Wert (indexOptionType count)),
    let cases := [some (indexType count), none]
    let observed := variantCase cases value
    (∃ present : Wert (indexType count), observed = (0, some ⟨indexType count, present⟩)) ∨
      observed = (1, none)

def CarrierIndexOptionZeroAussage : Prop :=
  Nonempty (Wert (indexOptionType 0)) ∧
    ∀ value : Wert (indexOptionType 0),
      variantCase [some (indexType 0), none] value = (1, none)

def CarrierIndexOptionParseAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).ParseAussage

def CarrierIndexOptionElaboriertAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).ElaboriertAussage

def CarrierIndexOptionRealisiertAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).RealisiertAussage

def CarrierIndexOptionAnnahmeAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).AnnahmeAussage

def CarrierIndexOptionIdealAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).IdealAussage

def CarrierIndexOptionEinheitAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).EinheitAussage

def CarrierIndexOptionImplAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).ImplAussage

def CarrierIndexOptionErhaltungAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexOptionTypeUse).ErhaltungsAussage

def CarrierIndexOptionSignatureAussage : Prop :=
  ∀ scope (args : Surface.FunctionArgs scope) frame,
    (∃ p ∈ args.parameters, indexOptionTypeUse p.written) →
    CarrierParameterEffect scope args frame

def CarrierIndexOptionRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := carrierTypeForm scope indexOptionTypeUse
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def CarrierIndexOptionErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ scope args,
    CarrierParameterErfuellbar scope indexOptionTypeUse platform start args

def CarrierIndexOptionProofPacket : Prop :=
  CarrierIndexOptionInversionAussage ∧
  CarrierIndexOptionDerivationAussage ∧
  CarrierIndexOptionCasesAussage ∧
  CarrierIndexOptionZeroAussage ∧
  CarrierIndexOptionParseAussage ∧
  CarrierIndexOptionElaboriertAussage ∧
  CarrierIndexOptionRealisiertAussage ∧
  CarrierIndexOptionAnnahmeAussage ∧
  CarrierIndexOptionIdealAussage ∧
  CarrierIndexOptionEinheitAussage ∧
  CarrierIndexOptionImplAussage ∧
  CarrierIndexOptionErhaltungAussage ∧
  CarrierIndexOptionSignatureAussage ∧
  CarrierIndexOptionRegelSicherAussage ∧
  CarrierIndexOptionErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
