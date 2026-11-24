module

public import Core.Ast.Aggregate.Types.CarrierTypeForms

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

def CarrierIndexInversionAussage : Prop :=
  ∀ {scope input written rest}, TypeReads scope (keyword "index" :: input) written rest →
    ∃ carrier count, input = keyword "into" :: .word carrier.val :: rest ∧
      scope.carrierCount carrier = some count ∧ written = .index carrier count

def CarrierIndexDerivationAussage : Prop :=
  ∀ scope carrier count rest, scope.carrierCount carrier = some count →
    TypeReads scope ((WrittenType.index carrier count).printPieces.map PrintedToken.value ++ rest)
      (.index carrier count) rest

def CarrierIndexRangeAussage : Prop :=
  ∀ (count : Nat) (offset : Int),
    (∃ value : Wert (indexType count), value.wert = offset) ↔ 0 ≤ offset ∧ offset < (count : Int)

def CarrierIndexParseAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).ParseAussage

def CarrierIndexElaboriertAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).ElaboriertAussage

def CarrierIndexRealisiertAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).RealisiertAussage

def CarrierIndexAnnahmeAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).AnnahmeAussage

def CarrierIndexIdealAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).IdealAussage

def CarrierIndexEinheitAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).EinheitAussage

def CarrierIndexImplAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).ImplAussage

def CarrierIndexErhaltungAussage : Prop :=
  ∀ scope, (carrierTypeForm scope indexTypeUse).ErhaltungsAussage

def CarrierIndexSignatureAussage : Prop :=
  ∀ scope (args : Surface.FunctionArgs scope) frame,
    (∃ p ∈ args.parameters, indexTypeUse p.written) →
    CarrierParameterEffect scope args frame

def CarrierIndexRegelSicherAussage : Prop :=
  ∀ scope platform args,
    let form := carrierTypeForm scope indexTypeUse
    Sicherheit.RegelSicher ((form.fragment args).sicherheitsEinheit platform) (form.befehl args)

def CarrierIndexErfuellbarAmAussage : Prop :=
  ∀ platform start, ∃ scope args,
    (carrierTypeForm scope indexTypeUse).ErfuellbarAm platform start args ∧
      CarrierParameterEffect scope args.val (Rahmen.start scope)

def CarrierIndexProofPacket : Prop :=
  CarrierIndexInversionAussage ∧
  CarrierIndexDerivationAussage ∧
  CarrierIndexRangeAussage ∧
  CarrierIndexParseAussage ∧
  CarrierIndexElaboriertAussage ∧
  CarrierIndexRealisiertAussage ∧
  CarrierIndexAnnahmeAussage ∧
  CarrierIndexIdealAussage ∧
  CarrierIndexEinheitAussage ∧
  CarrierIndexImplAussage ∧
  CarrierIndexErhaltungAussage ∧
  CarrierIndexSignatureAussage ∧
  CarrierIndexRegelSicherAussage ∧
  CarrierIndexErfuellbarAmAussage

end Gabbro.Core.Ast.Semantik
