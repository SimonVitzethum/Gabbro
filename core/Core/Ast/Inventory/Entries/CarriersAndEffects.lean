module

public import Core.Ast.Aggregate.Carrier.TableProofs
public import Core.Ast.Aggregate.Carrier.Effects.GroupProofs
public import Core.Ast.Aggregate.Carrier.Effects.InferenceProofs
public import Core.Ast.Aggregate.Types.CarrierIndexProofs
public import Core.Ast.Aggregate.Types.CarrierIndexOptionProofs
public import Core.Ast.Semantik.Kernregister

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem tablePacket : TableProofPacket :=
  ⟨tableInversion, tableDerivation, tableScope, tableBinding, tableParse, tableElaboriert,
    tableRealisiert, tableAnnahme, tableIdeal, tableEinheit, tableImpl, tableErhaltung,
    tableRegelSicher, tableErfuellbarAm⟩

public def tableEntry :
    RegistryPacketEntry ``Decl.table (declSchema ``Decl.table) TableProofPacket where
  entry := by
    simp only [declSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface tableParse tableElaboriert tableRealisiert, tableAnnahme,
      tableIdeal, tableEinheit, tableImpl, tableErhaltung, tableErfuellbarAm⟩
  packetProof := tablePacket

public def buildTableEntry :
    RegistryPacketEntry ``Befehl.definiereTraeger (befehlSchema ``Befehl.definiereTraeger) TableProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (tableIdeal scope).1⟩, tableAnnahme,
      tableIdeal, tableEinheit, tableImpl, tableErhaltung, tableErfuellbarAm⟩
  packetProof := tablePacket

private theorem effectGroupPacket : EffectGroupProofPacket :=
  ⟨effectGroup_inversion, effectGroup_derivation, effectGroup_scope, effectGroup_expansion,
    effectGroup_visibility, effectGroup_capture, effectGroup_signature, effectGroup_inferred,
    effectGroup_call, effectGroup_binding, effectGroup_parse, effectGroup_elaboriert,
    effectGroup_realisiert, effectGroup_annahme, effectGroup_ideal, effectGroup_einheit,
    effectGroup_impl, effectGroup_erhaltung, effectGroup_regelSicher, effectGroup_erfuellbarAm,
    effectGroup_useErfuellbar⟩

public def effectGroupEntry :
    RegistryPacketEntry ``Decl.effectGroup (declSchema ``Decl.effectGroup) EffectGroupProofPacket where
  entry := by
    simp only [declSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface effectGroup_parse effectGroup_elaboriert effectGroup_realisiert, effectGroup_annahme,
      effectGroup_ideal, effectGroup_einheit, effectGroup_impl, effectGroup_erhaltung, effectGroup_erfuellbarAm⟩
  packetProof := effectGroupPacket

public def buildEffectGroupEntry :
    RegistryPacketEntry ``Befehl.definiereEffektgruppe (befehlSchema ``Befehl.definiereEffektgruppe) EffectGroupProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (effectGroup_ideal scope).1⟩, effectGroup_annahme,
      effectGroup_ideal, effectGroup_einheit, effectGroup_impl, effectGroup_erhaltung, effectGroup_erfuellbarAm⟩
  packetProof := effectGroupPacket

private theorem carrierIndexPacket : CarrierIndexProofPacket :=
  ⟨carrierIndexInversion, carrierIndexDerivation, carrierIndexRange, carrierIndexParse,
    carrierIndexElaboriert, carrierIndexRealisiert, carrierIndexAnnahme, carrierIndexIdeal,
    carrierIndexEinheit, carrierIndexImpl, carrierIndexErhaltung, carrierIndexSignature,
    carrierIndexRegelSicher, carrierIndexErfuellbarAm⟩

public theorem carrierIndexEntry : RegistryPacketProof ``WrittenType.index CarrierIndexProofPacket :=
  ⟨carrierIndexPacket⟩

private theorem carrierIndexOptionPacket : CarrierIndexOptionProofPacket :=
  ⟨carrierIndexOptionInversion, carrierIndexOptionDerivation, carrierIndexOptionCases,
    carrierIndexOptionZero, carrierIndexOptionParse, carrierIndexOptionElaboriert,
    carrierIndexOptionRealisiert, carrierIndexOptionAnnahme, carrierIndexOptionIdeal,
    carrierIndexOptionEinheit, carrierIndexOptionImpl, carrierIndexOptionErhaltung,
    carrierIndexOptionSignature, carrierIndexOptionRegelSicher, carrierIndexOptionErfuellbarAm⟩

public theorem carrierIndexOptionEntry : RegistryPacketProof ``WrittenType.indexOption CarrierIndexOptionProofPacket :=
  ⟨carrierIndexOptionPacket⟩

end Gabbro.Core.Ast.Semantik
