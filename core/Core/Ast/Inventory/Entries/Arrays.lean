module

public import Core.Ast.Aggregate.ArrayValueProofs
public import Core.Ast.Semantik.Kernregister

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem arrayValuePacket : ArrayValueProofPacket :=
  ⟨Surface.arrayValueInversion, Surface.arrayValueSuffix, Surface.arrayValueDerivation, Surface.arrayValueElementSound,
    arrayValueParse, arrayValueElaboriert, arrayValueRealisiert, arrayValueAnnahme,
    arrayValueIdeal, arrayValueEinheit, arrayValueImpl, arrayValueErhaltung,
    arrayValueRegelSicher, arrayValueErfuellbarAm⟩

public def arrayValueEntry :
    RegistryPacketEntry ``Expr.arrayValue (exprSchema ``Expr.arrayValue) ArrayValueProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface arrayValueParse arrayValueElaboriert arrayValueRealisiert, arrayValueAnnahme,
      arrayValueIdeal, arrayValueEinheit, arrayValueImpl, arrayValueErhaltung, arrayValueErfuellbarAm⟩
  packetProof := arrayValuePacket

public def buildArrayEntry :
    RegistryPacketEntry ``Befehl.baueArray (befehlSchema ``Befehl.baueArray) ArrayValueProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (arrayValueIdeal scope).1⟩, arrayValueAnnahme,
      arrayValueIdeal, arrayValueEinheit, arrayValueImpl, arrayValueErhaltung, arrayValueErfuellbarAm⟩
  packetProof := arrayValuePacket

end Gabbro.Core.Ast.Semantik
