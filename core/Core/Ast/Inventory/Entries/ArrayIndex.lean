module

public import Core.Ast.Aggregate.ArrayIndexProofs
public import Core.Ast.Aggregate.Types.ArrayProofs
public import Core.Ast.Semantik.Kernregister

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem arrayIndexPacket : ArrayIndexProofPacket :=
  ⟨Surface.arrayIndexInversion, Surface.arrayIndexSuffix, Surface.arrayIndexDerivation,
    arrayIndexParse, arrayIndexElaboriert, arrayIndexRealisiert, arrayIndexAnnahme,
    arrayIndexIdeal, arrayIndexEinheit, arrayIndexImpl, arrayIndexErhaltung,
    arrayIndexRegelSicher, arrayIndexErfuellbarAm, arrayIndexGuard⟩

public def arrayIndexEntry :
    RegistryPacketEntry ``Expr.arrayIndex (exprSchema ``Expr.arrayIndex) ArrayIndexProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface arrayIndexParse arrayIndexElaboriert arrayIndexRealisiert, arrayIndexAnnahme,
      arrayIndexIdeal, arrayIndexEinheit, arrayIndexImpl, arrayIndexErhaltung, arrayIndexErfuellbarAm⟩
  packetProof := arrayIndexPacket

public def liesArrayEntry :
    RegistryPacketEntry ``Befehl.liesArray (befehlSchema ``Befehl.liesArray) ArrayIndexProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (arrayIndexIdeal scope).1⟩, arrayIndexAnnahme,
      arrayIndexIdeal, arrayIndexEinheit, arrayIndexImpl, arrayIndexErhaltung, arrayIndexErfuellbarAm⟩
  packetProof := arrayIndexPacket

public theorem arrayTypeEntry :
    RegistryPacketProof ``WrittenType.array ArrayTypeProofPacket :=
  ⟨⟨Gabbro.Core.Ast.arrayTypeInversion, Gabbro.Core.Ast.arrayTypeSuffix,
    Gabbro.Core.Ast.arrayTypeDerivation, Gabbro.Core.Ast.arrayTypeIndex,
    Gabbro.Core.Ast.arrayTypeSyntaxErfuellbar, arrayTypeParse, arrayTypeElaboriert,
    arrayTypeRealisiert, arrayTypeAnnahme, arrayTypeIdeal, arrayTypeEinheit, arrayTypeImpl,
    arrayTypeErhaltung, arrayTypeRegelSicher, arrayTypeErfuellbarAm⟩⟩

end Gabbro.Core.Ast.Semantik
