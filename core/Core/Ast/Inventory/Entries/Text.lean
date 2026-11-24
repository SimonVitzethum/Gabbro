module

public import Core.Ast.Semantik.Kernregister
public import Core.Ast.TextValue.LiteralProofs
public import Core.Ast.TextValue.ConcatProofs
public import Core.Ast.TextValue.IndexProofs
public import Core.Ast.TextValue.LengthProofs
public import Core.Ast.TextValue.SubstringProofs
public import Core.Ast.TextValue.TypeProofs

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem textLiteralPacket : TextLiteralProofPacket :=
  ⟨textLiteralInversion, textLiteralDerivation, textLiteralBytes, textLiteralParse,
    textLiteralElaboriert, textLiteralRealisiert, textLiteralAnnahme, textLiteralIdeal,
    textLiteralEinheit, textLiteralImpl, textLiteralErhaltung, textLiteralKernOrt,
    textLiteralRegelSicher, textLiteralRegelAntwortSicher, textLiteralKostenUndSpur,
    textLiteralErfuellbarAm⟩

private theorem textConcatPacket : TextConcatProofPacket :=
  ⟨textConcatInversion, textConcatDerivation, textConcatBytes, textConcatParse,
    textConcatElaboriert, textConcatRealisiert, textConcatAnnahme, textConcatIdeal,
    textConcatEinheit, textConcatImpl, textConcatErhaltung, textConcatKernOrt,
    textConcatRegelSicher, textConcatRegelAntwortSicher, textConcatKostenUndSpur,
    textConcatErfuellbarAm⟩

private theorem textIndexPacket : TextIndexProofPacket :=
  ⟨Gabbro.Core.Ast.Surface.textIndexDerivation, textIndexSuffix, textIndexBytes, textIndexParse,
    textIndexElaboriert, textIndexRealisiert, textIndexAnnahme, textIndexIdeal,
    textIndexEinheit, textIndexImpl, textIndexErhaltung, textIndexKernOrt,
    textIndexRegelSicher, textIndexRegelAntwortSicher, textIndexKostenUndSpur,
    textIndexErfuellbarAm⟩

private theorem textLengthPacket : TextLengthProofPacket :=
  ⟨textLength_inversion, textLength_derivation, textLength_bytes, textLength_parse,
    textLength_elaboriert, textLength_realisiert, textLength_annahme, textLength_ideal,
    textLength_einheit, textLength_impl, textLength_erhaltung, textLength_kernOrt,
    textLength_regelSicher, textLength_regelAntwortSicher, textLength_kostenUndSpur,
    textLength_erfuellbarAm⟩

private theorem substringPacket : SubstringProofPacket :=
  ⟨substringDerivation, substringSuffix, substringBytes, substringParse,
    substringElaboriert, substringRealisiert, substringAnnahme, substringIdeal,
    substringEinheit, substringImpl, substringErhaltung, substringKernOrt,
    substringRegelSicher, substringRegelAntwortSicher, substringKostenUndSpur,
    substringErfuellbarAm⟩

private theorem textTypePacket : TextTypeProofPacket :=
  ⟨TextTypeInversion, TextTypeDerivation, TextTypeWiden, TextTypeParse,
    TextTypeElaboriert, TextTypeRealisiert, TextTypeAnnahme, TextTypeIdeal,
    TextTypeEinheit, TextTypeImpl, TextTypeErhaltung, TextTypeKernOrt,
    TextTypeRegelSicher, TextTypeRegelAntwortSicher, TextTypeKostenUndSpur,
    TextTypeErfuellbarAm⟩

public def textLiteralEntry :
    RegistryPacketEntry ``Expr.textLiteral (exprSchema ``Expr.textLiteral) TextLiteralProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface textLiteralParse textLiteralElaboriert textLiteralRealisiert, textLiteralAnnahme,
      textLiteralIdeal, textLiteralEinheit, textLiteralImpl, textLiteralErhaltung, textLiteralErfuellbarAm⟩
  packetProof := textLiteralPacket

public def textConcatEntry :
    RegistryPacketEntry ``Expr.textConcat (exprSchema ``Expr.textConcat) TextConcatProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface textConcatParse textConcatElaboriert textConcatRealisiert, textConcatAnnahme,
      textConcatIdeal, textConcatEinheit, textConcatImpl, textConcatErhaltung, textConcatErfuellbarAm⟩
  packetProof := textConcatPacket

public def textIndexEntry :
    RegistryPacketEntry ``Expr.textIndex (exprSchema ``Expr.textIndex) TextIndexProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface textIndexParse textIndexElaboriert textIndexRealisiert, textIndexAnnahme,
      textIndexIdeal, textIndexEinheit, textIndexImpl, textIndexErhaltung, textIndexErfuellbarAm⟩
  packetProof := textIndexPacket

public def textLengthEntry :
    RegistryPacketEntry ``Expr.textLength (exprSchema ``Expr.textLength) TextLengthProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface textLength_parse textLength_elaboriert textLength_realisiert, textLength_annahme,
      textLength_ideal, textLength_einheit, textLength_impl, textLength_erhaltung, textLength_erfuellbarAm⟩
  packetProof := textLengthPacket

public def substringEntry :
    RegistryPacketEntry ``Expr.substring (exprSchema ``Expr.substring) SubstringProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface substringParse substringElaboriert substringRealisiert, substringAnnahme,
      substringIdeal, substringEinheit, substringImpl, substringErhaltung, substringErfuellbarAm⟩
  packetProof := substringPacket

public def textLiteralBefehlEntry :
    RegistryPacketEntry ``Befehl.textLiteral (befehlSchema ``Befehl.textLiteral) TextLiteralProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (textLiteralIdeal scope).1⟩, textLiteralAnnahme,
      textLiteralIdeal, textLiteralEinheit, textLiteralImpl, textLiteralErhaltung, textLiteralErfuellbarAm⟩
  packetProof := textLiteralPacket

public def textConcatBefehlEntry :
    RegistryPacketEntry ``Befehl.textConcat (befehlSchema ``Befehl.textConcat) TextConcatProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (textConcatIdeal scope).1⟩, textConcatAnnahme,
      textConcatIdeal, textConcatEinheit, textConcatImpl, textConcatErhaltung, textConcatErfuellbarAm⟩
  packetProof := textConcatPacket

public def textIndexBefehlEntry :
    RegistryPacketEntry ``Befehl.textIndex (befehlSchema ``Befehl.textIndex) TextIndexProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (textIndexIdeal scope).1⟩, textIndexAnnahme,
      textIndexIdeal, textIndexEinheit, textIndexImpl, textIndexErhaltung, textIndexErfuellbarAm⟩
  packetProof := textIndexPacket

public def textLengthBefehlEntry :
    RegistryPacketEntry ``Befehl.textLength (befehlSchema ``Befehl.textLength) TextLengthProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (textLength_ideal scope).1⟩, textLength_annahme,
      textLength_ideal, textLength_einheit, textLength_impl, textLength_erhaltung, textLength_erfuellbarAm⟩
  packetProof := textLengthPacket

public def substringBefehlEntry :
    RegistryPacketEntry ``Befehl.substring (befehlSchema ``Befehl.substring) SubstringProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (substringIdeal scope).1⟩, substringAnnahme,
      substringIdeal, substringEinheit, substringImpl, substringErhaltung, substringErfuellbarAm⟩
  packetProof := substringPacket

public theorem textTypeEntry :
    RegistryPacketProof ``Gabbro.Core.Ast.WrittenType.text TextTypeProofPacket := ⟨textTypePacket⟩

end Gabbro.Core.Ast.Semantik
