module

public import Core.Ast.Variant.TaggedDeclProofs
public import Core.Ast.Variant.VariantValueProofs
public import Core.Ast.Variant.VariantMatchProofs
public import Core.Ast.Semantik.Kernregister

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem taggedDeclPacket : TaggedDeclProofPacket :=
  ⟨taggedDecl_inversion, taggedDecl_suffix, taggedDecl_derivation, taggedDecl_parse,
    taggedDecl_elaboriert, taggedDecl_realisiert, taggedDecl_annahme, taggedDecl_ideal,
    taggedDecl_einheit, taggedDecl_impl, taggedDecl_erhaltung, taggedDecl_regelSicher,
    taggedDecl_erfuellbarAm, taggedDecl_binding⟩

private theorem variantValuePacket : VariantValueProofPacket :=
  ⟨variantValue_inversion, variantValue_suffix, variantValue_derivation, variantValue_parse,
    variantValue_elaboriert, variantValue_realisiert, variantValue_annahme, variantValue_ideal,
    variantValue_einheit, variantValue_impl, variantValue_erhaltung, variantValue_regelSicher,
    variantValue_erfuellbarAm, variantValue_payload⟩

private theorem variantMatchPacket : VariantMatchProofPacket :=
  ⟨variantMatch_inversion, variantMatch_suffix, variantMatch_derivation, variantMatch_parse,
    variantMatch_elaboriert, variantMatch_realisiert, variantMatch_annahme, variantMatch_ideal,
    variantMatch_einheit, variantMatch_impl, variantMatch_erhaltung, variantMatch_regelSicher,
    variantMatch_erfuellbarAm, variantMatch_exhaustive, variantMatch_dispatch⟩

public def taggedDeclEntry :
    RegistryPacketEntry ``Decl.tagged (declSchema ``Decl.tagged) TaggedDeclProofPacket where
  entry := by
    simp only [declSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface taggedDecl_parse taggedDecl_elaboriert taggedDecl_realisiert, taggedDecl_annahme,
      taggedDecl_ideal, taggedDecl_einheit, taggedDecl_impl, taggedDecl_erhaltung, taggedDecl_erfuellbarAm⟩
  packetProof := taggedDeclPacket

public def variantValueEntry :
    RegistryPacketEntry ``Expr.variantValue (exprSchema ``Expr.variantValue) VariantValueProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface variantValue_parse variantValue_elaboriert variantValue_realisiert, variantValue_annahme,
      variantValue_ideal, variantValue_einheit, variantValue_impl, variantValue_erhaltung, variantValue_erfuellbarAm⟩
  packetProof := variantValuePacket

public def variantMatchEntry :
    RegistryPacketEntry ``Stmt.variantMatch (stmtSchema ``Stmt.variantMatch) VariantMatchProofPacket where
  entry := by
    simp only [stmtSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface variantMatch_parse variantMatch_elaboriert variantMatch_realisiert, variantMatch_annahme,
      variantMatch_ideal, variantMatch_einheit, variantMatch_impl, variantMatch_erhaltung, variantMatch_erfuellbarAm⟩
  packetProof := variantMatchPacket

public def buildVariantEntry :
    RegistryPacketEntry ``Befehl.baueVariante (befehlSchema ``Befehl.baueVariante) VariantValueProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (variantValue_ideal scope).1⟩, variantValue_annahme,
      variantValue_ideal, variantValue_einheit, variantValue_impl, variantValue_erhaltung, variantValue_erfuellbarAm⟩
  packetProof := variantValuePacket

public def waehleVariantEntry :
    RegistryPacketEntry ``Befehl.waehleVariante (befehlSchema ``Befehl.waehleVariante) VariantMatchProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun ctx => (variantMatch_ideal ctx).1⟩, variantMatch_annahme,
      variantMatch_ideal, variantMatch_einheit, variantMatch_impl, variantMatch_erhaltung, variantMatch_erfuellbarAm⟩
  packetProof := variantMatchPacket

public def definiereVariantEntry :
    RegistryPacketEntry ``Befehl.definiereVariante (befehlSchema ``Befehl.definiereVariante) TaggedDeclProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (taggedDecl_ideal scope).1⟩, taggedDecl_annahme,
      taggedDecl_ideal, taggedDecl_einheit, taggedDecl_impl, taggedDecl_erhaltung, taggedDecl_erfuellbarAm⟩
  packetProof := taggedDeclPacket

end Gabbro.Core.Ast.Semantik
