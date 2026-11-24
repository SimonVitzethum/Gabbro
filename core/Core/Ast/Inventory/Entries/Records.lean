module

public import Core.Ast.Aggregate.Records.RecordDeclProofs
public import Core.Ast.Aggregate.Records.ConstructionProofs
public import Core.Ast.Aggregate.Records.RecordFieldProofs
public import Core.Ast.Aggregate.Records.AssignFieldProofs
public import Core.Ast.Aggregate.Records.MutableValueProofs
public import Core.Ast.Semantik.Kernregister

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem recordValuePacket : RecordValueProofPacket :=
  ⟨Surface.RecordValueInversion, Surface.RecordValueSuffix, Surface.RecordValueDerivation,
    recordValue_parse, recordValue_elaboriert, recordValue_realisiert, recordValue_annahme,
    recordValue_ideal, recordValue_einheit, recordValue_impl, recordValue_erhaltung,
    recordValue_regelSicher, recordValue_erfuellbarAm, recordValue_slots⟩

public def recordValueEntry :
    RegistryPacketEntry ``Expr.recordValue (exprSchema ``Expr.recordValue) RecordValueProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface recordValue_parse recordValue_elaboriert recordValue_realisiert, recordValue_annahme,
      recordValue_ideal, recordValue_einheit, recordValue_impl, recordValue_erhaltung, recordValue_erfuellbarAm⟩
  packetProof := recordValuePacket

public def buildRecordValueEntry :
    RegistryPacketEntry ``Befehl.baueRecord (befehlSchema ``Befehl.baueRecord) RecordValueProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (recordValue_ideal scope).1⟩, recordValue_annahme,
      recordValue_ideal, recordValue_einheit, recordValue_impl, recordValue_erhaltung, recordValue_erfuellbarAm⟩
  packetProof := recordValuePacket

private theorem recordFieldPacket : RecordFieldProofPacket :=
  ⟨Surface.RecordFieldInversion, Surface.RecordFieldSuffix, Surface.RecordFieldDerivation,
    RecordFieldParse, RecordFieldElaboriert, RecordFieldRealisiert, RecordFieldAnnahme,
    RecordFieldIdeal, RecordFieldEinheit, RecordFieldImpl, RecordFieldErhaltung,
    RecordFieldRegelSicher, RecordFieldErfuellbarAm, RecordFieldValue⟩

public def recordFieldEntry :
    RegistryPacketEntry ``Expr.recordField (exprSchema ``Expr.recordField) RecordFieldProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface RecordFieldParse RecordFieldElaboriert RecordFieldRealisiert, RecordFieldAnnahme,
      RecordFieldIdeal, RecordFieldEinheit, RecordFieldImpl, RecordFieldErhaltung, RecordFieldErfuellbarAm⟩
  packetProof := recordFieldPacket

public def buildRecordFieldEntry :
    RegistryPacketEntry ``Befehl.liesRecordFeld (befehlSchema ``Befehl.liesRecordFeld) RecordFieldProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (RecordFieldIdeal scope).1⟩, RecordFieldAnnahme,
      RecordFieldIdeal, RecordFieldEinheit, RecordFieldImpl, RecordFieldErhaltung, RecordFieldErfuellbarAm⟩
  packetProof := recordFieldPacket

private theorem assignFieldPacket : AssignFieldProofPacket :=
  ⟨Surface.AssignFieldInversion, Surface.AssignFieldSuffix, Surface.AssignFieldDerivation,
    AssignFieldParse, AssignFieldElaboriert, AssignFieldRealisiert, AssignFieldAnnahme,
    AssignFieldIdeal, AssignFieldEinheit, AssignFieldImpl, AssignFieldErhaltung,
    AssignFieldRegelSicher, AssignFieldErfuellbarAm, AssignFieldFrame, AssignFieldProgram⟩

public def assignFieldEntry :
    RegistryPacketEntry ``Stmt.assignField (stmtSchema ``Stmt.assignField) AssignFieldProofPacket where
  entry := by
    simp only [stmtSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface AssignFieldParse AssignFieldElaboriert AssignFieldRealisiert, AssignFieldAnnahme,
      AssignFieldIdeal, AssignFieldEinheit, AssignFieldImpl, AssignFieldErhaltung, AssignFieldErfuellbarAm⟩
  packetProof := assignFieldPacket

public def buildAssignFieldEntry :
    RegistryPacketEntry ``Befehl.setzeRecordFeld (befehlSchema ``Befehl.setzeRecordFeld) AssignFieldProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun ctx => (AssignFieldIdeal ctx).1⟩, AssignFieldAnnahme,
      AssignFieldIdeal, AssignFieldEinheit, AssignFieldImpl, AssignFieldErhaltung, AssignFieldErfuellbarAm⟩
  packetProof := assignFieldPacket

private theorem mutableValuePacket : MutableValueProofPacket :=
  ⟨Surface.mutableValue_inversion, Surface.mutableValue_suffix, Surface.mutableValue_derivation,
    mutableValue_parse, mutableValue_elaboriert, mutableValue_realisiert, mutableValue_annahme,
    mutableValue_ideal, mutableValue_einheit, mutableValue_impl, mutableValue_erhaltung,
    mutableValue_regelSicher, mutableValue_erfuellbar⟩

public def mutableValueEntry :
    RegistryPacketEntry ``Stmt.letMutableValue (stmtSchema ``Stmt.letMutableValue) MutableValueProofPacket where
  entry := by
    simp only [stmtSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface mutableValue_parse mutableValue_elaboriert mutableValue_realisiert, mutableValue_annahme,
      mutableValue_ideal, mutableValue_einheit, mutableValue_impl, mutableValue_erhaltung, mutableValue_erfuellbar⟩
  packetProof := mutableValuePacket

private theorem recordDeclPacket : RecordDeclProofPacket :=
  ⟨Surface.recordDecl_inversion, Surface.recordDecl_suffix, Surface.recordDecl_derivation,
    recordDecl_parse, recordDecl_elaboriert, recordDecl_realisiert, recordDecl_annahme,
    recordDecl_ideal, recordDecl_einheit, recordDecl_impl, recordDecl_erhaltung,
    recordDecl_regelSicher, recordDecl_erfuellbar, recordDecl_binding⟩

public def recordDeclEntry :
    RegistryPacketEntry ``Decl.record (declSchema ``Decl.record) RecordDeclProofPacket where
  entry := by
    simp only [declSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface recordDecl_parse recordDecl_elaboriert recordDecl_realisiert, recordDecl_annahme,
      recordDecl_ideal, recordDecl_einheit, recordDecl_impl, recordDecl_erhaltung, recordDecl_erfuellbar⟩
  packetProof := recordDeclPacket

public def buildRecordDeclEntry :
    RegistryPacketEntry ``Befehl.definiereRecord (befehlSchema ``Befehl.definiereRecord) RecordDeclProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (recordDecl_ideal scope).1⟩, recordDecl_annahme,
      recordDecl_ideal, recordDecl_einheit, recordDecl_impl, recordDecl_erhaltung, recordDecl_erfuellbar⟩
  packetProof := recordDeclPacket

end Gabbro.Core.Ast.Semantik
