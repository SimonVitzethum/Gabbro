module
public meta import Lean
meta import Lean.Elab.Task
meta import Core.Ast.Inventory.Entries.ArrayIndex
meta import Core.Ast.Inventory.Entries.Arrays
meta import Core.Ast.Inventory.Entries.CarriersAndEffects
meta import Core.Ast.Inventory.Entries.Option
meta import Core.Ast.Inventory.Entries.OwnedRegionType
meta import Core.Ast.Inventory.Entries.Variants
meta import Core.Ast.Inventory.Entries.Records
meta import Core.Ast.Inventory.Entries.Tuples
meta import Core.Ast.Inventory.Entries.WrittenTypeStatements
meta import Core.Ast.Inventory.Entries.Text
meta import Core.Ast.Inventory.Entries.ScalarTypes
meta import Core.Ast.LowLevel.Mem.Proofs.Entries
meta import Core.Ast.LowLevel.Exec.Registry
meta import Core.Ast.LowLevel.Exec.Proofs.ExecKern
meta import Core.Verfeinerung.Formen.Registry
public meta import Core.Waechter.Closing
public meta import Core.Waechter.Decision
public meta import Core.Waechter.Pins
public meta import Core.Waechter.PinTable
public meta import Core.Waechter.Registry
public meta import Core.Waechter.Safety
public meta import Core.Waechter.Semantics

open Lean Elab Command

namespace Gabbro.Core.Waechter

private meta def pins : Array (Name × UInt64) := pinTable

private meta def safety : Array Name := #[
  `Gabbro.Core.Sicherheit.RegelSicher, `Gabbro.Core.Sicherheit.RegelAntwortSicher,
  `Gabbro.Core.Sicherheit.RegelPflichten,
  `Gabbro.Core.Sicherheit.Speichersicher, `Gabbro.Core.Sicherheit.InvariantenErhalten,
  `Gabbro.Core.Sicherheit.Rennfrei, `Gabbro.Core.Sicherheit.ToctouFrei]

private meta def acceptance : AcceptanceSpec := {
  acceptance := #[
    `Gabbro.Core.Annahme.RegelLokal,
    `Gabbro.Core.Annahme.BefugtOrt,
    `Gabbro.Core.Annahme.Befugt,
    `Gabbro.Core.Annahme.AussengriffeEigen,
    `Gabbro.Core.Annahme.AussenKontextLokal,
    `Gabbro.Core.Annahme.AussenGueltig,
    `Gabbro.Core.Annahme.AussenLokal,
    `Gabbro.Core.Annahme.Lokal,
    `Gabbro.Core.Beobachtung.niedereAussensicht,
    `Gabbro.Core.Beobachtung.startProjektion,
    `Gabbro.Core.Beobachtung.NiedrigGleich,
    `Gabbro.Core.Beobachtung.LokaleGleich,
    `Gabbro.Core.Beobachtung.EndeSicht,
    `Gabbro.Core.Beobachtung.AntwortSicht,
    `Gabbro.Core.Beobachtung.QuellzustandGleich,
    `Gabbro.Core.Beobachtung.StartFlussLokal,
    `Gabbro.Core.Beobachtung.PlanSicht,
    `Gabbro.Core.Beobachtung.AusgabeZuwachs,
    `Gabbro.Core.Beobachtung.AusgabeSicht,
    `Gabbro.Core.Beobachtung.AusgabeLokal,
    `Gabbro.Core.Beobachtung.FormSchritt,
    `Gabbro.Core.Beobachtung.RegelFluss,
    `Gabbro.Core.Beobachtung.FlussLokal,
    `Gabbro.Core.Annahme.stale_griff_ungueltig,
    `Gabbro.Core.Annahme.fruehere_provenienz_verweigert,
    `Gabbro.Core.Annahme.fruehere_ableitung_verweigert,
    `Gabbro.Core.Annahme.KlauselTabelle,
    `Gabbro.Core.Annahme.kanonischeKlauseln,
    `Gabbro.Core.Annahme.KlauselnWahr,
    `Gabbro.Core.Annahme.waechterBedarf,
    `Gabbro.Core.Annahme.GuardVerwendung,
    `Gabbro.Core.Annahme.kanonischeVerwendung,
    `Gabbro.Core.Annahme.InternBlockiert,
    `Gabbro.Core.Annahme.GeschlossenWartend,
    `Gabbro.Core.Annahme.WaechterHalten,
    `Gabbro.Core.Annahme.Akzeptiert,
    `Gabbro.Core.Annahme.akzeptiert_katalog],
  syntaxModules := #[`Core.Ast],
  -- `Core.Speicher` is the shared M3 state foundation both machines step over: `I` runs
  -- quantify over `Zustand`, so the ideal layer includes it.
  idealModules := #[`Core.Maschine, `Core.Ideal, `Core.Speicher],
  catalogueModules := #[`Core.Katalog, `Core.Aussen],
  forbidden := #[
    `Gabbro.Core.Maschine.ImplSchritt, `Gabbro.Core.Maschine.Lauffolge,
    `Gabbro.Core.Maschine.Lauf, `Gabbro.Core.Maschine.Laeufe, `Gabbro.Core.Maschine.Schnitt,
    `Gabbro.Core.Maschine.System.ImplSchritt, `Gabbro.Core.Maschine.System.ImplErreichbar,
    `Gabbro.Core.Maschine.Regel.impl, `Gabbro.Core.Maschine.Einheit.laden],
  forbiddenModules := #[`Core.Verfeinerung, `Core.Sicherheit],
  ideal := #[`Gabbro.Core.Maschine.I.Schritt, `Gabbro.Core.Maschine.I.start, `Gabbro.Core.Maschine.I.Laeufe] }
private meta def registry : Array RegistryFamily := #[
  ⟨`Gabbro.Core.Ast.LowLevel.MemTree, `Gabbro.Core.Ast.LowLevel.schemaMem, #[
    (`Gabbro.Core.Ast.LowLevel.MemTree.splitAt, `Gabbro.Core.Ast.LowLevel.splitAtEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.splitPages, `Gabbro.Core.Ast.LowLevel.splitPagesEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.merge, `Gabbro.Core.Ast.LowLevel.mergeEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.newSpace, `Gabbro.Core.Ast.LowLevel.newSpaceEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.mapSpace, `Gabbro.Core.Ast.LowLevel.mapEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.protectSpace, `Gabbro.Core.Ast.LowLevel.protectEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.unmapSpace, `Gabbro.Core.Ast.LowLevel.unmapEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.flushSpace, `Gabbro.Core.Ast.LowLevel.flushEntry),
    (`Gabbro.Core.Ast.LowLevel.MemTree.activateSpace, `Gabbro.Core.Ast.LowLevel.activateEntry)], #[]⟩,
  ⟨`Gabbro.Core.Ast.LowLevel.ExecTree, `Gabbro.Core.Ast.LowLevel.schemaExec, #[], #[
    (`Gabbro.Core.Ast.LowLevel.ExecTree.stateDecl, `Gabbro.Core.Ast.LowLevel.StateDeclAussage),
    (`Gabbro.Core.Ast.LowLevel.ExecTree.jump, `Gabbro.Core.Ast.LowLevel.JumpAussage),
    (`Gabbro.Core.Ast.LowLevel.ExecTree.jumpLong, `Gabbro.Core.Ast.LowLevel.JumpLongAussage),
    (`Gabbro.Core.Ast.LowLevel.ExecTree.waitInterrupt, `Gabbro.Core.Ast.LowLevel.WaitAussage),
    (`Gabbro.Core.Ast.LowLevel.ExecTree.stopCore, `Gabbro.Core.Ast.LowLevel.StopAussage),
    (`Gabbro.Core.Ast.LowLevel.ExecTree.entryDecl, `Gabbro.Core.Ast.LowLevel.EntryAussage)]⟩,
  ⟨`Gabbro.Core.Ast.LowLevel.Tree, `Gabbro.Core.Ast.LowLevel.schema, #[
    (`Gabbro.Core.Ast.LowLevel.Tree.addressType, `Gabbro.Core.Ast.LowLevel.addressTypeTreeEntry),
    (`Gabbro.Core.Ast.LowLevel.Tree.regionAddress, `Gabbro.Core.Ast.LowLevel.regionAddressTreeEntry),
    (`Gabbro.Core.Ast.LowLevel.Tree.view, `Gabbro.Core.Ast.LowLevel.viewTreeEntry),
    (`Gabbro.Core.Ast.LowLevel.Tree.environment, `Gabbro.Core.Ast.LowLevel.environmentTreeEntry)], #[]⟩,
  ⟨`Gabbro.Core.Ast.Expr, `Gabbro.Core.Ast.Semantik.exprSchema, #[
    (`Gabbro.Core.Ast.Expr.lit, `Gabbro.Core.Ast.Semantik.literalEntry),
    (`Gabbro.Core.Ast.Expr.binary, `Gabbro.Core.Ast.Semantik.binaryEntry),
    (`Gabbro.Core.Ast.Expr.trueLit, `Gabbro.Core.Ast.Semantik.trueLitEntry),
    (`Gabbro.Core.Ast.Expr.falseLit, `Gabbro.Core.Ast.Semantik.falseLitEntry),
    (`Gabbro.Core.Ast.Expr.variable, `Gabbro.Core.Ast.Semantik.variableEntry),
    (`Gabbro.Core.Ast.Expr.negativeLit, `Gabbro.Core.Ast.Semantik.negativeLitEntry),
    (`Gabbro.Core.Ast.Expr.neg, `Gabbro.Core.Ast.Semantik.negEntry),
    (`Gabbro.Core.Ast.Expr.not, `Gabbro.Core.Ast.Semantik.notValueEntry),
    (`Gabbro.Core.Ast.Expr.div, `Gabbro.Core.Ast.Semantik.divisionEntry),
    (`Gabbro.Core.Ast.Expr.compare, `Gabbro.Core.Ast.Semantik.comparisonEntry),
    (`Gabbro.Core.Ast.Expr.logic, `Gabbro.Core.Ast.Semantik.logicEntry) ], #[]⟩,
  ⟨`Gabbro.Core.Ast.Stmt, `Gabbro.Core.Ast.Semantik.stmtSchema, #[
    (`Gabbro.Core.Ast.Stmt.letValue, `Gabbro.Core.Ast.Semantik.letEntry),
    (`Gabbro.Core.Ast.Stmt.assignVar, `Gabbro.Core.Ast.Semantik.assignVarEntry),
    (`Gabbro.Core.Ast.Stmt.ret, `Gabbro.Core.Ast.Semantik.returnValueEntry),
    (`Gabbro.Core.Ast.Stmt.ite, `Gabbro.Core.Ast.Semantik.ifElseEntry),
    (`Gabbro.Core.Ast.Stmt.retVoid, `Gabbro.Core.Ast.Semantik.returnVoidEntry),
    (`Gabbro.Core.Ast.Stmt.letMutable, `Gabbro.Core.Ast.Semantik.mutableLocalEntry),
    (`Gabbro.Core.Ast.Stmt.directCall, `Gabbro.Core.Ast.Semantik.directCallEntry),
    (`Gabbro.Core.Ast.Stmt.bindDirect, `Gabbro.Core.Ast.Semantik.bindDirectEntry),
    (`Gabbro.Core.Ast.Stmt.whileBounded, `Gabbro.Core.Ast.Semantik.boundedWhileEntry),
    (`Gabbro.Core.Ast.Stmt.forRange, `Gabbro.Core.Ast.Semantik.forRangeEntry) ], #[
    (`Gabbro.Core.Ast.Stmt.letRegion, `Gabbro.Core.Ast.Semantik.RegionBindUnitAussage) ]⟩,
  ⟨`Gabbro.Core.Ast.Decl, `Gabbro.Core.Ast.Semantik.declSchema, #[
    (`Gabbro.Core.Ast.Decl.constant, `Gabbro.Core.Ast.Semantik.constantEntry),
    (`Gabbro.Core.Ast.Decl.function, `Gabbro.Core.Ast.Semantik.functionEntry),
    (`Gabbro.Core.Ast.Decl.environment, `Gabbro.Core.Ast.Semantik.environmentDeclEntry) ], #[]⟩,
  ⟨`Gabbro.Core.Ast.BracedBlock, `Gabbro.Core.Ast.Semantik.bracedSchema, #[
    (`Gabbro.Core.Ast.BracedBlock.braces, `Gabbro.Core.Ast.Semantik.bracedEntry) ], #[]⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl, `Gabbro.Core.Ast.Semantik.befehlSchema, #[
    (`Gabbro.Core.Ast.Semantik.Befehl.literal, `Gabbro.Core.Ast.Semantik.kernLiteralEntry),
    (`Gabbro.Core.Ast.Semantik.Befehl.binaer, `Gabbro.Core.Ast.Semantik.kernBinaryEntry),
    (`Gabbro.Core.Ast.Semantik.Befehl.binden, `Gabbro.Core.Ast.Semantik.kernLetEntry),
    (`Gabbro.Core.Ast.Semantik.Befehl.wahrheitswert, `Gabbro.Core.Ast.Semantik.kern_wahrheitswert),
    (`Gabbro.Core.Ast.Semantik.Befehl.lesen, `Gabbro.Core.Ast.Semantik.kern_lesen),
    (`Gabbro.Core.Ast.Semantik.Befehl.negativ, `Gabbro.Core.Ast.Semantik.kern_negativ),
    (`Gabbro.Core.Ast.Semantik.Befehl.negieren, `Gabbro.Core.Ast.Semantik.kern_negieren),
    (`Gabbro.Core.Ast.Semantik.Befehl.verneinen, `Gabbro.Core.Ast.Semantik.kern_verneinen),
    (`Gabbro.Core.Ast.Semantik.Befehl.teilen, `Gabbro.Core.Ast.Semantik.kern_teilen),
    (`Gabbro.Core.Ast.Semantik.Befehl.vergleichen, `Gabbro.Core.Ast.Semantik.kern_vergleichen),
    (`Gabbro.Core.Ast.Semantik.Befehl.springeWenn, `Gabbro.Core.Ast.Semantik.kern_springeWenn),
    (`Gabbro.Core.Ast.Semantik.Befehl.zuweisen, `Gabbro.Core.Ast.Semantik.kern_zuweisen),
    (`Gabbro.Core.Ast.Semantik.Befehl.zurueck, `Gabbro.Core.Ast.Semantik.kern_zurueck),
    (`Gabbro.Core.Ast.Semantik.Befehl.springe, `Gabbro.Core.Ast.Semantik.kern_springe),
    (`Gabbro.Core.Ast.Semantik.Befehl.blockEnde, `Gabbro.Core.Ast.Semantik.kern_blockEnde),
    (`Gabbro.Core.Ast.Semantik.Befehl.bindeWert, `Gabbro.Core.Ast.Semantik.kern_bindeWert),
    (`Gabbro.Core.Ast.Semantik.Befehl.definiere, `Gabbro.Core.Ast.Semantik.kern_definiere),
    (`Gabbro.Core.Ast.Semantik.Befehl.rufe, `Gabbro.Core.Ast.Semantik.kern_rufe),
    (`Gabbro.Core.Ast.Semantik.Befehl.rueckVoid, `Gabbro.Core.Ast.Semantik.kern_rueckVoid),
    (`Gabbro.Core.Ast.Semantik.Befehl.pruefeMass, `Gabbro.Core.Ast.Semantik.kern_pruefeMass),
    (`Gabbro.Core.Ast.Semantik.Befehl.setzePasszahl, `Gabbro.Core.Ast.Semantik.kern_setzePasszahl),
    (`Gabbro.Core.Ast.Semantik.Befehl.whileTest, `Gabbro.Core.Ast.Semantik.kern_whileTest),
    (`Gabbro.Core.Ast.Semantik.Befehl.forAnfang, `Gabbro.Core.Ast.Semantik.kern_forAnfang),
    (`Gabbro.Core.Ast.Semantik.Befehl.forTest, `Gabbro.Core.Ast.Semantik.kern_forTest),
    (`Gabbro.Core.Ast.Semantik.Befehl.forNaechster, `Gabbro.Core.Ast.Semantik.kern_forNaechster),
    (`Gabbro.Core.Ast.Semantik.Befehl.zurueckSprung, `Gabbro.Core.Ast.Semantik.kern_zurueckSprung),
    (`Gabbro.Core.Ast.Semantik.Befehl.starte, `Gabbro.Core.Ast.Semantik.kern_starte),
    (`Gabbro.Core.Ast.Semantik.Befehl.ende, `Gabbro.Core.Ast.Semantik.kern_ende),
    (`Gabbro.Core.Ast.Semantik.Befehl.waehleUmgebung, `Gabbro.Core.Ast.Semantik.environmentBefehlEntry) ], #[
    (`Gabbro.Core.Ast.Semantik.Befehl.bindeRegion, `Gabbro.Core.Ast.Semantik.RegionBindUnitAussage) ]⟩]

/-- Change only the proof slot when a scoped form is closed. -/
private meta def scopedEntries : Array RegistryPacket := #[
  ⟨`Gabbro.Core.Ast.Expr.arrayValue, `Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, some `Gabbro.Core.Ast.Semantik.arrayValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.arrayIndex, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, some `Gabbro.Core.Ast.Semantik.arrayIndexEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.tupleValue, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket, some `Gabbro.Core.Ast.Semantik.tupleValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.tupleField, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, some `Gabbro.Core.Ast.Semantik.tupleFieldEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.recordValue, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket, some `Gabbro.Core.Ast.Semantik.recordValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.recordField, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, some `Gabbro.Core.Ast.Semantik.recordFieldEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.variantValue, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket, some `Gabbro.Core.Ast.Semantik.variantValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, some `Gabbro.Core.Ast.Semantik.textLiteralEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket, some `Gabbro.Core.Ast.Semantik.textConcatEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket, some `Gabbro.Core.Ast.Semantik.textIndexEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket, some `Gabbro.Core.Ast.Semantik.textLengthEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket, some `Gabbro.Core.Ast.Semantik.substringEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.optionIsSome, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket, some `Gabbro.Core.Ast.Semantik.optionTestEntry⟩,
  ⟨`Gabbro.Core.Ast.Stmt.tupleBind, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket, some `Gabbro.Core.Ast.Semantik.tupleBindEntry⟩,
  ⟨`Gabbro.Core.Ast.Stmt.assignField, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, some `Gabbro.Core.Ast.Semantik.assignFieldEntry⟩,
  ⟨`Gabbro.Core.Ast.Stmt.letMutableValue, `Gabbro.Core.Ast.Semantik.MutableValueProofPacket, some `Gabbro.Core.Ast.Semantik.mutableValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Stmt.variantMatch, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, some `Gabbro.Core.Ast.Semantik.variantMatchEntry⟩,
  ⟨`Gabbro.Core.Ast.Stmt.letOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, some `Gabbro.Core.Ast.Semantik.letOptionEntry⟩,
  ⟨`Gabbro.Core.Ast.Stmt.retOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, some `Gabbro.Core.Ast.Semantik.retOptionEntry⟩,
  ⟨`Gabbro.Core.Ast.Decl.record, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, some `Gabbro.Core.Ast.Semantik.recordDeclEntry⟩,
  ⟨`Gabbro.Core.Ast.Decl.tagged, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, some `Gabbro.Core.Ast.Semantik.taggedDeclEntry⟩,
  ⟨`Gabbro.Core.Ast.Decl.table, `Gabbro.Core.Ast.Semantik.TableProofPacket, some `Gabbro.Core.Ast.Semantik.tableEntry⟩,
  ⟨`Gabbro.Core.Ast.Decl.effectGroup, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, some `Gabbro.Core.Ast.Semantik.effectGroupEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueArray, `Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, some `Gabbro.Core.Ast.Semantik.buildArrayEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesArray, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, some `Gabbro.Core.Ast.Semantik.liesArrayEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueTupel, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket, some `Gabbro.Core.Ast.Semantik.buildTupleEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesTupelfeld, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, some `Gabbro.Core.Ast.Semantik.liesTupleFieldEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueRecord, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket, some `Gabbro.Core.Ast.Semantik.buildRecordValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesRecordFeld, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, some `Gabbro.Core.Ast.Semantik.buildRecordFieldEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.bindeTupel, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket, some `Gabbro.Core.Ast.Semantik.bindeTupleEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.setzeRecordFeld, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, some `Gabbro.Core.Ast.Semantik.buildAssignFieldEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereRecord, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, some `Gabbro.Core.Ast.Semantik.buildRecordDeclEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueVariante, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket, some `Gabbro.Core.Ast.Semantik.buildVariantEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.waehleVariante, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, some `Gabbro.Core.Ast.Semantik.waehleVariantEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereVariante, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, some `Gabbro.Core.Ast.Semantik.definiereVariantEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, some `Gabbro.Core.Ast.Semantik.textLiteralBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket, some `Gabbro.Core.Ast.Semantik.textConcatBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket, some `Gabbro.Core.Ast.Semantik.textIndexBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket, some `Gabbro.Core.Ast.Semantik.textLengthBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket, some `Gabbro.Core.Ast.Semantik.substringBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereTraeger, `Gabbro.Core.Ast.Semantik.TableProofPacket, some `Gabbro.Core.Ast.Semantik.buildTableEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.optionIstBesetzt, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket, some `Gabbro.Core.Ast.Semantik.optionIstBesetztEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereEffektgruppe, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, some `Gabbro.Core.Ast.Semantik.buildEffectGroupEntry⟩]

private meta def auxiliaryEntries : Array RegistryPacket := #[
  ⟨`Gabbro.Core.Ast.WrittenType.bool, `Gabbro.Core.Ast.Semantik.BoolTypeRegistryAussage, some `Gabbro.Core.Ast.Semantik.boolTypeEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.integer, `Gabbro.Core.Ast.Semantik.IntegerTypeRegistryAussage, some `Gabbro.Core.Ast.Semantik.integerTypeEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.array, `Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, some `Gabbro.Core.Ast.Semantik.arrayTypeEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.tuple, `Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, some `Gabbro.Core.Ast.Semantik.tupleTypeEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.text, `Gabbro.Core.Ast.Semantik.TextTypeProofPacket, some `Gabbro.Core.Ast.Semantik.textTypeEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.index, `Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket, some `Gabbro.Core.Ast.Semantik.carrierIndexEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.indexOption, `Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket, some `Gabbro.Core.Ast.Semantik.carrierIndexOptionEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.ownedRegion, `Gabbro.Core.Ast.Semantik.OwnedRegionTypeRegistryAussage, some `Gabbro.Core.Ast.Semantik.ownedRegionTypeEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.optionMatchForm, `Gabbro.Core.Ast.Semantik.OptionMatchProofPacket, some `Gabbro.Core.Ast.Semantik.optionMatchEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.skalar, `Gabbro.Core.Ast.Semantik.SkalarSimAussage, some `Gabbro.Core.Ast.Semantik.skalarEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.kontrollfluss, `Gabbro.Core.Ast.Semantik.KontrollflussSimAussage, some `Gabbro.Core.Ast.Semantik.kontrollflussEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.aufrufSchleife, `Gabbro.Core.Ast.Semantik.AufrufSchleifeSimAussage, some `Gabbro.Core.Ast.Semantik.aufrufSchleifeEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.aggregat, `Gabbro.Core.Ast.Semantik.AggregatSimAussage, some `Gabbro.Core.Ast.Semantik.aggregatEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.variante, `Gabbro.Core.Ast.Semantik.VarianteSimAussage, some `Gabbro.Core.Ast.Semantik.varianteEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.text, `Gabbro.Core.Ast.Semantik.TextSimAussage, some `Gabbro.Core.Ast.Semantik.textEntry⟩]

private meta def openAuxiliaryEntries : Array (Name × Name) := #[
  (`Gabbro.Core.Ast.WrittenType.address, `Gabbro.Core.Ast.Semantik.AddressTypeUnitAussage),
]

private meta def flowEntries : Array RegistryPacket := #[
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.skalar, `Gabbro.Core.Beobachtung.SkalarNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.kontrollfluss, `Gabbro.Core.Beobachtung.KontrollflussNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.aufrufSchleife, `Gabbro.Core.Beobachtung.AufrufSchleifeNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.aggregat, `Gabbro.Core.Beobachtung.AggregatNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.variante, `Gabbro.Core.Beobachtung.VarianteNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.SimFamilie.text, `Gabbro.Core.Beobachtung.TextNIAussage, none⟩,
  ⟨`Gabbro.Core.Maschine.SchrittWahl.antwort, `Gabbro.Core.Beobachtung.AntwortNIAussage, none⟩,
  ⟨`Gabbro.Core.Maschine.SchrittWahl.interrupt, `Gabbro.Core.Beobachtung.InterruptNIAussage, none⟩,
  ⟨`Gabbro.Core.Maschine.SchrittWahl.absturz, `Gabbro.Core.Beobachtung.AbsturzNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.LowLevel.Instruction, `Gabbro.Core.Beobachtung.RegionNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.LowLevel.MemInstruction, `Gabbro.Core.Beobachtung.SpeicherverwaltungsNIAussage, none⟩,
  ⟨`Gabbro.Core.Ast.LowLevel.Device.Denotation, `Gabbro.Core.Beobachtung.GeraeteNIAussage, none⟩]

private meta def wildcardRoots : Array Name := #[
  `Gabbro.Core.Ast.Semantik.Befehl.ideal, `Gabbro.Core.Ast.Semantik.Befehl.impl,
  `Gabbro.Core.Maschine.I.Schritt, `Gabbro.Core.Maschine.ImplSchritt,
  `Gabbro.Core.Maschine.I.linearisiert_in_I, `Gabbro.Core.Maschine.I.replay_rahmen]
private meta def catalogueKinds : Array ClosedKinds := #[
  ⟨`Gabbro.Core.Maschine.Ergebnis, [`Gabbro.Core.Maschine.Ergebnis.ende, `Gabbro.Core.Maschine.Ergebnis.katalog]⟩,
  ⟨`Gabbro.Core.Katalog.Ereignis, [`Gabbro.Core.Katalog.Ereignis.frage, `Gabbro.Core.Katalog.Ereignis.antwort,
    `Gabbro.Core.Katalog.Ereignis.interrupt, `Gabbro.Core.Katalog.Ereignis.geraet, `Gabbro.Core.Katalog.Ereignis.dma,
    `Gabbro.Core.Katalog.Ereignis.seite, `Gabbro.Core.Katalog.Ereignis.persistenz]⟩]
private meta def closing : Option ClosingSpec := none

private meta def sourceBatches (items : Array Source) : Array (Array Source) := Id.run do
  let batchCount := 12
  let batchSize := max 1 ((items.size + batchCount - 1) / batchCount)
  let mut batches := #[]
  for batch in [:batchCount] do
    let start := batch * batchSize
    if start >= items.size then break
    batches := batches.push (items.extract start (start + batchSize))
  return batches

/-- Audits the source inventory and private compiled declarations at the root, so coverage
    does not depend on each module opting in. -/
elab "#check_core" : command => do
  let started ← IO.monoMsNow
  let root ← IO.FS.realPath (← getFileName)
  let (sources, layoutErrors) ← readCoreSources root
  let imported ← getEnv
  let scans := (sourceBatches sources).map fun batch =>
    Task.spawn fun _ => batch.map fun source => (source, auditSource imported source)
  let (hygiene, reached) := packageErrors sources
  -- An orphan need not have any compiled artifact. Check the reached modules without it.
  let reachableSources := sources.filter (reached.contains ·.moduleName)
  let env ← auditEnvironment imported reachableSources
  let scanned := scans.flatMap (·.get)
  let mut errors := layoutErrors ++ hygiene ++ (scanned.flatMap (·.2.errors))
  let env := withAxiomSummaries (env.setExporting false)
  let elaboratedErrors ← liftTermElabM <| withEnv env do
    let declarationTask ← Meta.MetaM.asTask' (proofErrors (coreDeclarations env))
    let roots := pins.map (·.1) ++ acceptance.acceptance ++ acceptance.ideal ++ safety ++ wildcardRoots
    let closingRoots := closing.toArray.flatMap fun spec => #[spec.shape, spec.frame]
    let index := indexDependencies env roots closingRoots (closing.map (·.trustedRoots) |>.getD {})
    let dependencyErrors := compiledImportErrors env ++ pinErrors env index pins ++ acceptanceErrors env index acceptance
      ++ safetyErrors env index safety
    let pinNames := pins.map (·.1)
    let mut errors ← registryErrors registry scopedEntries pinNames closing.isSome
    let auxiliary := auxiliaryEntries ++ openAuxiliaryEntries.map (fun (form, packet) => ⟨form, packet, none⟩)
    let covered := #[`Gabbro.Core.Ast.Semantik.SimFamilie, `Gabbro.Core.Ast.WrittenType]
    errors := errors ++ (← auxiliaryRegistryErrors auxiliary pinNames closing.isSome covered)
    errors := errors ++ (← auxiliaryRegistryErrors flowEntries pinNames closing.isSome
      #[`Gabbro.Core.Ast.Semantik.SimFamilie])
    errors := errors ++ (← semanticsErrors index wildcardRoots catalogueKinds scanned)
    if let some spec := closing then
      errors := errors ++ (← closingErrors spec pins (imported.setExporting true) index)
    return dependencyErrors ++ (← withoutModifyingState declarationTask.get) ++ errors
  errors := errors ++ elaboratedErrors
  for error in errors do
    logError error
  logInfo m!"Core guards ran in {(← IO.monoMsNow) - started} ms"

end Gabbro.Core.Waechter
