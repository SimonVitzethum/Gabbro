module
public meta import Lean
meta import Lean.Elab.Task
public meta import Core.Waechter.Closing
public meta import Core.Waechter.Decision
public meta import Core.Waechter.Pins
public meta import Core.Waechter.Registry
public meta import Core.Waechter.Safety
public meta import Core.Waechter.Semantics

open Lean Elab Command

namespace Gabbro.Core.Waechter

private meta def pins : Array (Name × UInt64) := #[
  (`Gabbro.Core.Ast.LowLevel.schema, 2832344932234046658),
  (`Gabbro.Core.Ast.LowLevel.AddressTypeAussage, 794241308270216629),
  (`Gabbro.Core.Ast.LowLevel.RegionAddressAussage, 7943639601374982434),
  (`Gabbro.Core.Ast.LowLevel.ViewAussage, 11869545850515923925),
  (`Gabbro.Core.Ast.LowLevel.EnvironmentAussage, 4514224908322717946),
  (`Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage, 15733259603368706660),
  (`Gabbro.Core.Ast.Semantik.AddressTypeUnitAussage, 3525134736315824921),
  (`Gabbro.Core.Ast.Semantik.AddressTypeUnitErfuellbarAussage, 3245356768079883295),
  (`Gabbro.Core.Ast.Semantik.RegionAddressUnitAussage, 10499648118045920537),
  (`Gabbro.Core.Ast.Semantik.ViewUnitAussage, 14449785275102840490),
  (`Gabbro.Core.Ast.Semantik.RegionBindUnitAussage, 5229462174105162127),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterReadAussage, 854024946337055167),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterWriteAussage, 15587504982948919072),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterReadElseAussage, 4151308446977920525),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterTransitionAussage, 15164958506020940950),
  (`Gabbro.Core.Ast.LowLevel.Device.LendAussage, 5411258669457648864),
  (`Gabbro.Core.Ast.LowLevel.Device.TakeBackAussage, 11925056374736953551),
  (`Gabbro.Core.Ast.LowLevel.Device.DmaAussage, 13067714030895001407),
  (`Gabbro.Core.Ast.Ty, 3989644667745438811),
  (`Gabbro.Core.Ast.Local, 18043796543273204751),
  (`Gabbro.Core.Ast.Expr, 9166984138855068896),
  (`Gabbro.Core.Ast.Stmt, 7384092252714694966),
  (`Gabbro.Core.Ast.Block, 7384092252714694966),
  (`Gabbro.Core.Ast.BracedBlock, 7384092252714694966),
  (`Gabbro.Core.Ast.Decl, 7632233716831133940),
  (`Gabbro.Core.Ast.UnitBody, 6300453094967138015),
  (`Gabbro.Core.Ast.Unit, 4139245067018445815),
  (`Gabbro.Core.Ast.Parse, 6940181947863415283),
  (`Gabbro.Core.Ast.Bezeichnet, 12778531047887887708),
  (`Gabbro.Core.Ast.Semantik.Elaboriert, 5804571342824586276),
  (`Gabbro.Core.Ast.Semantik.Bezeichnet, 8237088605646168940),
  (`Gabbro.Core.Ast.Semantik.exprSchema, 292222939901237052),
  (`Gabbro.Core.Ast.Semantik.stmtSchema, 12586283685876718032),
  (`Gabbro.Core.Ast.Semantik.declSchema, 17448314214912247577),
  (`Gabbro.Core.Ast.Semantik.bracedSchema, 17587814424160913414),
  (`Gabbro.Core.Ast.Semantik.befehlSchema, 723543502494294818),
  (`Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, 12758089507299988359),
  (`Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, 16904261679426119406),
  (`Gabbro.Core.Ast.Semantik.TupleValueProofPacket, 2267889959962161004),
  (`Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, 65800977044383837),
  (`Gabbro.Core.Ast.Semantik.RecordValueProofPacket, 4785415688349918824),
  (`Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, 7022563865970492839),
  (`Gabbro.Core.Ast.Semantik.TupleBindProofPacket, 5496515042592610899),
  (`Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, 10469015020683989043),
  (`Gabbro.Core.Ast.Semantik.MutableValueProofPacket, 2344148455517004510),
  (`Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, 14489828437512647395),
  (`Gabbro.Core.Ast.Semantik.VariantValueProofPacket, 15711562313845953845),
  (`Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, 17520025104486017482),
  (`Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, 13727755743503701433),
  (`Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, 15649291053488244958),
  (`Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, 14852161570861370365),
  (`Gabbro.Core.Sicherheit.RegelSicher, 14751731639756142739),
  (`Gabbro.Core.Ziel.Rahmen, 11884202126975013255),
  (`Gabbro.Core.Ziel.NichtLeer, 3734935478639616152),
  (`Gabbro.Core.Ziel.Verfeinert, 6262184474930089844),
  (`Gabbro.Core.Ziel.NI, 7136388435487395955),
  (`Gabbro.Core.Ziel.GabbroZielForm, 10442611768856402706),
  (`Gabbro.Core.Ziel.Sicherheit, 3609222519026224003),
  (`Gabbro.Core.Ziel.SicherheitNichtLeer, 3680087890639914969),
  (`Gabbro.Core.Ziel.GabbroSicherheitForm, 14131772821008578448),
  (`Gabbro.Core.Sicherheit.ToctouFrei, 3928262155281586864),
  (`Gabbro.Core.Sicherheit.Rennfrei, 6004684599932984556),
  (`Gabbro.Core.Sicherheit.InvariantenErhalten, 5797154018978927278),
  (`Gabbro.Core.Sicherheit.Speichersicher, 13444848169355027863),
  (`Gabbro.Core.Katalog.Hardware, 15597978166845504711),
  (`Gabbro.Core.Katalog.FairLaeufe, 8964919104053723618),
  (`Gabbro.Core.Katalog.ZulStart, 4240263083736116198),
  (`Gabbro.Core.Katalog.KatalogWohlgeformt, 1164436312579668639),
  (`Gabbro.Core.Katalog.GeraeteUebergang, 11023072156822412079),
  (`Gabbro.Core.Katalog.atomar, 7794746235685721259),
  (`Gabbro.Core.Katalog.dma, 4560393809987731272),
  (`Gabbro.Core.Katalog.kerneSchreiten, 14534126503517418609),
  (`Gabbro.Core.Katalog.lader, 9915574560480216163),
  (`Gabbro.Core.Katalog.nativeFloat, 1675873447485087518),
  (`Gabbro.Core.Katalog.persistenz, 11266828187864264603),
  (`Gabbro.Core.Katalog.Plattform.firmwareAbi, 6929680125484201438),
  (`Gabbro.Core.Katalog.Plattform.systemAbi, 5876375511519544102),
  (`Gabbro.Core.Katalog.Plattform.uart, 2855728390110218122),
  (`Gabbro.Core.Katalog.Plattform.virtio, 2446173331483218903),
  (`Gabbro.Core.Katalog.Plattform.ziel, 7655265232793873708),
  (`Gabbro.Core.Katalog.regionen, 6935289300322291742),
  (`Gabbro.Core.Katalog.uebersetze, 3754628535707676002),
  (`Gabbro.Core.Katalog.unterbrechungen, 11302222399176252642),
  (`Gabbro.Core.Maschine.Ergebnis, 14979664447435771641),
  (`Gabbro.Core.Maschine.AbsturzSchritt, 13629927236173472726),
  (`Gabbro.Core.Maschine.I.Schritt, 10902251193023140292),
  (`Gabbro.Core.Maschine.ImplSchritt, 2016209155784197599),
  (`Gabbro.Core.Maschine.Laeufe, 10543170110298187230),
  (`Gabbro.Core.Maschine.I.Laeufe, 16702826062692723677),
  (`Gabbro.Core.Maschine.I.AussenBezug, 14545744460845935956),
  (`Gabbro.Core.Maschine.I.Bestimmt, 9030341408699802814),
  (`Gabbro.Core.Maschine.I.Fortschritt, 14331443440873085814),
  (`Gabbro.Core.Maschine.I.Sim, 2462139631059147866),
  (`Gabbro.Core.Maschine.I.Haengt, 11530574022863258723),
  (`Gabbro.Core.Maschine.I.RegelKomponierbar, 2131622631997208645),
  (`Gabbro.Core.Annahme.Akzeptiert, 2964006569689969159),
  (`Gabbro.Core.Annahme.Lokal, 3673240487411088430),
  (`Gabbro.Core.Annahme.AussenLokal, 4337584449661950587),
  (`Gabbro.Core.Annahme.KlauselnWahr, 8147739929617763377),
  (`Gabbro.Core.Annahme.WaechterHalten, 15584117099234001852),
  (`Gabbro.Core.Annahme.GeschlossenWartend, 7169846444890678982),
  (`Gabbro.Core.Maschine.PartielleOperation, 3187517857228953299),
  (`Gabbro.Core.Annahme.waechterBedarf, 9657614452858633655)]

private meta def safety : Array Name := #[
  `Gabbro.Core.Sicherheit.RegelSicher,
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
  ⟨`Gabbro.Core.Ast.LowLevel.Tree, `Gabbro.Core.Ast.LowLevel.schema, #[], #[
    (`Gabbro.Core.Ast.LowLevel.Tree.addressType, `Gabbro.Core.Ast.LowLevel.AddressTypeAussage),
    (`Gabbro.Core.Ast.LowLevel.Tree.regionAddress, `Gabbro.Core.Ast.LowLevel.RegionAddressAussage),
    (`Gabbro.Core.Ast.LowLevel.Tree.view, `Gabbro.Core.Ast.LowLevel.ViewAussage),
    (`Gabbro.Core.Ast.LowLevel.Tree.environment, `Gabbro.Core.Ast.LowLevel.EnvironmentAussage)]⟩,
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
    (`Gabbro.Core.Ast.Expr.logic, `Gabbro.Core.Ast.Semantik.logicEntry) ], #[
    (`Gabbro.Core.Ast.Expr.arrayValue, `Gabbro.Core.Ast.Semantik.ArrayValueProofPacket),
    (`Gabbro.Core.Ast.Expr.arrayIndex, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket),
    (`Gabbro.Core.Ast.Expr.tupleValue, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket),
    (`Gabbro.Core.Ast.Expr.tupleField, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket),
    (`Gabbro.Core.Ast.Expr.recordValue, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket),
    (`Gabbro.Core.Ast.Expr.recordField, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket),
    (`Gabbro.Core.Ast.Expr.variantValue, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket) ]⟩,
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
    (`Gabbro.Core.Ast.Stmt.tupleBind, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket),
    (`Gabbro.Core.Ast.Stmt.assignField, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket),
    (`Gabbro.Core.Ast.Stmt.letMutableValue, `Gabbro.Core.Ast.Semantik.MutableValueProofPacket),
    (`Gabbro.Core.Ast.Stmt.variantMatch, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket),
    (`Gabbro.Core.Ast.Stmt.letRegion, `Gabbro.Core.Ast.Semantik.RegionBindUnitAussage) ]⟩,
  ⟨`Gabbro.Core.Ast.Decl, `Gabbro.Core.Ast.Semantik.declSchema, #[
    (`Gabbro.Core.Ast.Decl.constant, `Gabbro.Core.Ast.Semantik.constantEntry),
    (`Gabbro.Core.Ast.Decl.function, `Gabbro.Core.Ast.Semantik.functionEntry) ], #[
    (`Gabbro.Core.Ast.Decl.record, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket),
    (`Gabbro.Core.Ast.Decl.tagged, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket),
    (`Gabbro.Core.Ast.Decl.environment, `Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage) ]⟩,
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
    (`Gabbro.Core.Ast.Semantik.Befehl.ende, `Gabbro.Core.Ast.Semantik.kern_ende) ], #[
    (`Gabbro.Core.Ast.Semantik.Befehl.baueArray, `Gabbro.Core.Ast.Semantik.ArrayValueProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.liesArray, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.baueTupel, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.liesTupelfeld, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.baueRecord, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.liesRecordFeld, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.bindeTupel, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.setzeRecordFeld, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.definiereRecord, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.baueVariante, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.waehleVariante, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.definiereVariante, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.waehleUmgebung, `Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage),
    (`Gabbro.Core.Ast.Semantik.Befehl.bindeRegion, `Gabbro.Core.Ast.Semantik.RegionBindUnitAussage) ]⟩]

private meta def openTypeEntries : Array (Name × Name) := #[
  (`Gabbro.Core.Ast.WrittenType.array, `Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.tuple, `Gabbro.Core.Ast.Semantik.TupleTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.address, `Gabbro.Core.Ast.Semantik.AddressTypeUnitAussage)]

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
    let mut errors ← registryErrors registry pinNames closing.isSome
    errors := errors ++ (← openRegistryErrors openTypeEntries pinNames closing.isSome)
    errors := errors ++ (← semanticsErrors index wildcardRoots catalogueKinds scanned)
    if let some spec := closing then
      errors := errors ++ (← closingErrors spec pins (imported.setExporting true) index)
    return dependencyErrors ++ (← withoutModifyingState declarationTask.get) ++ errors
  errors := errors ++ elaboratedErrors
  for error in errors do
    logError error
  logInfo m!"Core guards ran in {(← IO.monoMsNow) - started} ms"

end Gabbro.Core.Waechter
