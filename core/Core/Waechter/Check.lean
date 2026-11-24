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
  (`Gabbro.Core.Beobachtung.NiedrigeBeob, 8380224728954698503),
  (`Gabbro.Core.Beobachtung.NiedrigAequiv, 5325936300272809159),
  (`Gabbro.Core.Katalog.Plattform.spekulationshuelle, 9646114676836847360),
  (`Gabbro.Core.Beobachtung.NiedrigGleich, 1113978584766348090),
  (`Gabbro.Core.Beobachtung.GleicheNiedrigeUmgebung, 11405736449449224126),
  (`Gabbro.Core.Beobachtung.GleichePolitik, 7611314121134932511),
  (`Gabbro.Core.Beobachtung.ImSchranken, 7026144039880470692),
  (`Gabbro.Core.Beobachtung.B8Pflichten, 0),
  (`Gabbro.Core.Beobachtung.B8Abschluss, 0),
  (`Gabbro.Core.Beobachtung.kostenNullAussage, 0),
  (`Gabbro.Core.Beobachtung.kostenSchrittAussage, 0),
  (`Gabbro.Core.Beobachtung.kostenTeilungAussage, 0),
  (`Gabbro.Core.Beobachtung.kostenMonotonAussage, 0),
  (`Gabbro.Core.Beobachtung.kostenAnfangAussage, 0),
  (`Gabbro.Core.Beobachtung.halteAnfangAussage, 0),
  (`Gabbro.Core.Beobachtung.halteFremdAussage, 0),
  (`Gabbro.Core.Beobachtung.zeitRumpfNeuAussage, 0),
  (`Gabbro.Core.Beobachtung.zeitRechtzeitigErweiternAussage, 0),
  (`Gabbro.Core.Beobachtung.zeitSpaetErweiternAussage, 0),
  (`Gabbro.Core.Beobachtung.b8LeerlaufAussage, 0),
  (`Gabbro.Core.Katalog.Katalog.dauerMaximum, 16990558230020595847),
  (`Gabbro.Core.Ast.Ty, 4264492780836872700),
  (`Gabbro.Core.Ast.Local, 6370605275454439302),
  (`Gabbro.Core.Ast.Expr, 13817919532148845917),
  (`Gabbro.Core.Ast.Stmt, 13187945759778334996),
  (`Gabbro.Core.Ast.Block, 13187945759778334996),
  (`Gabbro.Core.Ast.BracedBlock, 13187945759778334996),
  (`Gabbro.Core.Ast.Decl, 10239274893468156882),
  (`Gabbro.Core.Ast.UnitBody, 18284720303362696585),
  (`Gabbro.Core.Ast.Unit, 5385091271834252949),
  (`Gabbro.Core.Ast.Parse, 11097918721276606861),
  (`Gabbro.Core.Ast.Bezeichnet, 10652016832381994034),
  (`Gabbro.Core.Ast.Semantik.Elaboriert, 15176833045776773700),
  (`Gabbro.Core.Ast.Semantik.Bezeichnet, 15344327058250995692),
  (`Gabbro.Core.Ast.Semantik.exprSchema, 10702462836798294392),
  (`Gabbro.Core.Ast.Semantik.stmtSchema, 3985011902968498453),
  (`Gabbro.Core.Ast.Semantik.declSchema, 4735356093979686128),
  (`Gabbro.Core.Ast.Semantik.bracedSchema, 1645842236986079183),
  (`Gabbro.Core.Ast.Semantik.befehlSchema, 10401760838417222209),
  (`Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, 4356096181917287825),
  (`Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, 14187053105571374855),
  (`Gabbro.Core.Ast.Semantik.TupleValueProofPacket, 5339112539778417106),
  (`Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, 6381663503469321146),
  (`Gabbro.Core.Ast.Semantik.RecordValueProofPacket, 8480960442906524113),
  (`Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, 8302142640327553637),
  (`Gabbro.Core.Ast.Semantik.TupleBindProofPacket, 16025135253152340522),
  (`Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, 1375085071947039428),
  (`Gabbro.Core.Ast.Semantik.MutableValueProofPacket, 16641739898452917129),
  (`Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, 13059238527020898607),
  (`Gabbro.Core.Ast.Semantik.VariantValueProofPacket, 4087307226960479928),
  (`Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, 12592303134885691167),
  (`Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, 13140374360321434000),
  (`Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, 6359630823379473114),
  (`Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, 12696547901250916589),
  (`Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, 10727222537436399389),
  (`Gabbro.Core.Ast.Semantik.TextLengthProofPacket, 4620856767111490159),
  (`Gabbro.Core.Ast.Semantik.TextConcatProofPacket, 1921483864487877331),
  (`Gabbro.Core.Ast.Semantik.TextIndexProofPacket, 5260606407625125546),
  (`Gabbro.Core.Ast.Semantik.SubstringProofPacket, 10554571864009294559),
  (`Gabbro.Core.Ast.Semantik.TextTypeProofPacket, 14116952845329082571),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket, 14464783928850510168),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket, 15764583623170259851),
  (`Gabbro.Core.Ast.Semantik.TableProofPacket, 1493069139387848348),
  (`Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, 15805049637121809678),
  (`Gabbro.Core.Ast.Semantik.OptionTestProofPacket, 17868237307026143414),
  (`Gabbro.Core.Ast.Semantik.OptionMatchProofPacket, 1141082247032219188),
  (`Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, 7324591963556156296),
  (`Gabbro.Core.Sicherheit.RegelSicher, 16067809292282756032),
  (`Gabbro.Core.Ziel.Rahmen, 11884202126975013255),
  (`Gabbro.Core.Ziel.NichtLeer, 3734935478639616152),
  (`Gabbro.Core.Ziel.Verfeinert, 6262184474930089844),
  (`Gabbro.Core.Ziel.NI, 7136388435487395955),
  (`Gabbro.Core.Ziel.GabbroZielForm, 10442611768856402706),
  (`Gabbro.Core.Ziel.Sicherheit, 3609222519026224003),
  (`Gabbro.Core.Ziel.SicherheitNichtLeer, 3680087890639914969),
  (`Gabbro.Core.Ziel.GabbroSicherheitForm, 14131772821008578448),
  (`Gabbro.Core.Sicherheit.ToctouFrei, 243092626053257803),
  (`Gabbro.Core.Sicherheit.Rennfrei, 15438729780195728957),
  (`Gabbro.Core.Sicherheit.InvariantenErhalten, 1684443241857757243),
  (`Gabbro.Core.Sicherheit.Speichersicher, 1654585950317661274),
  (`Gabbro.Core.Katalog.Hardware, 3517031233163520317),
  (`Gabbro.Core.Katalog.FairLaeufe, 12824706767208441764),
  (`Gabbro.Core.Katalog.ZulStart, 8513960854720171139),
  (`Gabbro.Core.Katalog.KatalogWohlgeformt, 17814518153659352653),
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
  (`Gabbro.Core.Maschine.AbsturzSchritt, 2722360304480008598),
  (`Gabbro.Core.Maschine.I.Schritt, 15346941996730804332),
  (`Gabbro.Core.Maschine.ImplSchritt, 7175608013554397151),
  (`Gabbro.Core.Maschine.Laeufe, 13030399617526740489),
  (`Gabbro.Core.Maschine.I.Laeufe, 9234808820425370046),
  (`Gabbro.Core.Maschine.I.AussenBezug, 14545744460845935956),
  (`Gabbro.Core.Maschine.I.Bestimmt, 7049320253757918330),
  (`Gabbro.Core.Maschine.I.Fortschritt, 7327703375541758626),
  (`Gabbro.Core.Maschine.I.Sim, 953337358041712979),
  (`Gabbro.Core.Maschine.I.Haengt, 6894787070203168920),
  (`Gabbro.Core.Maschine.I.RegelKomponierbar, 2131622631997208645),
  (`Gabbro.Core.Annahme.Akzeptiert, 3154968092365899865),
  (`Gabbro.Core.Annahme.Lokal, 12068175343176633389),
  (`Gabbro.Core.Annahme.AussenLokal, 12062990052172449400),
  (`Gabbro.Core.Annahme.KlauselnWahr, 14761967842491337222),
  (`Gabbro.Core.Annahme.WaechterHalten, 16860721752260323354),
  (`Gabbro.Core.Annahme.GeschlossenWartend, 6249161161004728275),
  (`Gabbro.Core.Maschine.PartielleOperation, 17845138986886266319),
  (`Gabbro.Core.Annahme.waechterBedarf, 2466293456166709549)]

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
    (`Gabbro.Core.Ast.Expr.variantValue, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket),
    (`Gabbro.Core.Ast.Expr.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket),
    (`Gabbro.Core.Ast.Expr.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket),
    (`Gabbro.Core.Ast.Expr.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket),
    (`Gabbro.Core.Ast.Expr.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket),
    (`Gabbro.Core.Ast.Expr.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket),
    (`Gabbro.Core.Ast.Expr.optionIsSome, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket) ]⟩,
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
    (`Gabbro.Core.Ast.Stmt.letOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket),
    (`Gabbro.Core.Ast.Stmt.retOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket) ]⟩,
  ⟨`Gabbro.Core.Ast.Decl, `Gabbro.Core.Ast.Semantik.declSchema, #[
    (`Gabbro.Core.Ast.Decl.constant, `Gabbro.Core.Ast.Semantik.constantEntry),
    (`Gabbro.Core.Ast.Decl.function, `Gabbro.Core.Ast.Semantik.functionEntry) ], #[
    (`Gabbro.Core.Ast.Decl.record, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket),
    (`Gabbro.Core.Ast.Decl.tagged, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket),
    (`Gabbro.Core.Ast.Decl.table, `Gabbro.Core.Ast.Semantik.TableProofPacket),
    (`Gabbro.Core.Ast.Decl.effectGroup, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket) ]⟩,
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
    (`Gabbro.Core.Ast.Semantik.Befehl.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.definiereTraeger, `Gabbro.Core.Ast.Semantik.TableProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.optionIstBesetzt, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.definiereEffektgruppe, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket) ]⟩]

private meta def openAuxiliaryEntries : Array (Name × Name) := #[
  (`Gabbro.Core.Ast.WrittenType.array, `Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.tuple, `Gabbro.Core.Ast.Semantik.TupleTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.text, `Gabbro.Core.Ast.Semantik.TextTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.index, `Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket),
  (`Gabbro.Core.Ast.WrittenType.indexOption, `Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket),
  (`Gabbro.Core.Ast.Semantik.optionMatchForm, `Gabbro.Core.Ast.Semantik.OptionMatchProofPacket)]

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
    errors := errors ++ (← openRegistryErrors openAuxiliaryEntries pinNames closing.isSome)
    errors := errors ++ (← semanticsErrors index wildcardRoots catalogueKinds scanned)
    if let some spec := closing then
      errors := errors ++ (← closingErrors spec pins (imported.setExporting true) index)
    return dependencyErrors ++ (← withoutModifyingState declarationTask.get) ++ errors
  errors := errors ++ elaboratedErrors
  for error in errors do
    logError error
  logInfo m!"Core guards ran in {(← IO.monoMsNow) - started} ms"

end Gabbro.Core.Waechter
