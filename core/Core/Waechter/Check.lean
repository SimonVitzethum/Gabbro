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
  (`Gabbro.Core.Ast.LowLevel.schemaMem, 0),
  (`Gabbro.Core.Ast.LowLevel.SplitAtAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.SplitPagesAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.MergeAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.NewSpaceAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.MapAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.ProtectAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.UnmapAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.FlushAussage, 0),
  (`Gabbro.Core.Ast.LowLevel.ActivateAussage, 0),
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
  (`Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage, 7319798228071612859),
  (`Gabbro.Core.Ast.LowLevel.schema, 17609198345977790499),
  (`Gabbro.Core.Ast.LowLevel.AddressTypeAussage, 11009489123797045368),
  (`Gabbro.Core.Ast.LowLevel.RegionAddressAussage, 16229512138000935843),
  (`Gabbro.Core.Ast.LowLevel.ViewAussage, 6907148149172672224),
  (`Gabbro.Core.Ast.LowLevel.EnvironmentAussage, 3027431613941020891),
  (`Gabbro.Core.Beobachtung.NiedrigeBeob, 8380224728954698503),
  (`Gabbro.Core.Beobachtung.NiedrigAequiv, 5325936300272809159),
  (`Gabbro.Core.Katalog.Plattform.spekulationshuelle, 9646114676836847360),
  (`Gabbro.Core.Beobachtung.NiedrigGleich, 1113978584766348090),
  (`Gabbro.Core.Beobachtung.GleicheNiedrigeUmgebung, 11405736449449224126),
  (`Gabbro.Core.Beobachtung.GleichePolitik, 7611314121134932511),
  (`Gabbro.Core.Beobachtung.ImSchranken, 7026144039880470692),
  (`Gabbro.Core.Katalog.Katalog.dauerMaximum, 16990558230020595847),
  (`Gabbro.Core.Ast.Ty, 4264492780836872700),
  (`Gabbro.Core.Ast.Local, 6370605275454439302),
  (`Gabbro.Core.Ast.Expr, 13817919532148845917),
  (`Gabbro.Core.Ast.Stmt, 13187945759778334996),
  (`Gabbro.Core.Ast.Block, 13187945759778334996),
  (`Gabbro.Core.Ast.BracedBlock, 13187945759778334996),
  (`Gabbro.Core.Ast.Decl, 15218842397360160303),
  (`Gabbro.Core.Ast.UnitBody, 1819261089491017240),
  (`Gabbro.Core.Ast.Unit, 13944332436161408052),
  (`Gabbro.Core.Ast.Parse, 17914961565165142882),
  (`Gabbro.Core.Ast.Bezeichnet, 6059719947286295809),
  (`Gabbro.Core.Ast.Semantik.Elaboriert, 9710803329185032068),
  (`Gabbro.Core.Ast.Semantik.Bezeichnet, 8532326390698839564),
  (`Gabbro.Core.Ast.Semantik.exprSchema, 6442672813675497348),
  (`Gabbro.Core.Ast.Semantik.stmtSchema, 6961161701128197681),
  (`Gabbro.Core.Ast.Semantik.declSchema, 2056915661562883868),
  (`Gabbro.Core.Ast.Semantik.bracedSchema, 4740985723117945875),
  (`Gabbro.Core.Ast.Semantik.befehlSchema, 7940832519129698902),
  (`Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, 11533077599505760310),
  (`Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, 16455932954744241228),
  (`Gabbro.Core.Ast.Semantik.TupleValueProofPacket, 15101000052640690173),
  (`Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, 13121180496961167065),
  (`Gabbro.Core.Ast.Semantik.RecordValueProofPacket, 6489591369870456592),
  (`Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, 15865258454437343718),
  (`Gabbro.Core.Ast.Semantik.TupleBindProofPacket, 11772581730800011777),
  (`Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, 11369434078727098089),
  (`Gabbro.Core.Ast.Semantik.MutableValueProofPacket, 11567391431170722066),
  (`Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, 16802691678563827732),
  (`Gabbro.Core.Ast.Semantik.VariantValueProofPacket, 3789508832770414137),
  (`Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, 2259397856607130085),
  (`Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, 3346063617309928607),
  (`Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, 2902909754508048838),
  (`Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, 7958056095272745373),
  (`Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, 12605080358721170354),
  (`Gabbro.Core.Ast.Semantik.TextLengthProofPacket, 1212043607800529408),
  (`Gabbro.Core.Ast.Semantik.TextConcatProofPacket, 13195337694978400260),
  (`Gabbro.Core.Ast.Semantik.TextIndexProofPacket, 17040943799930683305),
  (`Gabbro.Core.Ast.Semantik.SubstringProofPacket, 13364006108391320196),
  (`Gabbro.Core.Ast.Semantik.TextTypeProofPacket, 9162977309127032031),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket, 16760253489035962268),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket, 5711406624077995483),
  (`Gabbro.Core.Ast.Semantik.TableProofPacket, 4185018734779268847),
  (`Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, 3881988445716297561),
  (`Gabbro.Core.Ast.Semantik.OptionTestProofPacket, 11980065538316879925),
  (`Gabbro.Core.Ast.Semantik.OptionMatchProofPacket, 14640176804452854627),
  (`Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, 9873437927112651),
  (`Gabbro.Core.Sicherheit.RegelSicher, 14059395004744157412),
  (`Gabbro.Core.Ziel.Rahmen, 11884202126975013255),
  (`Gabbro.Core.Ziel.NichtLeer, 3734935478639616152),
  (`Gabbro.Core.Ziel.Verfeinert, 6262184474930089844),
  (`Gabbro.Core.Ziel.NI, 7136388435487395955),
  (`Gabbro.Core.Ziel.GabbroZielForm, 10442611768856402706),
  (`Gabbro.Core.Ziel.Sicherheit, 3609222519026224003),
  (`Gabbro.Core.Ziel.SicherheitNichtLeer, 3680087890639914969),
  (`Gabbro.Core.Ziel.GabbroSicherheitForm, 14131772821008578448),
  (`Gabbro.Core.Sicherheit.ToctouFrei, 5325567703471775071),
  (`Gabbro.Core.Sicherheit.Rennfrei, 15438729780195728957),
  (`Gabbro.Core.Sicherheit.InvariantenErhalten, 1684443241857757243),
  (`Gabbro.Core.Sicherheit.Speichersicher, 1654585950317661274),
  (`Gabbro.Core.Katalog.Hardware, 3517031233163520317),
  (`Gabbro.Core.Katalog.FairLaeufe, 12824706767208441764),
  (`Gabbro.Core.Katalog.ZulStart, 339235726871917878),
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
  (`Gabbro.Core.Maschine.Laeufe, 8607980195564532221),
  (`Gabbro.Core.Maschine.I.Laeufe, 2254669744208532722),
  (`Gabbro.Core.Maschine.I.AussenBezug, 14545744460845935956),
  (`Gabbro.Core.Maschine.I.Bestimmt, 7049320253757918330),
  (`Gabbro.Core.Maschine.I.Fortschritt, 7327703375541758626),
  (`Gabbro.Core.Maschine.I.Sim, 953337358041712979),
  (`Gabbro.Core.Maschine.I.Haengt, 6894787070203168920),
  (`Gabbro.Core.Maschine.I.RegelKomponierbar, 2131622631997208645),
  (`Gabbro.Core.Annahme.Akzeptiert, 14785600931209126213),
  (`Gabbro.Core.Annahme.Lokal, 8537419093173066105),
  (`Gabbro.Core.Annahme.AussenLokal, 2850687780170911524),
  (`Gabbro.Core.Annahme.KlauselnWahr, 8082805075160504394),
  (`Gabbro.Core.Annahme.WaechterHalten, 1202060150610760878),
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
  ⟨`Gabbro.Core.Ast.LowLevel.MemTree, `Gabbro.Core.Ast.LowLevel.schemaMem, #[], #[
    (`Gabbro.Core.Ast.LowLevel.MemTree.splitAt, `Gabbro.Core.Ast.LowLevel.SplitAtAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.splitPages, `Gabbro.Core.Ast.LowLevel.SplitPagesAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.merge, `Gabbro.Core.Ast.LowLevel.MergeAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.newSpace, `Gabbro.Core.Ast.LowLevel.NewSpaceAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.mapSpace, `Gabbro.Core.Ast.LowLevel.MapAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.protectSpace, `Gabbro.Core.Ast.LowLevel.ProtectAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.unmapSpace, `Gabbro.Core.Ast.LowLevel.UnmapAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.flushSpace, `Gabbro.Core.Ast.LowLevel.FlushAussage),
    (`Gabbro.Core.Ast.LowLevel.MemTree.activateSpace, `Gabbro.Core.Ast.LowLevel.ActivateAussage)]⟩,
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
    (`Gabbro.Core.Ast.Stmt.retOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket),
    (`Gabbro.Core.Ast.Stmt.letRegion, `Gabbro.Core.Ast.Semantik.RegionBindUnitAussage) ]⟩,
  ⟨`Gabbro.Core.Ast.Decl, `Gabbro.Core.Ast.Semantik.declSchema, #[
    (`Gabbro.Core.Ast.Decl.constant, `Gabbro.Core.Ast.Semantik.constantEntry),
    (`Gabbro.Core.Ast.Decl.function, `Gabbro.Core.Ast.Semantik.functionEntry) ], #[
    (`Gabbro.Core.Ast.Decl.record, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket),
    (`Gabbro.Core.Ast.Decl.tagged, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket),
    (`Gabbro.Core.Ast.Decl.table, `Gabbro.Core.Ast.Semantik.TableProofPacket),
    (`Gabbro.Core.Ast.Decl.effectGroup, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket),
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
    (`Gabbro.Core.Ast.Semantik.Befehl.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.definiereTraeger, `Gabbro.Core.Ast.Semantik.TableProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.optionIstBesetzt, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.definiereEffektgruppe, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket),
    (`Gabbro.Core.Ast.Semantik.Befehl.waehleUmgebung, `Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage),
    (`Gabbro.Core.Ast.Semantik.Befehl.bindeRegion, `Gabbro.Core.Ast.Semantik.RegionBindUnitAussage) ]⟩]

private meta def openAuxiliaryEntries : Array (Name × Name) := #[
  (`Gabbro.Core.Ast.WrittenType.array, `Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.tuple, `Gabbro.Core.Ast.Semantik.TupleTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.text, `Gabbro.Core.Ast.Semantik.TextTypeProofPacket),
  (`Gabbro.Core.Ast.WrittenType.index, `Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket),
  (`Gabbro.Core.Ast.WrittenType.indexOption, `Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket),
  (`Gabbro.Core.Ast.Semantik.optionMatchForm, `Gabbro.Core.Ast.Semantik.OptionMatchProofPacket),
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
