module
public meta import Lean
meta import Lean.Elab.Task
meta import Core.Ast.Inventory.Entries.ArrayIndex
meta import Core.Ast.Inventory.Entries.Arrays
meta import Core.Ast.Inventory.Entries.CarriersAndEffects
meta import Core.Ast.Inventory.Entries.Option
meta import Core.Ast.Inventory.Entries.OwnedRegionType
meta import Core.Ast.Inventory.Entries.Variants
meta import Core.Ast.Inventory.Entries.WrittenTypeStatements
meta import Core.Ast.Inventory.Entries.Text
meta import Core.Verfeinerung.Formen.Registry
public meta import Core.Waechter.Closing
public meta import Core.Waechter.Decision
public meta import Core.Waechter.Pins
public meta import Core.Waechter.Registry
public meta import Core.Waechter.Safety
public meta import Core.Waechter.Semantics

open Lean Elab Command

namespace Gabbro.Core.Waechter

private meta def pins : Array (Name × UInt64) := #[
  (`Gabbro.Core.Ast.Semantik.BoolTypeRegistryAussage, 17675852018870980887),
  (`Gabbro.Core.Ast.Semantik.IntegerTypeRegistryAussage, 10048472741723074573),
  (`Gabbro.Core.Ast.Semantik.OwnedRegionTypeRegistryAussage, 14002860827496155215),
  (`Gabbro.Core.Ast.LowLevel.schemaMem, 15056380717633799532),
  (`Gabbro.Core.Ast.LowLevel.MemRegelAntwortSicherAussage, 14145296679685159933),
  (`Gabbro.Core.Ast.LowLevel.SplitAtAussage, 13745092202238210397),
  (`Gabbro.Core.Ast.LowLevel.SplitPagesAussage, 5201603974483779385),
  (`Gabbro.Core.Ast.LowLevel.MergeAussage, 7558944386447482581),
  (`Gabbro.Core.Ast.LowLevel.NewSpaceAussage, 15795743523239827988),
  (`Gabbro.Core.Ast.LowLevel.MapAussage, 7556898621161746453),
  (`Gabbro.Core.Ast.LowLevel.ProtectAussage, 4346427744430274253),
  (`Gabbro.Core.Ast.LowLevel.UnmapAussage, 12540610934590975095),
  (`Gabbro.Core.Ast.LowLevel.FlushAussage, 331680468419105402),
  (`Gabbro.Core.Ast.LowLevel.ActivateAussage, 17379982144279967706),
  (`Gabbro.Core.Ast.Semantik.AddressTypeUnitAussage, 8659488053402451011),
  (`Gabbro.Core.Ast.Semantik.AddressTypeUnitErfuellbarAussage, 11055738908308874434),
  (`Gabbro.Core.Ast.Semantik.RegionAddressUnitAussage, 10487757405389955670),
  (`Gabbro.Core.Ast.Semantik.ViewUnitAussage, 5333044864028827048),
  (`Gabbro.Core.Ast.Semantik.RegionBindUnitAussage, 2727360655240965219),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterReadAussage, 15696690675639403088),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterWriteAussage, 4759926371167336105),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterReadElseAussage, 5784323693599135584),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterRegelAntwortSicherAussage, 14024839646617587863),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterTransitionAussage, 12549731911685393145),
  (`Gabbro.Core.Ast.LowLevel.Device.LendAussage, 2549621462376397167),
  (`Gabbro.Core.Ast.LowLevel.Device.TakeBackAussage, 7678404762004743412),
  (`Gabbro.Core.Ast.LowLevel.Device.DmaAussage, 6660087069398687915),
  (`Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage, 7666688847673653021),
  (`Gabbro.Core.Ast.LowLevel.schema, 12912960704360944047),
  (`Gabbro.Core.Ast.LowLevel.RegelAntwortSicherAussage, 12283068607266011639),
  (`Gabbro.Core.Ast.LowLevel.AddressTypeAussage, 3793195783415088848),
  (`Gabbro.Core.Ast.LowLevel.RegionAddressAussage, 7975225910067950159),
  (`Gabbro.Core.Ast.LowLevel.ViewAussage, 16435414610047952856),
  (`Gabbro.Core.Ast.LowLevel.EnvironmentAussage, 4039913668056321855),
  (`Gabbro.Core.Beobachtung.NiedrigeBeob, 8380224728954698503),
  (`Gabbro.Core.Beobachtung.NiedrigAequiv, 5325936300272809159),
  (`Gabbro.Core.Katalog.Plattform.spekulationshuelle, 9646114676836847360),
  (`Gabbro.Core.Beobachtung.NiedrigGleich, 1113978584766348090),
  (`Gabbro.Core.Beobachtung.GleicheNiedrigeUmgebung, 11405736449449224126),
  (`Gabbro.Core.Beobachtung.GleichePolitik, 7611314121134932511),
  (`Gabbro.Core.Beobachtung.ImSchranken, 7026144039880470692),
  (`Gabbro.Core.Beobachtung.B8Pflichten, 0),
  (`Gabbro.Core.Beobachtung.KHPflichten, 0),
  (`Gabbro.Core.Beobachtung.ZeitPflichten, 0),
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
  (`Gabbro.Core.Beobachtung.khLeerlaufAussage, 0),
  (`Gabbro.Core.Katalog.Katalog.dauerMaximum, 16990558230020595847),
  (`Gabbro.Core.Ast.Ty, 11778562012426237599),
  (`Gabbro.Core.Ast.Local, 12494921867450307309),
  (`Gabbro.Core.Ast.Expr, 17304713255317030706),
  (`Gabbro.Core.Ast.Stmt, 9650784173528834358),
  (`Gabbro.Core.Ast.Block, 9650784173528834358),
  (`Gabbro.Core.Ast.BracedBlock, 9650784173528834358),
  (`Gabbro.Core.Ast.Decl, 11708785102856312389),
  (`Gabbro.Core.Ast.UnitBody, 1343785407712970514),
  (`Gabbro.Core.Ast.Unit, 16312122039110487282),
  (`Gabbro.Core.Ast.Parse, 16023375331748819233),
  (`Gabbro.Core.Ast.Bezeichnet, 1860912224805596650),
  (`Gabbro.Core.Ast.Semantik.Elaboriert, 3699703491707153934),
  (`Gabbro.Core.Ast.Semantik.Bezeichnet, 7835108179057266678),
  (`Gabbro.Core.Ast.Semantik.exprSchema, 3793760292311380295),
  (`Gabbro.Core.Ast.Semantik.stmtSchema, 6338272148804659328),
  (`Gabbro.Core.Ast.Semantik.declSchema, 12858483236668466797),
  (`Gabbro.Core.Ast.Semantik.bracedSchema, 17706227794227783311),
  (`Gabbro.Core.Ast.Semantik.befehlSchema, 4775196620813107231),
  (`Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, 7926474596940619221),
  (`Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, 11120146123179291461),
  (`Gabbro.Core.Ast.Semantik.TupleValueProofPacket, 7922898914715859862),
  (`Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, 5912469974389678278),
  (`Gabbro.Core.Ast.Semantik.RecordValueProofPacket, 13064596160981381400),
  (`Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, 15137450909954166232),
  (`Gabbro.Core.Ast.Semantik.TupleBindProofPacket, 12891951079156127031),
  (`Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, 16434984990583657851),
  (`Gabbro.Core.Ast.Semantik.MutableValueProofPacket, 13388051373240539481),
  (`Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, 6912851339351744465),
  (`Gabbro.Core.Ast.Semantik.VariantValueProofPacket, 6625080835049673488),
  (`Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, 18406119125432532629),
  (`Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, 6195178118832550475),
  (`Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, 15314624442894419398),
  (`Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, 16652718143797575071),
  (`Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, 8568616864809147542),
  (`Gabbro.Core.Ast.Semantik.TextLengthProofPacket, 3986837654503811979),
  (`Gabbro.Core.Ast.Semantik.TextConcatProofPacket, 4859768527246415910),
  (`Gabbro.Core.Ast.Semantik.TextIndexProofPacket, 11125213193085216613),
  (`Gabbro.Core.Ast.Semantik.SubstringProofPacket, 14857857599555189845),
  (`Gabbro.Core.Ast.Semantik.TextTypeProofPacket, 11040493085125990506),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket, 10723151518297374230),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket, 104246028322088572),
  (`Gabbro.Core.Ast.Semantik.TableProofPacket, 6215922813864168169),
  (`Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, 15089735107991481441),
  (`Gabbro.Core.Ast.Semantik.OptionTestProofPacket, 17304996935289938096),
  (`Gabbro.Core.Ast.Semantik.OptionMatchProofPacket, 6789647291622164254),
  (`Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, 4858702150073341057),
  (`Gabbro.Core.Sicherheit.RegelSicher, 14059395004744157412),
  (`Gabbro.Core.Sicherheit.RegelAntwortSicher, 17409749439812809323),
  (`Gabbro.Core.Sicherheit.RegelPflichten, 2369209967678043503),
  (`Gabbro.Core.Ast.Semantik.Quellform.SicherheitsAussage, 15766680830768517854),
  (`Gabbro.Core.Ast.Semantik.ProgramKernSicherheitsAussage, 1479461249594615259),
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
  (`Gabbro.Core.Ast.Semantik.SkalarSimAussage, 676534439246503231),
  (`Gabbro.Core.Ast.Semantik.KontrollflussSimAussage, 1927919718525879389),
  (`Gabbro.Core.Ast.Semantik.AufrufSchleifeSimAussage, 13795266634228367384),
  (`Gabbro.Core.Ast.Semantik.AggregatSimAussage, 17753571956087113725),
  (`Gabbro.Core.Ast.Semantik.VarianteSimAussage, 17665297750242263679),
  (`Gabbro.Core.Ast.Semantik.TextSimAussage, 9813248759695306163),
  (`Gabbro.Core.Maschine.I.Haengt, 6894787070203168920),
  (`Gabbro.Core.Maschine.I.RegelKomponierbar, 2131622631997208645),
  (`Gabbro.Core.Annahme.Akzeptiert, 14785600931209126213),
  (`Gabbro.Core.Annahme.Lokal, 8537419093173066105),
  (`Gabbro.Core.Annahme.AussenLokal, 2850687780170911524),
  (`Gabbro.Core.Annahme.KlauselnWahr, 8082805075160504394),
  (`Gabbro.Core.Annahme.WaechterHalten, 1202060150610760878),
  (`Gabbro.Core.Annahme.GeschlossenWartend, 6249161161004728275),
  (`Gabbro.Core.Maschine.PartielleOperation, 17845138986886266319),
  (`Gabbro.Core.Annahme.waechterBedarf, 2466293456166709549),
  (`Gabbro.Core.Fortschritt.Klasse, 7205213477869984243),
  (`Gabbro.Core.Fortschritt.DeadlockFrei, 16943362007587733102),
  (`Gabbro.Core.Fortschritt.StarvationFrei, 15370919905938327436),
  (`Gabbro.Core.Fortschritt.LockFrei, 2551997228544415486),
  (`Gabbro.Core.Fortschritt.WaitFrei, 807206487104895166),
  (`Gabbro.Core.Fortschritt.KlassenFortschritt, 9056879346766445553)]

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
    (`Gabbro.Core.Ast.Decl.function, `Gabbro.Core.Ast.Semantik.functionEntry) ], #[
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
    (`Gabbro.Core.Ast.Semantik.Befehl.waehleUmgebung, `Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage),
    (`Gabbro.Core.Ast.Semantik.Befehl.bindeRegion, `Gabbro.Core.Ast.Semantik.RegionBindUnitAussage) ]⟩]

/-- Change only the proof slot when a scoped form is closed. -/
private meta def scopedEntries : Array RegistryPacket := #[
  ⟨`Gabbro.Core.Ast.Expr.arrayValue, `Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, some `Gabbro.Core.Ast.Semantik.arrayValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.arrayIndex, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, some `Gabbro.Core.Ast.Semantik.arrayIndexEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.tupleValue, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.tupleField, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.recordValue, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.recordField, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.variantValue, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket, some `Gabbro.Core.Ast.Semantik.variantValueEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, some `Gabbro.Core.Ast.Semantik.textLiteralEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket, some `Gabbro.Core.Ast.Semantik.textConcatEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket, some `Gabbro.Core.Ast.Semantik.textIndexEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket, some `Gabbro.Core.Ast.Semantik.textLengthEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket, some `Gabbro.Core.Ast.Semantik.substringEntry⟩,
  ⟨`Gabbro.Core.Ast.Expr.optionIsSome, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.tupleBind, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.assignField, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.letMutableValue, `Gabbro.Core.Ast.Semantik.MutableValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.variantMatch, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, some `Gabbro.Core.Ast.Semantik.variantMatchEntry⟩,
  ⟨`Gabbro.Core.Ast.Stmt.letOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.retOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Decl.record, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Decl.tagged, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, some `Gabbro.Core.Ast.Semantik.taggedDeclEntry⟩,
  ⟨`Gabbro.Core.Ast.Decl.table, `Gabbro.Core.Ast.Semantik.TableProofPacket, some `Gabbro.Core.Ast.Semantik.tableEntry⟩,
  ⟨`Gabbro.Core.Ast.Decl.effectGroup, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, some `Gabbro.Core.Ast.Semantik.effectGroupEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueArray, `Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, some `Gabbro.Core.Ast.Semantik.buildArrayEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesArray, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, some `Gabbro.Core.Ast.Semantik.liesArrayEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueTupel, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesTupelfeld, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueRecord, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesRecordFeld, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.bindeTupel, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.setzeRecordFeld, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereRecord, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueVariante, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket, some `Gabbro.Core.Ast.Semantik.buildVariantEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.waehleVariante, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, some `Gabbro.Core.Ast.Semantik.waehleVariantEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereVariante, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, some `Gabbro.Core.Ast.Semantik.definiereVariantEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, some `Gabbro.Core.Ast.Semantik.textLiteralBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket, some `Gabbro.Core.Ast.Semantik.textConcatBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket, some `Gabbro.Core.Ast.Semantik.textIndexBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket, some `Gabbro.Core.Ast.Semantik.textLengthBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket, some `Gabbro.Core.Ast.Semantik.substringBefehlEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereTraeger, `Gabbro.Core.Ast.Semantik.TableProofPacket, some `Gabbro.Core.Ast.Semantik.buildTableEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.optionIstBesetzt, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereEffektgruppe, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, some `Gabbro.Core.Ast.Semantik.buildEffectGroupEntry⟩]

private meta def auxiliaryEntries : Array RegistryPacket := #[
  ⟨`Gabbro.Core.Ast.WrittenType.bool, `Gabbro.Core.Ast.Semantik.BoolTypeRegistryAussage, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.integer, `Gabbro.Core.Ast.Semantik.IntegerTypeRegistryAussage, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.array, `Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, some `Gabbro.Core.Ast.Semantik.arrayTypeEntry⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.tuple, `Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, none⟩,
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
    errors := errors ++ (← semanticsErrors index wildcardRoots catalogueKinds scanned)
    if let some spec := closing then
      errors := errors ++ (← closingErrors spec pins (imported.setExporting true) index)
    return dependencyErrors ++ (← withoutModifyingState declarationTask.get) ++ errors
  errors := errors ++ elaboratedErrors
  for error in errors do
    logError error
  logInfo m!"Core guards ran in {(← IO.monoMsNow) - started} ms"

end Gabbro.Core.Waechter
