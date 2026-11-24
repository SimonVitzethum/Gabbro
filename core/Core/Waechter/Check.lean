module
public meta import Lean
meta import Lean.Elab.Task
meta import Core.Ast.Inventory.Entries.Arrays
meta import Core.Ast.Inventory.Entries.Option
meta import Core.Ast.Inventory.Entries.WrittenTypeStatements
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
  (`Gabbro.Core.Ast.Semantik.BoolTypeRegistryAussage, 12798303477801311497),
  (`Gabbro.Core.Ast.Semantik.IntegerTypeRegistryAussage, 2315473242246776171),
  (`Gabbro.Core.Ast.Semantik.OwnedRegionTypeRegistryAussage, 12306600108190455667),
  (`Gabbro.Core.Ast.LowLevel.schemaMem, 17663330537240466070),
  (`Gabbro.Core.Ast.LowLevel.MemRegelAntwortSicherAussage, 13180530958917619434),
  (`Gabbro.Core.Ast.LowLevel.SplitAtAussage, 12370211613065369911),
  (`Gabbro.Core.Ast.LowLevel.SplitPagesAussage, 10794451468041959651),
  (`Gabbro.Core.Ast.LowLevel.MergeAussage, 1414285457752968851),
  (`Gabbro.Core.Ast.LowLevel.NewSpaceAussage, 17441111264167071750),
  (`Gabbro.Core.Ast.LowLevel.MapAussage, 9220829017215573995),
  (`Gabbro.Core.Ast.LowLevel.ProtectAussage, 1307153427585789643),
  (`Gabbro.Core.Ast.LowLevel.UnmapAussage, 11626283661818315697),
  (`Gabbro.Core.Ast.LowLevel.FlushAussage, 148660867866084312),
  (`Gabbro.Core.Ast.LowLevel.ActivateAussage, 6030105158610253656),
  (`Gabbro.Core.Ast.Semantik.AddressTypeUnitAussage, 4941730822615214159),
  (`Gabbro.Core.Ast.Semantik.AddressTypeUnitErfuellbarAussage, 14374708897144167770),
  (`Gabbro.Core.Ast.Semantik.RegionAddressUnitAussage, 4821253191398779386),
  (`Gabbro.Core.Ast.Semantik.ViewUnitAussage, 16941075495743032652),
  (`Gabbro.Core.Ast.Semantik.RegionBindUnitAussage, 3222501905784935939),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterReadAussage, 5709775738227765852),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterWriteAussage, 16773427134140861989),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterReadElseAussage, 577199600327178392),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterRegelAntwortSicherAussage, 18238649824871300224),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterTransitionAussage, 6288700209855568683),
  (`Gabbro.Core.Ast.LowLevel.Device.LendAussage, 2549621462376397167),
  (`Gabbro.Core.Ast.LowLevel.Device.TakeBackAussage, 7678404762004743412),
  (`Gabbro.Core.Ast.LowLevel.Device.DmaAussage, 6660087069398687915),
  (`Gabbro.Core.Ast.Semantik.EnvironmentUnitAussage, 332365741710039525),
  (`Gabbro.Core.Ast.LowLevel.schema, 5975758502447882451),
  (`Gabbro.Core.Ast.LowLevel.RegelAntwortSicherAussage, 13355274141793453820),
  (`Gabbro.Core.Ast.LowLevel.AddressTypeAussage, 5317775546804310252),
  (`Gabbro.Core.Ast.LowLevel.RegionAddressAussage, 16380472560367819459),
  (`Gabbro.Core.Ast.LowLevel.ViewAussage, 16102711755038495580),
  (`Gabbro.Core.Ast.LowLevel.EnvironmentAussage, 12617065088653880787),
  (`Gabbro.Core.Beobachtung.NiedrigeBeob, 5599216887541274336),
  (`Gabbro.Core.Beobachtung.NiedrigAequiv, 3046953505163452875),
  (`Gabbro.Core.Beobachtung.LokaleGleich, 9834437015953644194),
  (`Gabbro.Core.Beobachtung.EndeSicht, 9556974322465349963),
  (`Gabbro.Core.Beobachtung.AntwortSicht, 5272787653713635787),
  (`Gabbro.Core.Beobachtung.QuellzustandGleich, 6481530046882307749),
  (`Gabbro.Core.Beobachtung.StartFlussLokal, 18446296788937562920),
  (`Gabbro.Core.Beobachtung.PlanSicht, 7884324158466133600),
  (`Gabbro.Core.Beobachtung.AusgabeZuwachs, 1485527850633908575),
  (`Gabbro.Core.Beobachtung.AusgabeSicht, 12432994889524384705),
  (`Gabbro.Core.Beobachtung.AusgabeLokal, 6805088062946349882),
  (`Gabbro.Core.Beobachtung.FormSchritt, 6257404041583297219),
  (`Gabbro.Core.Beobachtung.RegelFluss, 5986240727518793425),
  (`Gabbro.Core.Beobachtung.FlussLokal, 8476184994906608447),
  (`Gabbro.Core.Beobachtung.LaderSicht, 7611263567227901381),
  (`Gabbro.Core.Beobachtung.LaderNIPflicht, 5394147595164078153),
  (`Gabbro.Core.Beobachtung.ProtokollNIPflicht, 2516906009457701360),
  (`Gabbro.Core.Beobachtung.Nichtinterferent, 6601230751984166097),
  (`Gabbro.Core.Beobachtung.RegelNIPflicht, 6976522792872034986),
  (`Gabbro.Core.Beobachtung.FamilienNI, 1378066824215777444),
  (`Gabbro.Core.Beobachtung.ProtokollwahlNI, 4200530525082805411),
  (`Gabbro.Core.Beobachtung.SkalarNIAussage, 3635874088068385566),
  (`Gabbro.Core.Beobachtung.KontrollflussNIAussage, 11572140493953092796),
  (`Gabbro.Core.Beobachtung.AufrufSchleifeNIAussage, 1333112768278699147),
  (`Gabbro.Core.Beobachtung.AggregatNIAussage, 4992780197477053411),
  (`Gabbro.Core.Beobachtung.TextNIAussage, 4565469444067105301),
  (`Gabbro.Core.Beobachtung.VarianteNIAussage, 4573022451563620555),
  (`Gabbro.Core.Beobachtung.AntwortNIAussage, 11345518988418414144),
  (`Gabbro.Core.Beobachtung.InterruptNIAussage, 1989033255492933366),
  (`Gabbro.Core.Beobachtung.AbsturzNIAussage, 63024329139960062),
  (`Gabbro.Core.Beobachtung.RegionNIAussage, 13017023498192209700),
  (`Gabbro.Core.Beobachtung.SpeicherverwaltungsNIAussage, 4664750381144777032),
  (`Gabbro.Core.Beobachtung.GeraeteNIAussage, 1770587715731626834),
  (`Gabbro.Core.Katalog.Plattform.spekulationshuelle, 9646114676836847360),
  (`Gabbro.Core.Beobachtung.NiedrigGleich, 7436106153758641574),
  (`Gabbro.Core.Beobachtung.GleicheNiedrigeUmgebung, 6234288436884287166),
  (`Gabbro.Core.Beobachtung.GleichePolitik, 15105688279569619206),
  (`Gabbro.Core.Beobachtung.ImSchranken, 14430301138024949332),
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
  (`Gabbro.Core.Ast.Semantik.Elaboriert, 13183703242328236634),
  (`Gabbro.Core.Ast.Semantik.Bezeichnet, 4971581746999780802),
  (`Gabbro.Core.Ast.Semantik.exprSchema, 3561445603873443729),
  (`Gabbro.Core.Ast.Semantik.stmtSchema, 16511158430247645214),
  (`Gabbro.Core.Ast.Semantik.declSchema, 5940570300593919137),
  (`Gabbro.Core.Ast.Semantik.bracedSchema, 3362485737666547081),
  (`Gabbro.Core.Ast.Semantik.befehlSchema, 3651524870865739287),
  (`Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, 7129370531993862635),
  (`Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, 5807147138336817159),
  (`Gabbro.Core.Ast.Semantik.TupleValueProofPacket, 9642919166452592520),
  (`Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, 6459642599776928428),
  (`Gabbro.Core.Ast.Semantik.RecordValueProofPacket, 12089693377941428270),
  (`Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, 2893991565176026330),
  (`Gabbro.Core.Ast.Semantik.TupleBindProofPacket, 18389736596806090093),
  (`Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, 10582208274358026517),
  (`Gabbro.Core.Ast.Semantik.MutableValueProofPacket, 8932850112409237371),
  (`Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, 6057198105954152443),
  (`Gabbro.Core.Ast.Semantik.VariantValueProofPacket, 18318023229298778662),
  (`Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, 13838916812026917363),
  (`Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, 17580818402480360549),
  (`Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, 13390652131394218532),
  (`Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, 14982232331492704937),
  (`Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, 2610047381683014056),
  (`Gabbro.Core.Ast.Semantik.TextLengthProofPacket, 8557357445009761813),
  (`Gabbro.Core.Ast.Semantik.TextConcatProofPacket, 9377782233855997836),
  (`Gabbro.Core.Ast.Semantik.TextIndexProofPacket, 2539941978685392695),
  (`Gabbro.Core.Ast.Semantik.SubstringProofPacket, 7054210750487788579),
  (`Gabbro.Core.Ast.Semantik.TextTypeProofPacket, 1619162220095174908),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket, 6735030681245146276),
  (`Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket, 8913544023559627394),
  (`Gabbro.Core.Ast.Semantik.TableProofPacket, 633197898246167263),
  (`Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, 11439177605397661795),
  (`Gabbro.Core.Ast.Semantik.OptionTestProofPacket, 14254452402164840730),
  (`Gabbro.Core.Ast.Semantik.OptionMatchProofPacket, 5021562168068766500),
  (`Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, 11937044985209529627),
  (`Gabbro.Core.Sicherheit.RegelSicher, 1423892264051868710),
  (`Gabbro.Core.Sicherheit.RegelAntwortSicher, 11251389405074513903),
  (`Gabbro.Core.Sicherheit.RegelPflichten, 15707179930598521381),
  (`Gabbro.Core.Ast.Semantik.Quellform.SicherheitsAussage, 7160244122336518728),
  (`Gabbro.Core.Ast.Semantik.ProgramKernSicherheitsAussage, 10781582465234451429),
  (`Gabbro.Core.Ziel.Rahmen, 11884202126975013255),
  (`Gabbro.Core.Ziel.NichtLeer, 3734935478639616152),
  (`Gabbro.Core.Ziel.Verfeinert, 6262184474930089844),
  (`Gabbro.Core.Ziel.NI, 7136388435487395955),
  (`Gabbro.Core.Ziel.GabbroZielForm, 10442611768856402706),
  (`Gabbro.Core.Ziel.Sicherheit, 3609222519026224003),
  (`Gabbro.Core.Ziel.SicherheitNichtLeer, 3680087890639914969),
  (`Gabbro.Core.Ziel.GabbroSicherheitForm, 14131772821008578448),
  (`Gabbro.Core.Sicherheit.ToctouFrei, 13383408147655156761),
  (`Gabbro.Core.Sicherheit.Rennfrei, 16623318329282186189),
  (`Gabbro.Core.Sicherheit.InvariantenErhalten, 2519724351699677875),
  (`Gabbro.Core.Sicherheit.Speichersicher, 712188308935759762),
  (`Gabbro.Core.Katalog.Hardware, 3517031233163520317),
  (`Gabbro.Core.Katalog.FairLaeufe, 3377533376377286296),
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
  (`Gabbro.Core.Maschine.AbsturzSchritt, 118190599494727466),
  (`Gabbro.Core.Maschine.I.Schritt, 617327513307147300),
  (`Gabbro.Core.Maschine.ImplSchritt, 13092936033496988811),
  (`Gabbro.Core.Maschine.Laeufe, 12571873960916681763),
  (`Gabbro.Core.Maschine.I.Laeufe, 17967247355945508440),
  (`Gabbro.Core.Maschine.I.AussenBezug, 14545744460845935956),
  (`Gabbro.Core.Maschine.I.Bestimmt, 5694742150798589190),
  (`Gabbro.Core.Maschine.I.Fortschritt, 1830217721526817104),
  (`Gabbro.Core.Maschine.I.Sim, 5521024623855626767),
  (`Gabbro.Core.Ast.Semantik.SkalarSimAussage, 12943678712158073329),
  (`Gabbro.Core.Ast.Semantik.KontrollflussSimAussage, 9821140042002562715),
  (`Gabbro.Core.Ast.Semantik.AufrufSchleifeSimAussage, 4487859624971661886),
  (`Gabbro.Core.Ast.Semantik.AggregatSimAussage, 12725142951395975563),
  (`Gabbro.Core.Ast.Semantik.VarianteSimAussage, 17720957968414936881),
  (`Gabbro.Core.Ast.Semantik.TextSimAussage, 6533872926534190709),
  (`Gabbro.Core.Maschine.I.Haengt, 8992824583621734043),
  (`Gabbro.Core.Maschine.I.RegelKomponierbar, 2131622631997208645),
  (`Gabbro.Core.Annahme.Akzeptiert, 12530553220026648001),
  (`Gabbro.Core.Annahme.Lokal, 12350579693722623833),
  (`Gabbro.Core.Annahme.AussenLokal, 4029774292567373286),
  (`Gabbro.Core.Annahme.KlauselnWahr, 12353942747810371772),
  (`Gabbro.Core.Annahme.WaechterHalten, 6563708492780585036),
  (`Gabbro.Core.Annahme.GeschlossenWartend, 4177870225206141763),
  (`Gabbro.Core.Maschine.PartielleOperation, 17845138986886266319),
  (`Gabbro.Core.Annahme.waechterBedarf, 2466293456166709549),
  (`Gabbro.Core.Fortschritt.Klasse, 7205213477869984243),
  (`Gabbro.Core.Fortschritt.DeadlockFrei, 6418875941874835450),
  (`Gabbro.Core.Fortschritt.StarvationFrei, 5626090967859860399),
  (`Gabbro.Core.Fortschritt.LockFrei, 18035599849138421110),
  (`Gabbro.Core.Fortschritt.WaitFrei, 7129896085423078866),
  (`Gabbro.Core.Fortschritt.KlassenFortschritt, 5322603302426740766)]

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
  ⟨`Gabbro.Core.Ast.Expr.arrayIndex, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.tupleValue, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.tupleField, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.recordValue, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.recordField, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.variantValue, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Expr.optionIsSome, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.tupleBind, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.assignField, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.letMutableValue, `Gabbro.Core.Ast.Semantik.MutableValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.variantMatch, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.letOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Stmt.retOption, `Gabbro.Core.Ast.Semantik.OptionConstructorProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Decl.record, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Decl.tagged, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Decl.table, `Gabbro.Core.Ast.Semantik.TableProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Decl.effectGroup, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueArray, `Gabbro.Core.Ast.Semantik.ArrayValueProofPacket, some `Gabbro.Core.Ast.Semantik.buildArrayEntry⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesArray, `Gabbro.Core.Ast.Semantik.ArrayIndexProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueTupel, `Gabbro.Core.Ast.Semantik.TupleValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesTupelfeld, `Gabbro.Core.Ast.Semantik.TupleFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueRecord, `Gabbro.Core.Ast.Semantik.RecordValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.liesRecordFeld, `Gabbro.Core.Ast.Semantik.RecordFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.bindeTupel, `Gabbro.Core.Ast.Semantik.TupleBindProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.setzeRecordFeld, `Gabbro.Core.Ast.Semantik.AssignFieldProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereRecord, `Gabbro.Core.Ast.Semantik.RecordDeclProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.baueVariante, `Gabbro.Core.Ast.Semantik.VariantValueProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.waehleVariante, `Gabbro.Core.Ast.Semantik.VariantMatchProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereVariante, `Gabbro.Core.Ast.Semantik.TaggedDeclProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textLiteral, `Gabbro.Core.Ast.Semantik.TextLiteralProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textConcat, `Gabbro.Core.Ast.Semantik.TextConcatProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textIndex, `Gabbro.Core.Ast.Semantik.TextIndexProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.textLength, `Gabbro.Core.Ast.Semantik.TextLengthProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.substring, `Gabbro.Core.Ast.Semantik.SubstringProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereTraeger, `Gabbro.Core.Ast.Semantik.TableProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.optionIstBesetzt, `Gabbro.Core.Ast.Semantik.OptionTestProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl.definiereEffektgruppe, `Gabbro.Core.Ast.Semantik.EffectGroupProofPacket, none⟩]

private meta def auxiliaryEntries : Array RegistryPacket := #[
  ⟨`Gabbro.Core.Ast.WrittenType.bool, `Gabbro.Core.Ast.Semantik.BoolTypeRegistryAussage, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.integer, `Gabbro.Core.Ast.Semantik.IntegerTypeRegistryAussage, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.array, `Gabbro.Core.Ast.Semantik.ArrayTypeProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.tuple, `Gabbro.Core.Ast.Semantik.TupleTypeProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.text, `Gabbro.Core.Ast.Semantik.TextTypeProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.index, `Gabbro.Core.Ast.Semantik.CarrierIndexProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.indexOption, `Gabbro.Core.Ast.Semantik.CarrierIndexOptionProofPacket, none⟩,
  ⟨`Gabbro.Core.Ast.WrittenType.ownedRegion, `Gabbro.Core.Ast.Semantik.OwnedRegionTypeRegistryAussage, none⟩,
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
