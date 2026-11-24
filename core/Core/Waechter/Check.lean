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
  (`Gabbro.Core.Beobachtung.NiedrigGleich, 14656191603660804878),
  (`Gabbro.Core.Beobachtung.GleicheNiedrigeUmgebung, 17452001308781497914),
  (`Gabbro.Core.Beobachtung.GleichePolitik, 5963814770407062591),
  (`Gabbro.Core.Beobachtung.ImSchranken, 3700198419217621832),
  (`Gabbro.Core.Katalog.Katalog.dauerMaximum, 16990558230020595847),
  (`Gabbro.Core.Ast.Ty, 15487100176899724456),
  (`Gabbro.Core.Ast.Local, 17525257410544725057),
  (`Gabbro.Core.Ast.Expr, 8606431487102838548),
  (`Gabbro.Core.Ast.Stmt, 4546621363431285859),
  (`Gabbro.Core.Ast.Block, 8345591539700921648),
  (`Gabbro.Core.Ast.Decl, 6465150350800960424),
  (`Gabbro.Core.Ast.UnitBody, 516762930773383719),
  (`Gabbro.Core.Ast.Unit, 364396323052472367),
  (`Gabbro.Core.Ast.Parse, 1549730433282280622),
  (`Gabbro.Core.Ast.Bezeichnet, 14573227002043866697),
  (`Gabbro.Core.Ast.Semantik.Elaboriert, 13779991798032833931),
  (`Gabbro.Core.Ast.Semantik.Bezeichnet, 5483708933868727932),
  (`Gabbro.Core.Ast.Semantik.exprSchema, 194231170125970003),
  (`Gabbro.Core.Ast.Semantik.stmtSchema, 14541684349318389604),
  (`Gabbro.Core.Ast.Semantik.befehlSchema, 5118293204423033148),
  (`Gabbro.Core.Sicherheit.RegelSicher, 11713368170977043482),
  (`Gabbro.Core.Ziel.Rahmen, 11884202126975013255),
  (`Gabbro.Core.Ziel.NichtLeer, 3734935478639616152),
  (`Gabbro.Core.Ziel.Verfeinert, 6262184474930089844),
  (`Gabbro.Core.Ziel.NI, 7136388435487395955),
  (`Gabbro.Core.Ziel.GabbroZielForm, 10442611768856402706),
  (`Gabbro.Core.Ziel.Sicherheit, 3609222519026224003),
  (`Gabbro.Core.Ziel.SicherheitNichtLeer, 3680087890639914969),
  (`Gabbro.Core.Ziel.GabbroSicherheitForm, 14131772821008578448),
  (`Gabbro.Core.Sicherheit.ToctouFrei, 13458230556218665573),
  (`Gabbro.Core.Sicherheit.Rennfrei, 17144265909704503431),
  (`Gabbro.Core.Sicherheit.InvariantenErhalten, 16221492331599536673),
  (`Gabbro.Core.Sicherheit.Speichersicher, 11882776765286062576),
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
  (`Gabbro.Core.Maschine.Laeufe, 3454087982534677499),
  (`Gabbro.Core.Maschine.I.Laeufe, 13477579632781106936),
  (`Gabbro.Core.Maschine.I.AussenBezug, 14545744460845935956),
  (`Gabbro.Core.Maschine.I.Bestimmt, 7049320253757918330),
  (`Gabbro.Core.Maschine.I.Fortschritt, 7327703375541758626),
  (`Gabbro.Core.Maschine.I.Sim, 11481063685465942093),
  (`Gabbro.Core.Maschine.I.Haengt, 15954979937903876922),
  (`Gabbro.Core.Maschine.I.RegelKomponierbar, 2131622631997208645),
  (`Gabbro.Core.Annahme.Akzeptiert, 15234603377791923172),
  (`Gabbro.Core.Annahme.Lokal, 13003709583326167579),
  (`Gabbro.Core.Annahme.AussenLokal, 2928956100793009800),
  (`Gabbro.Core.Annahme.KlauselnWahr, 4555496438099755736),
  (`Gabbro.Core.Annahme.WaechterHalten, 5637657827783153021),
  (`Gabbro.Core.Annahme.GeschlossenWartend, 15329009898575453325),
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
    (`Gabbro.Core.Ast.Expr.binary, `Gabbro.Core.Ast.Semantik.binaryEntry)]⟩,
  ⟨`Gabbro.Core.Ast.Stmt, `Gabbro.Core.Ast.Semantik.stmtSchema, #[
    (`Gabbro.Core.Ast.Stmt.letValue, `Gabbro.Core.Ast.Semantik.letEntry)]⟩,
  ⟨`Gabbro.Core.Ast.Semantik.Befehl, `Gabbro.Core.Ast.Semantik.befehlSchema, #[
    (`Gabbro.Core.Ast.Semantik.Befehl.literal, `Gabbro.Core.Ast.Semantik.kernLiteralEntry),
    (`Gabbro.Core.Ast.Semantik.Befehl.binaer, `Gabbro.Core.Ast.Semantik.kernBinaryEntry),
    (`Gabbro.Core.Ast.Semantik.Befehl.binden, `Gabbro.Core.Ast.Semantik.kernLetEntry)]⟩]
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
    let mut errors ← registryErrors registry
    errors := errors ++ (← semanticsErrors index wildcardRoots catalogueKinds scanned)
    if let some spec := closing then
      errors := errors ++ (← closingErrors spec pins (imported.setExporting true) index)
    return dependencyErrors ++ (← withoutModifyingState declarationTask.get) ++ errors
  errors := errors ++ elaboratedErrors
  for error in errors do
    logError error
  logInfo m!"Core guards ran in {(← IO.monoMsNow) - started} ms"

end Gabbro.Core.Waechter
