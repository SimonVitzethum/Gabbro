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
  (`Gabbro.Core.Ast.Ty, 12782873945396265670),
  (`Gabbro.Core.Ast.Local, 3790732133586003643),
  (`Gabbro.Core.Ast.Expr, 9528347216282307943),
  (`Gabbro.Core.Ast.Stmt, 5262650281051958971),
  (`Gabbro.Core.Ast.Block, 554026736110315180),
  (`Gabbro.Core.Ast.Decl, 7135683955101088422),
  (`Gabbro.Core.Ast.UnitBody, 12910938552000479105),
  (`Gabbro.Core.Ast.Unit, 8561659821477951161),
  (`Gabbro.Core.Ast.Parse, 7662161646515821401),
  (`Gabbro.Core.Ast.Bezeichnet, 17783779404160999950),
  (`Gabbro.Core.Ziel.Rahmen, 11884202126975013255),
  (`Gabbro.Core.Ziel.NichtLeer, 3734935478639616152),
  (`Gabbro.Core.Ziel.Verfeinert, 6262184474930089844),
  (`Gabbro.Core.Ziel.NI, 7136388435487395955),
  (`Gabbro.Core.Ziel.GabbroZielForm, 10442611768856402706),
  (`Gabbro.Core.Ziel.Sicherheit, 3609222519026224003),
  (`Gabbro.Core.Ziel.SicherheitNichtLeer, 3680087890639914969),
  (`Gabbro.Core.Ziel.GabbroSicherheitForm, 14131772821008578448),
  (`Gabbro.Core.Sicherheit.ToctouFrei, 11381814552534556595),
  (`Gabbro.Core.Sicherheit.Rennfrei, 12472433670687765624),
  (`Gabbro.Core.Sicherheit.InvariantenErhalten, 7597918355407308461),
  (`Gabbro.Core.Sicherheit.Speichersicher, 11710885866490055687),
  (`Gabbro.Core.Katalog.Hardware, 15597978166845504711),
  (`Gabbro.Core.Katalog.FairLaeufe, 8964919104053723618),
  (`Gabbro.Core.Katalog.ZulStart, 13125439710374010607),
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
  (`Gabbro.Core.Maschine.Laeufe, 10295988679746434946),
  (`Gabbro.Core.Maschine.I.Laeufe, 5038720100858755217),
  (`Gabbro.Core.Maschine.I.AussenBezug, 14545744460845935956),
  (`Gabbro.Core.Maschine.I.Bestimmt, 9030341408699802814),
  (`Gabbro.Core.Maschine.I.Fortschritt, 14331443440873085814),
  (`Gabbro.Core.Maschine.I.Sim, 11481878824407565002),
  (`Gabbro.Core.Maschine.I.Haengt, 3926075680164924931),
  (`Gabbro.Core.Maschine.I.RegelKomponierbar, 2131622631997208645),
  (`Gabbro.Core.Annahme.Akzeptiert, 1850904904185999708),
  (`Gabbro.Core.Annahme.Lokal, 8784920126825670562),
  (`Gabbro.Core.Annahme.AussenLokal, 7307448124395715955),
  (`Gabbro.Core.Annahme.KlauselnWahr, 14364699446252582715),
  (`Gabbro.Core.Annahme.WaechterHalten, 17221166307777910703),
  (`Gabbro.Core.Annahme.GeschlossenWartend, 7241406859196003142),
  (`Gabbro.Core.Annahme.PartielleOperation, 2295140537526814431),
  (`Gabbro.Core.Annahme.waechterBedarf, 9908614701891846494)]

private meta def safety : Array Name := #[
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
    `Gabbro.Core.Annahme.PartielleOperation,
    `Gabbro.Core.Annahme.Operanden,
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
private meta def registry : Array RegistryFamily := #[]
private meta def wildcardRoots : Array Name := #[
  `Gabbro.Core.Maschine.I.Schritt, `Gabbro.Core.Maschine.ImplSchritt,
  `Gabbro.Core.Maschine.I.linearisiert_in_I, `Gabbro.Core.Maschine.I.replay_rahmen]
private meta def catalogueKinds : Array ClosedKinds := #[
  ⟨`Gabbro.Core.Maschine.Ergebnis, [`Gabbro.Core.Maschine.Ergebnis.ende, `Gabbro.Core.Maschine.Ergebnis.katalog]⟩,
  ⟨`Gabbro.Core.Katalog.Ereignis, [`Gabbro.Core.Katalog.Ereignis.frage, `Gabbro.Core.Katalog.Ereignis.antwort,
    `Gabbro.Core.Katalog.Ereignis.interrupt, `Gabbro.Core.Katalog.Ereignis.geraet, `Gabbro.Core.Katalog.Ereignis.dma,
    `Gabbro.Core.Katalog.Ereignis.seite, `Gabbro.Core.Katalog.Ereignis.persistenz]⟩]
private meta def closing : Option ClosingSpec := none

private meta def auditBatches (items : Array α) : Array (Array α) := Id.run do
  let batchSize := max 1 ((items.size + 11) / 12)
  let mut batches := #[]
  for batch in [:12] do
    let start := batch * batchSize
    if start >= items.size then break
    batches := batches.push (items.extract start (start + batchSize))
  return batches

/-- Runs the package guards after the root's model imports have been elaborated. -/
elab "#check_core" : command => do
  let started ← IO.monoMsNow
  let root ← IO.FS.realPath (← getFileName)
  let (sources, layoutErrors) ← readCoreSources root
  let imported ← getEnv
  let scans := (auditBatches sources).map fun batch =>
    Task.spawn fun _ => batch.map fun source => (source, auditSource imported source)
  let (hygiene, reached) := packageErrors sources
  -- An orphan need not have any compiled artifact. Check the reached modules without it.
  let reachableSources := sources.filter (reached.contains ·.moduleName)
  let env ← auditEnvironment reachableSources
  let scanned := scans.flatMap (·.get)
  let mut errors := layoutErrors ++ hygiene ++ (scanned.flatMap (·.2.errors))
  let env := withAxiomSummaries (env.setExporting false)
  let elaboratedErrors ← liftTermElabM <| withEnv env do
    let declarationTask ← Meta.MetaM.asTask' (proofErrors (auditBatches (coreDeclarations env)))
    let roots := pins.map (·.1) ++ acceptance.acceptance ++ acceptance.ideal ++ safety ++ wildcardRoots
    let closingRoots := closing.toArray.flatMap fun spec => #[spec.shape, spec.frame]
    let index := indexDependencies env roots closingRoots (closing.map (·.trustedRoots) |>.getD {})
    let mut errors := compiledImportErrors env ++ pinErrors env index pins ++ acceptanceErrors env index acceptance
    errors := errors ++ safetyErrors env index safety
    errors := errors ++ (← registryErrors registry)
    errors := errors ++ (← semanticsErrors index wildcardRoots catalogueKinds scanned)
    if let some spec := closing then
      errors := errors ++ (← closingErrors spec pins (imported.setExporting true) index)
    return errors ++ (← withoutModifyingState declarationTask.get)
  errors := errors ++ elaboratedErrors
  for error in errors do
    logError error
  logInfo m!"Core guards ran in {(← IO.monoMsNow) - started} ms"

end Gabbro.Core.Waechter
