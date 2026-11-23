/-
  File:      Grammatik/Zielsatz/Waechter/Ratschen.lean
  Subject:   GUARD 5 (B24 step 0, `dokumente/PERFECT-MODEL.md` §6.7; AGENTS.md §3, §5): two ratchets over the
             SOURCE of the whole package: no new `_zeuge` theorem, and no new kernel-evaluated `decide` (the
             `decide` tactic with the `+kernel` option) outside the probe modules.

  Both are properties of the text, not of the elaborated environment (a kernel `decide` leaves no mark in the term
  that tells it from an ordinary proof, and the module system hides proofs), so the guard reads every `.lean` file
  under `Grammatik/` and `nativefloat/NativeFloat/` at elaboration time. Probe modules (a path containing `Proben`
  or `Probes`) are exempt. A `_zeuge` theorem is a `theorem`/`lemma` whose name contains `_zeuge`.
  The module imports the whole package (`Alle.Teil1`–`Teil3`), so that Lake runs it again after any change.
  RATCHET: `zeugen` (file:name) and `kernDecide` (file, count) are today's measurement; new occurrences fail,
  removed ones fail until the list is lowered.
-/
module
public import Grammatik.Zielsatz.Waechter.Grundlagen
public import Grammatik.Alle.Teil1
public import Grammatik.Alle.Teil2
public import Grammatik.Alle.Teil3
meta import Lean
meta import Grammatik.Zielsatz.Waechter.Grundlagen
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Waechter.Ratschen

open Lean Meta

/-- RATCHET: today's `_zeuge` theorems outside the probes (file:name). -/
def zeugen : List String :=
  ["Grammatik/Adaequanz/Minimal.lean:zelle_zeuge",
   "Grammatik/Bausteine/Arena/Struktur/Erkenner/ArenaErkennerZeuge.lean:nimmPush_zeuge",
   "Grammatik/Bausteine/Arena/Struktur/Erkenner/ArenaErkennerZeuge.lean:kopfUnlinkFrei_zeuge",
   "Grammatik/Bausteine/Arena/Struktur/Formen/ArenaFormZeuge.lean:push_zeuge",
   "Grammatik/Bausteine/Arena/Struktur/Formen/ArenaFormZeuge.lean:pop_zeuge'",
   "Grammatik/Bausteine/Arena/Struktur/Formen/ArenaFormZeuge.lean:blattEin_zeuge",
   "Grammatik/Bausteine/Arena/Struktur/Formen/ArenaFormZeuge.lean:blattAus_zeuge",
   "Grammatik/Bausteine/Arena/Struktur/Formen/ArenaFormZeuge.lean:unlink_zeuge",
   "Grammatik/Bausteine/Arena/Struktur/Formen/ArenaFormZeuge.lean:grow_zeuge",
   "Grammatik/Bausteine/Schablonen/SchablonenModul/Teil1.lean:lebenslauf_zeuge_halde",
   "Grammatik/Bausteine/Schablonen/SchablonenModul/Teil1.lean:lebenslauf_zeuge_atomar_verweigert",
   "Grammatik/Bausteine/Schablonen/SchablonenModul/Teil1.lean:lebenslauf_zeuge_stopp",
   "Grammatik/Bausteine/Schablonen/SchablonenModul/Teil1.lean:lebenslauf_zeuge_reserve",
   "Grammatik/Bausteine/Zeichenfolge/ZeichenfolgeGebunden.lean:bounded_string_zeuge",
   "Grammatik/Berechenbarkeit/RecursionBoundary.lean:head_zeuge",
   "Grammatik/Berechenbarkeit/RecursionBoundary.lean:step_zeuge",
   "Grammatik/Berechenbarkeit/RecursionBoundary.lean:reached_zeuge",
   "Grammatik/Berechenbarkeit/RecursionBoundary.lean:depth_zeuge",
   "Grammatik/Berechenbarkeit/RecursionBoundary.lean:accepted_zeuge",
   "Grammatik/Berechenbarkeit/Storage/CallReturn.lean:reached_zeuge",
   "Grammatik/Berechenbarkeit/Storage/CallReturn.lean:accepted_zeuge",
   "Grammatik/GabbroV/GvBaum/Teil1.lean:baumBlatt_zeuge",
   "Grammatik/GabbroV/GvBruecke.lean:kette_bruecke_zeuge",
   "Grammatik/GabbroV/GvKetten.lean:tick_runde_zeuge",
   "Grammatik/GabbroV/GvLauf.lean:kettenLauf_invariant_zeuge",
   "Grammatik/GabbroV/GvSplits.lean:kette_invariant_zeuge",
   "Grammatik/GabbroV/GvSplits.lean:kette_block_invariant_zeuge",
   "Grammatik/GabbroV/Start/GvLuecken.lean:gvLuecke_luecke_zeuge",
   "Grammatik/GabbroV/Start/GvStartPflicht.lean:gv_startPflicht_zeuge",
   "Grammatik/Gen/Zeugen/Schluss/Teil3.lean:compiler_zeugen_korrekt",
   "Grammatik/Isabelle/DeviceKonstruktor.lean:zelle_zeuge",
   "Grammatik/Kern/Semantik/Evaluation/GanzzahlMatch.lean:match_exhaustive_zeuge",
   "Grammatik/Kern/Semantik/MaschinenKette/T1/Teil2.lean:serialLink_zeuge_tabelle",
   "Grammatik/Kern/Semantik/MaschinenKette/T2.lean:serialLink_zeuge_fuer_kette",
   "Grammatik/Kern/Syntax/Profil/Teil2.lean:profil_modell_zeuge",
   "Grammatik/Kern/Syntax/Profil/Teil2.lean:bindung_fuegt_nichts_hinzu_zeuge",
   "Grammatik/Kern/Syntax/Satz/PruefungAbschluss.lean:pruef_identitaet_zeuge",
   "Grammatik/Kern/Syntax/Satz/PruefungAbschluss.lean:abschluss_wahr_zeuge",
   "Grammatik/Kern/Syntax/Satz/PruefungAbschluss.lean:abschluss_falsch_zeuge",
   "Grammatik/Kern/Syntax/Syntax/Teil3.lean:verbrauchWahl_zeuge_zwei",
   "Grammatik/Kern/Syntax/Ziel/T4/Teil1.lean:kette_mit_zeugen_schritt",
   "Grammatik/Kern/Syntax/Ziel/T4/Teil2.lean:kette_mit_zeugen",
   "Grammatik/Kern/Syntax/Ziel/T5.lean:kette_mit_zeugen_orakel",
   "Grammatik/Korpus/Programme/Einheit104.lean:contracts_refused4_zeuge",
   "Grammatik/Korpus/Referenz/Referenz104/Teil2.lean:referenz104_zeuge",
   "Grammatik/Korpus/Referenz/ReferenzB/T2/Teil1Basis.lean:refPCschreibt_zeuge",
   "Grammatik/Korpus/Referenz/ReferenzB/T3.lean:refB_schreibt_zeuge",
   "Grammatik/Korpus/Referenz/ReferenzB/T3.lean:refB_pc_schreibt_zeuge",
   "Grammatik/Logik/Fortschritt/KostenGZeuge.lean:frame_schritte_beschraenkt_zeuge",
   "Grammatik/Logik/Fortschritt/KostenGZeuge.lean:frame_schritte_beschraenkt_zeuge_schleife",
   "Grammatik/Logik/Fortschritt/KostenGZeuge.lean:fremd_zeuge_axInc",
   "Grammatik/Logik/Fortschritt/KostenGZeuge.lean:fremd_budget_erhalten_zeuge",
   "Grammatik/Logik/Ruf/Adaequat/RufAdaequatG/Steps/T11a.lean:rufG_adaequat_umkehr_zeuge",
   "Grammatik/Logik/Ruf/Adaequat/RufAdaequatG/T6/Teil1.lean:rufG_adaequat_zeuge",
   "Grammatik/Logik/Ruf/Adaequat/RufAdaequatRufG/T8a.lean:rufG_adaequat_ruf_zeuge",
   "Grammatik/Logik/Ruf/Adaequat/RufAdaequatRufG/T8a.lean:rufG_adaequat_ruf_zeuge_bind",
   "Grammatik/Logik/Ruf/Adaequat/RufAdaequatRufG/T8a.lean:rufG_adaequat_ruf_zeuge_schleife",
   "Grammatik/Logik/Ruf/Adaequat/RufAdaequatRufG/T9/Teil1.lean:rufG_adaequat_ruf_zeuge_leave",
   "Grammatik/Logik/Ruf/Adaequat/RufAdaequatRufG/T9/Teil1.lean:rufG_adaequat_ruf_zeuge_sonst",
   "Grammatik/Logik/Ruf/Hoare/HoareRuf.lean:hoare_call_zeuge",
   "Grammatik/Logik/Ruf/Maschine/RufMaschineG/T7.lean:rufG_treu_zeuge_bind_leave",
   "Grammatik/Logik/Ruf/Umkehr/RufUmkehrRufG/T5/Teil2.lean:rufG_adaequat_ruf_umkehr_zeuge",
   "Grammatik/Logik/Vertraege/Getrennt/GetrenntZeuge.lean:getrennt_ruf_rahmen_zeuge",
   "Grammatik/Logik/Vertraege/Pruefer/Witness/AtomicReadAudit.lean:gates_zeuge",
   "Grammatik/Logik/Vertraege/Pruefer/Witness/AtomicReadAudit.lean:accepted_zeuge",
   "Grammatik/Logik/Vertraege/Pruefer/Witness/AtomicReadAudit.lean:false_contract_refused_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/DisziplinBedarf/Teil2.lean:invariantenKontext_aus_disziplin_bedarf_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/Threads/MehrfadenLauf.lean:ziel_ort_mehrfaden_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/Threads/MehrfadenLauf.lean:keine_verklemmungG_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/Threads/Schiebung.lean:shl_weite_im_c_definiert_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/TravAwaitsLauf/Teil2.lean:trav_awaits_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/TravLese/Teil3.lean:_root_.Gabbro.Grammatik.rennfrei_g_voll_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/Wettlauf/Teil1.lean:Lauf.haelt_zeuge",
   "Grammatik/Nebenlaeufigkeit/Allgemein/Wettlauf/Teil1Basis.lean:offen_zeuge",
   "Grammatik/Nebenlaeufigkeit/Rennfreiheit/EigenZustandD/T4.lean:eigenzustand_nur_eigene_schritteD_rep_zeuge",
   "Grammatik/Nebenlaeufigkeit/Rennfreiheit/EigenZustandD/T5.lean:pcSchritt_fremd_fest_zeuge",
   "Grammatik/Nebenlaeufigkeit/Rennfreiheit/RennfreiG.lean:rennfrei_g_zeuge",
   "Grammatik/Nebenlaeufigkeit/Sperren/FremdSperre.lean:axiomCall_haelt_waechter_zeuge",
   "Grammatik/Nebenlaeufigkeit/Sperren/FremdSperre.lean:gutO_bewacht_zeuge",
   "Grammatik/Nebenlaeufigkeit/Sperren/Ressourceninvariante/Teil2.lean:csl_ressourceninvariante_zeuge",
   "Grammatik/Nichtinterferenz/Zeuge/Teil1.lean:n1_zeuge",
   "Grammatik/Niedrig/Erfuellbarkeit/Fixture.lean:successful_view_zeuge",
   "Grammatik/Niedrig/Erfuellbarkeit/Fixture.lean:class_refusal_zeuge",
   "Grammatik/Niedrig/Erfuellbarkeit/Fixture.lean:bounds_refusal_zeuge",
   "Grammatik/Niedrig/Erfuellbarkeit/Fixture.lean:conflicting_loan_zeuge",
   "Grammatik/Niedrig/Erfuellbarkeit/Fixture.lean:return_zeuge",
   "Grammatik/Parser/Elab/Uebersetze/Pruefung/Fremdtor/Functions.lean:wrapper_accepted_zeuge",
   "Grammatik/Parser/Round/RundlaufTok/Teil4.lean:parseTop_druck_ruf_zeuge2",
   "Grammatik/Parser/Stmt/LibraryCertificates.lean:translation_wrong_execution_zeuge",
   "Grammatik/Parser/Stmt/LibraryFixtures.lean:translation_rek_library_zeuge",
   "Grammatik/Parser/Stmt/LibraryFixtures.lean:translation_rek_lower_zeuge",
   "Grammatik/Parser/Stmt/LibraryQualifiedFixtures.lean:translation_qual_library_zeuge",
   "Grammatik/Parser/Stmt/LibraryQualifiedFixtures.lean:translation_qual_lower_zeuge",
   "Grammatik/Speichermodell/DarstellungTy.lean:cells_zeuge_ne",
   "Grammatik/Speichermodell/Payload/PayloadLitmus.lean:mp_zeuge",
   "Grammatik/Zielsatz/Eigenschaften/Divergenz/Teil2.lean:divergent_body_zeuge",
   "Grammatik/Zielsatz/Eigenschaften/Divergenz/Teil2.lean:ewig_spin_zeuge",
   "Grammatik/Zielsatz/Eigenschaften/ForeignNever.lean:nv_zeuge_gut",
   "Grammatik/Zielsatz/Eigenschaften/ForeignNever.lean:nv_zeuge_kein_out",
   "Grammatik/Zielsatz/Eigenschaften/ForeignNever.lean:nv_zeuge_nicht_leer",
   "Grammatik/Zielsatz/Eigenschaften/ForeignNever.lean:nv_zeuge_kopf_benannt",
   "Grammatik/Zielsatz/Einbettung/Zeuge.lean:einbettung_zeuge",
   "Grammatik/Zielsatz/Kern/CheckedMehrfaden.lean:accepted_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Geraet/ZielOrtGeraetZeuge/Teil2.lean:ziel_ort_geraet_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Geraet/ZielOrtSperreZeuge/T2/Teil1.lean:ziel_ort_sperre_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrt/T3a.lean:vertragAmOrtG_refP_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtGanzZeuge/Teil1.lean:ziel_ort_ganz_fortschritt_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtGanzZeuge/Teil1.lean:ziel_ort_ganz_ax_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtGanzZeuge/Teil1Basis.lean:ziel_ort_ganz_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtGanzZeuge/Teil2.lean:ziel_ort_ganz_vertrag_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtGanzZeuge/Teil2.lean:ziel_ort_voll_ax_lokal_aus_ganz_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtVollZeuge/Teil2.lean:ziel_ort_voll_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtZeuge/Teil2.lean:ziel_ort_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtZeuge/Teil2.lean:ziel_ort_zeuge_interferenz",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtZeuge/Teil2.lean:rufG_haelt_statisch_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Grundlage/ZielOrtZeuge/Teil2.lean:rufG_haelt_signatur_zeuge",
   "Grammatik/Zielsatz/ZielOrt/Rahmen/ZielOrtAxZeuge.lean:ziel_ort_voll_ax_zeuge"]

/-- RATCHET: today's kernel `decide` uses outside the probes (file, count). -/
def kernDecide : List (String × Nat) :=
  [("Grammatik/Bausteine/Arena/Struktur/ArenaDynZeuge.lean", 1),
   ("Grammatik/Bausteine/Arena/Unbounded/GRegion.lean", 2),
   ("Grammatik/Bausteine/Kernzelle/Erfuellbarkeit.lean", 4),
   ("Grammatik/Bausteine/Schablonen/ZeugeTorModell.lean", 1),
   ("Grammatik/Berechenbarkeit/RecursionBoundary.lean", 1),
   ("Grammatik/Berechenbarkeit/Storage/CallReturn.lean", 1),
   ("Grammatik/Code/Conc/Erfuellbarkeit.lean", 1),
   ("Grammatik/Code/Conc/ErfuellbarkeitFixture.lean", 4),
   ("Grammatik/GabbroV/Start/GvStartPflicht.lean", 1),
   ("Grammatik/Gen/Druck/Einheit.lean", 2),
   ("Grammatik/Gen/Erzeuger/Probe.lean", 6),
   ("Grammatik/Gen/Text/Invers/Funktion/Teil1.lean", 12),
   ("Grammatik/Gen/Text/Zeugen/M103_131.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/M103_803.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/M169_350.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/M16_13.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/M47_549.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/M49_50.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/M99_824.lean", 2),
   ("Grammatik/Gen/Text/Zeugen/N16_5.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N18_0.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N18_4.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N19/N19_0.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N19/N19_5.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N19/N19_7.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N20_1.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N23_4.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N24_0.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N3_0.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/N47_45.lean", 1),
   ("Grammatik/Gen/Text/Zeugen/Reset.lean", 2),
   ("Grammatik/Gen/Zeugen/Gap/Audit.lean", 7),
   ("Grammatik/Gen/Zeugen/Gap/F03_reg.lean", 3),
   ("Grammatik/Gen/Zeugen/M/F00_call.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F01_chain.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F02_foot.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F03_reg.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F04_nolock.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F06_pool.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F07_race.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F08_answer.lean", 2),
   ("Grammatik/Gen/Zeugen/M/F09_mask.lean", 2),
   ("Grammatik/Gen/Zeugen/M/M103_131.lean", 2),
   ("Grammatik/Gen/Zeugen/M/M103_803.lean", 2),
   ("Grammatik/Gen/Zeugen/M/M169_350.lean", 2),
   ("Grammatik/Gen/Zeugen/M/M16_13.lean", 2),
   ("Grammatik/Gen/Zeugen/M/M49_50.lean", 1),
   ("Grammatik/Gen/Zeugen/M/Recovery.lean", 1),
   ("Grammatik/Gen/Zeugen/M/ScalarRead.lean", 1),
   ("Grammatik/Gen/Zeugen/Reset.lean", 2),
   ("Grammatik/Kern/Taktik/KernelRfl.lean", 1),
   ("Grammatik/Korpus/Programme/GenOblig104.lean", 1),
   ("Grammatik/Korpus/Zeugnis/Zeugnis/T3/Teil1Basis.lean", 2),
   ("Grammatik/Korpus/Zeugnis/Zeugnis/T4Basis.lean", 1),
   ("Grammatik/Logik/Vertraege/Pruefer/Witness/AtomicReadAudit.lean", 2),
   ("Grammatik/Parser/Elab/Uebersetze/Akku/Herkunft.lean", 25),
   ("Grammatik/Parser/Elab/Uebersetze/Pruefung/Fremdtor.lean", 6),
   ("Grammatik/Parser/Elab/Uebersetze/Pruefung/Fremdtor/Functions.lean", 6),
   ("Grammatik/Parser/Elab/Uebersetze/Pruefung/Fremdtor/Source.lean", 11),
   ("Grammatik/Parser/Elab/UebersetzeAllg3/Measures/Fixtures.lean", 4),
   ("Grammatik/Parser/Elab/UebersetzeAllg3/Measures/Refusals.lean", 11),
   ("Grammatik/Parser/Elab/UebersetzeAllg3/Rest2.lean", 5),
   ("Grammatik/Parser/Elab/UebersetzeAllg3/Rest3.lean", 4),
   ("Grammatik/Parser/Expr/Ausdruck/Teil3.lean", 1),
   ("Grammatik/Parser/Round/Statements/RundlaufAnw3.lean", 1),
   ("Grammatik/Parser/Stmt/LibraryFixtures.lean", 1),
   ("Grammatik/Parser/Stmt/LibraryQualifiedFixtures.lean", 1),
   ("Grammatik/Parser/Stmt/LibraryTranslationFixtures.lean", 1),
   ("Grammatik/Zielsatz/Atomar/AtomarAkzeptiertZeuge.lean", 3),
   ("Grammatik/Zielsatz/Atomar/CallSite/CallSitePositiveFixture.lean", 1),
   ("Grammatik/Zielsatz/Atomar/CallSite/CallSiteReplayBlocker.lean", 1),
   ("Grammatik/Zielsatz/Faeden/RuheZeuge.lean", 2),
   ("Grammatik/Zielsatz/Kern/AkzeptiertZeuge.lean", 3),
   ("Grammatik/Zielsatz/Kern/CheckedMehrfaden.lean", 1),
   ("Grammatik/Zielsatz/Kern/Erfuellbarkeit.lean", 3),
   ("Grammatik/Zielsatz/Kern/PoolCertificate.lean", 5)]

/-- The Lean files of the package under the given directories, without the probes. -/
def dateien (wurzeln : List System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for w in wurzeln do
    if ← w.isDir then
      for f in ← w.walkDir do
        let s := f.toString
        if s.endsWith ".lean" && (s.splitOn "Proben").length == 1 && (s.splitOn "Probes").length == 1 then
          out := out.push f
  return out.qsort (fun a b => a.toString < b.toString)

def pruefe : MetaM Unit := do
  let muster := "decide " ++ "+kernel"
  let fs ← dateien ["Grammatik", "nativefloat/NativeFloat"]
  if fs.size < 1000 then throwError "the guard found only {fs.size} source files: wrong working directory?"
  let mut zs : List String := []
  let mut ds : List (String × Nat) := []
  for f in fs do
    let text ← IO.FS.readFile f
    let k := (text.splitOn muster).length - 1
    if k > 0 then ds := ds ++ [(f.toString, k)]
    if (text.splitOn "_zeuge").length == 1 then continue
    for zeile in text.splitOn "\n" do
      if (zeile.splitOn "_zeuge").length == 1 then continue
      let ws := ((zeile.replace "\t" " ").splitOn " ").filter (!·.isEmpty)
      for (w, v) in ws.zip (ws.drop 1) do
        if (w == "theorem" || w == "lemma") && (v.splitOn "_zeuge").length > 1 then
          zs := zs ++ [s!"{f}:{v}"]
  let befunde := (ratscheMenge zs zeugen).map ("witness theorem: " ++ ·) ++
    (ratsche ds kernDecide).map ("kernel decide: " ++ ·)
  melde s!"witnesses or kernel decide outside the probes ({zs.length} witness theorems, {ds.foldl (· + ·.2) 0} kernel decides in {fs.size} files)"
    befunde
    ("prove from general theorems instead (AGENTS.md §3, §5); lower the lists where uses were removed. " ++
     s!"Measured:\nzeugen := {alsNamen zs}\nkernDecide := {alsListe ds}")

run_meta pruefe

end Gabbro.Grammatik.Zielsatz.Waechter.Ratschen
