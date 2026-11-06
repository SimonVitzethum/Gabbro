/- C16 remaining forms (2): counterprobes end to end.

   The external `counterprobe ... expects ...` pair elaborates to the retained
   sonde identity on the check; the derived `CheckDecl` carries it, and the
   binding to the check identity (`SondenBindung`) with the artifact
   (`SondenArtefakt`) becomes ordinary decided data. Acceptance requires the
   binding: a `durchgefallen` run on the matching artifact with a false verdict
   is measured (`Gemessen`); an unrun counterprobe stays unmeasured, a stale
   artifact measures nothing, and a check without a sonde measures nothing for
   any artifact. The completed negative report discharges through the gate
   wrapper into the goal leg. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Zulassung
public import Grammatik.Parser.Elab.UebersetzeAllg3
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof
public import Grammatik.Kern.Syntax.Satz.PruefungMessung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss
public import Grammatik.Kern.Syntax.Satz.PruefungGegenprobe
public import Grammatik.Kern.Syntax.Satz.PruefungArtefakt

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeFacts
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeFacts
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeLowering
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeUnits
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Zulassung

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

local instance counterprobePublicAxiomEquality (u : UProg) : DecidableEq (declOf u).Ax :=
  inferInstanceAs (DecidableEq (Fin u.axs.length))

/-! ## The counterprobe unit, from source text -/

/-- The counterprobe unit elaborates. -/
theorem checkTextSonde_ok : (elabText checkTextSonde).toOption.isSome = true := by
  rw [sonde_source_ok]
  rfl

/-- The elaborated unit behind the counterprobe witness. -/
def uSonde : UProg := (elabText checkTextSonde).toOption.get checkTextSonde_ok

private theorem sonde_unit_actual : uSonde = sondeUnitMade.val :=
  Except.ok.inj ((except_ok_get (x := elabText checkTextSonde) checkTextSonde_ok).symm.trans
    sonde_source_ok)

private theorem sonde_facts_actual : CounterprobeFacts uSonde :=
  Eq.mpr (congrArg CounterprobeFacts sonde_unit_actual) sonde_facts

/-- The unit has no tables and no statics. -/
theorem uSonde_tabs_leer : uSonde.tabs = [] := sonde_facts_actual.common.tabs

theorem uSonde_globs_leer : uSonde.globs = [] := sonde_facts_actual.common.globs

/-- The sonde identity travels from source text to the elaborated record. -/
example : (elabText checkTextSonde).map (fun u => u.checks.map (·.sonde)) =
    .ok [some ("ext", "ext text")] := by
  have mapped := congrArg (fun result : Except String UProg =>
    result.map (fun unit => unit.checks.map (·.sonde))) sonde_source_ok
  exact mapped.trans (congrArg (fun result : List (Option (String × String)) =>
    (Except.ok result : Except String (List (Option (String × String))))) sonde_facts.sourceIdentity)

/-- The unit lowers. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uSonde_lowered : (lowerAllg uSonde).toOption.isSome = true := sonde_facts_actual.common.lowered

/-- The lowered program behind the counterprobe witness. -/
def checkPSonde : Programm (declOf uSonde) :=
  ((lowerAllg uSonde).toOption.get uSonde_lowered).1

/-- The check derives. -/
theorem uSonde_checks_ok : (uCheckDecls uSonde).toOption.isSome = true := sonde_facts_actual.common.derived

def checkChecksSonde : List (CheckDecl (declOf uSonde)) :=
  (uCheckDecls uSonde).toOption.get uSonde_checks_ok

/-! ## The Duty is declared and threaded, non-vacuously -/

/-- The derived check travels under its elaborated name. -/
theorem sonde_namen : (checkChecksSonde.map CheckDecl.name) = ["p"] := by
  have getter := congrArg (fun result : Except String (List (CheckDecl (declOf uSonde))) =>
    result.map (List.map CheckDecl.name))
      (except_ok_get (x := uCheckDecls uSonde) uSonde_checks_ok)
  exact Except.ok.inj (getter.symm.trans sonde_facts_actual.common.names)

/-- The Duty is the declared mark `p#duty` at stage 0. -/
theorem sonde_duty_marke :
    (uCheckDecls uSonde).map
      (List.map fun d => (uSonde.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := sonde_facts_actual.common.duty

/-- The probe threads exactly the Duty in its lowered signature. -/
theorem sonde_probe_threadet :
    (uCheckDecls uSonde).map (fun cs => cs.all fun d =>
      decide (((declOf uSonde).signatur d.probe).konsumiert = [d.duty]) &&
      decide (((declOf uSonde).signatur d.probe).produziert = [d.duty])) =
    .ok true := sonde_facts_actual.common.probe

/-- Every gate wrapper discharges that same Duty. -/
theorem sonde_tor_threadet :
    (uCheckDecls uSonde).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf uSonde).signatur g).konsumiert)) =
    .ok true := sonde_facts_actual.common.gates

/-- The derived check carries the sonde identity with its exact text. -/
theorem sonde_behalten :
    (checkChecksSonde.map CheckDecl.sonde) = [some ("ext", "ext text")] := sonde_facts_actual.retained

/-- One derived check: the sonde of every member is the bound one. -/
theorem sonde_behalten_single (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) : d.sonde = some ("ext", "ext text") := by
  have hm : d.sonde ∈ checkChecksSonde.map CheckDecl.sonde :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [sonde_behalten] at hm
  exact List.mem_singleton.mp hm

/-- The derived check carries no floor entries. -/
theorem sonde_boeden :
    (checkChecksSonde.map fun d => d.boden.length) = [0] := sonde_facts_actual.common.floorCounts

/-- The derived check is not a test build. -/
theorem sonde_testbau :
    (checkChecksSonde.map CheckDecl.testbau) = [false] := sonde_facts_actual.testBuild

theorem sonde_testbau_single (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) : d.testbau = false := by
  have hm : d.testbau ∈ checkChecksSonde.map CheckDecl.testbau :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [sonde_testbau] at hm
  exact List.mem_singleton.mp hm

/-! ## Acceptance with the real Duty -/

/-- The lowered unit with its derived check is admitted. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sonde_checkB :
    checkB checkPSonde [] [] (List.finRange uSonde.fns.length) checkChecksSonde = true := sonde_facts_actual.common.admitted

/-- End-to-end acceptance from source text with a real Duty. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sonde_akzeptiert :
    AkzeptiertX checkPSonde (Cover.Differenz.sperrFamilie uSonde)
      (List.finRange uSonde.fns.length) [] [] [] [] checkChecksSonde = true := sonde_facts_actual.common.accepted

/-- The admission Prop follows from the Bool. -/
theorem sonde_admission :
    CheckAdmission checkPSonde (List.finRange uSonde.fns.length) checkChecksSonde :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : uSonde.tabs.length = 0 := by rw [uSonde_tabs_leer]
      have t' : Fin uSonde.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : uSonde.globs.length = 0 := by rw [uSonde_globs_leer]
      have g' : Fin uSonde.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp sonde_checkB

/-! ## The binding, the artifact and the measured status -/

/-- The negative report completes the derived check. -/
theorem sonde_abschluss (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) :
    CheckAbschluss checkPSonde d berichtSondeFalsch := by
  obtain ⟨hexp, _, _, _, _⟩ := sonde_admission
  refine ⟨hexp d hd, by decide, ?_⟩
  show berichtSondeFalsch.boeden.length = d.boden.length
  have hlen : d.boden.length = 0 := by
    have hm : d.boden.length ∈ checkChecksSonde.map (fun d => d.boden.length) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [sonde_boeden] at hm
    exact List.mem_singleton.mp hm
  rw [show berichtSondeFalsch.boeden.length = 0 from rfl, hlen]

/-- The single bound sonde owns its name on the derived unit. -/
theorem sonde_eindeutig : SondenEindeutig checkChecksSonde :=
  sondenEindeutigB_ok.mp sonde_facts_actual.unique

/-- The unique binding: the derived check carries the external name with its
    exact text, and no other-named check of the unit carries that name. -/
theorem sonde_bindung (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) :
    SondenBindung checkChecksSonde d "ext" "ext text" := by
  refine ⟨sonde_behalten_single d hd, hd, fun e he hne => ?_⟩
  have hmem_e : e.name ∈ ["p"] := by
    have hm : e.name ∈ checkChecksSonde.map CheckDecl.name :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    rwa [sonde_namen] at hm
  have hmem_d : d.name ∈ ["p"] := by
    have hm : d.name ∈ checkChecksSonde.map CheckDecl.name :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    rwa [sonde_namen] at hm
  have heq : e.name = d.name := by
    rw [List.mem_singleton.mp hmem_e, List.mem_singleton.mp hmem_d]
  exact absurd heq hne

/-- The artifact fits the derived check: a bound sonde, the same build mode,
    and the check's exact text under the artifact's name. -/
theorem artefakt_passt_sonde (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) : artefaktPasst d artefaktSonde := by
  refine ⟨?_, ?_, "ext text", sonde_behalten_single d hd⟩
  · rw [sonde_behalten_single d hd]
  · show d.testbau = false
    exact sonde_testbau_single d hd

/-- The measured counterprobe: a failed run on the matching artifact with a
    false verdict. Acceptance requires the binding. -/
theorem gemessen_sonde (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) :
    Gemessen d artefaktSonde .durchgefallen berichtSondeFalsch :=
  ⟨rfl, rfl, artefakt_passt_sonde d hd⟩

/-- The gate wrapper discharges the completed negative report. -/
theorem sonde_entladung (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) :
    ∃ g, CheckEntladung checkPSonde d berichtSondeFalsch g := by
  have hlen : d.gates.length = 1 := by
    have hm : d.gates.length ∈ checkChecksSonde.map (fun d => d.gates.length) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    have hr : (checkChecksSonde.map fun d => d.gates.length) = [1] := sonde_facts_actual.common.gateCounts
    rw [hr] at hm
    exact List.mem_singleton.mp hm
  match hg : d.gates with
  | [] => simp [hg] at hlen
  | g :: _ =>
    refine ⟨g, sonde_abschluss d hd, ?_, List.mem_cons.mpr (Or.inl rfl)⟩
    have hall : (checkChecksSonde.all fun d =>
        d.gates.all fun g =>
          decide (d.duty ∈ ((declOf uSonde).signatur g).konsumiert)) = true := sonde_facts_actual.gateDuty
    have h1 := List.all_eq_true.mp hall d hd
    have hmem : g ∈ d.gates := hg ▸ List.mem_cons_self
    have h2 := List.all_eq_true.mp h1 g hmem
    exact of_decide_eq_true h2

/-- The discharged negative entry satisfies the goal leg. -/
theorem sonde_treue (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) (g : (declOf uSonde).Fn)
    (h : CheckEntladung checkPSonde d berichtSondeFalsch g) :
    Zielsatz.CheckTreueG checkPSonde [d] [⟨d.probe, berichtSondeFalsch, false, some g⟩] :=
  treue_aus_entladung h

/-! ## Refusals: unrun, stale and unbound counterprobes measure nothing -/

/-- An unrun counterprobe stays unmeasured, for every check and artifact. -/
theorem ungelaufen_verweigert (c : CheckDecl (declOf uSonde))
    (a : SondenArtefakt) (r : CheckReport) :
    ¬ Gemessen c a .nichtGelaufen r :=
  nichtGelaufen_unmeasured rfl

/-- A stale artifact name measures nothing on the derived check. -/
theorem artefakt_fremd_sonde (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) :
    ¬ artefaktPasst d ⟨"alt", false, "ship"⟩ := by
  intro h
  obtain ⟨_, _, t, ht⟩ := h
  have hs := sonde_behalten_single d hd
  rw [hs] at ht
  have h2 : ("ext", "ext text") = ("alt", t) := by simpa using ht
  exact absurd (congrArg Prod.fst h2) (by decide)

/-- A stale artifact never yields a measurement. -/
theorem gemessen_fremd_verweigert (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) (st : ProbenStand) :
    ¬ Gemessen d ⟨"alt", false, "ship"⟩ st berichtSondeFalsch :=
  fremd_artefakt (artefakt_fremd_sonde d hd)

/-- A check without a sonde measures nothing for any artifact: the minimal
    end-to-end check `checkU` (no `counterprobe` clause) stays unmeasured. -/
theorem checkU_sonde_leer : (checkChecks.map CheckDecl.sonde) = [none] := by
  have actual : NoSonde checkU :=
    Eq.mpr (congrArg NoSonde admission_unit_actual) admission_no_sonde
  exact actual checkU_checks_ok

/-- Acceptance requires the binding: unbound checks refuse every measurement. -/
theorem ungebunden_verweigert (d : CheckDecl (declOf checkU))
    (hd : d ∈ checkChecks) (a : SondenArtefakt) (st : ProbenStand)
    (r : CheckReport) : ¬ Gemessen d a st r := by
  intro h
  obtain ⟨_, _, hpasst⟩ := h
  obtain ⟨his, _, _⟩ := hpasst
  have hs : d.sonde = none := by
    have hm : d.sonde ∈ checkChecks.map CheckDecl.sonde :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [checkU_sonde_leer] at hm
    exact List.mem_singleton.mp hm
  exact (by decide : ¬ (none : Option (String × String)).isSome) (hs ▸ his)

/-- The counterprobe adapter is executable ordinary code and forwards the
    resolved external function's actual Boolean answer. -/
example : (uSonde.fns.find? (fun f => strEq f.name "p#sonde#ext")).map
    (fun f => (f.body, f.ret, f.nimmt, f.gibt)) =
    some ([.bindCall "ans" "ext" []], .bool (.var "ans"), [], []) := sonde_facts_actual.adapter

/-- The matching image and binding yield measured acceptance, beyond the
    structural `checkB`/`AkzeptiertX` admission above. -/
theorem sonde_nachweisB : checkChecksSonde.all (fun d =>
    sondenNachweisB checkChecksSonde d "ship" artefaktSonde
      .durchgefallen berichtSondeFalsch) = true := sonde_facts_actual.measured

theorem sonde_nachweis (d : CheckDecl (declOf uSonde))
    (hd : d ∈ checkChecksSonde) :
    SondenNachweis checkChecksSonde d "ship" artefaktSonde
      .durchgefallen berichtSondeFalsch :=
  sondenNachweisB_sound _ _ _ _ _ _ hd
    (List.all_eq_true.mp sonde_nachweisB d hd)

/-- Same name and mode, wrong image: the external result is stale. -/
theorem sonde_falsches_bild (d : CheckDecl (declOf uSonde)) :
    ¬ SondenNachweis checkChecksSonde d "ship"
      ⟨"ext", false, "old-image"⟩ .durchgefallen berichtSondeFalsch :=
  sondenNachweis_stale _ _ _ _ _ _ (by decide)

/-- Refuse the same stale image in the executable data check. -/
example : checkChecksSonde.all (fun d =>
    !(sondenArtefaktB d "ship" ⟨"ext", false, "old-image"⟩
      .durchgefallen berichtSondeFalsch)) = true := sonde_facts_actual.stale

/-- Dropping the ordinary adapter invalidates descriptor derivation too. -/
def uSondeOhneBindung : UProg :=
  { uSonde with fns := uSonde.fns.filter fun f => !strEq f.name "p#sonde#ext" }

example : (uCheckDecls uSondeOhneBindung).toOption.isNone = true := by
  unfold uSondeOhneBindung
  rw [sonde_unit_actual]
  exact sonde_without_binding_refused

/-- A bare external label has no executable binding. -/
example : (elabText
    "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"ext text\" expects ext }").toOption.isNone = true := sonde_unbound_refused

/-- An external counterprobe belongs to exactly one check. -/
example : (elabText
    "impl fn g() { return; } impl fn ext() -> bool { return false; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"one\" expects ext } check q { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"two\" expects ext }").toOption.isNone = true := sonde_duplicate_refused

end Gabbro.Grammatik.Parser.Uebersetze
