/- C16 remaining forms (1): floors end to end, both verdicts.

   A declared floor (`floor` over the measured places) elaborates with the
   ordinary predicate reader and is retained on the elaborated check
   (`UCheck.boeden`); the derived `CheckDecl` carries one floor entry per
   elaborated floor. The probe body stays ordinary code returning the verdict;
   the report carries the evaluated floor outcomes beside that verdict. Both
   verdicts complete the Duty: the passing floor (true report) and the failing
   floor (false report) each discharge through the gate wrapper, and the
   discharged entry satisfies the goal leg. The measured local and comparison
   are executable code in the ordinary probe; `recordCheckCode` captures every return
   in its actual scope. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.UebersetzeAllg3
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof
public import Grammatik.Kern.Syntax.Satz.PruefungMessung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Floor
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Text
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import Grammatik.Parser.Elab.UebersetzePipeline

import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

/-! ## The floored units, from source text -/

/-- The passing floor: the probe answers `true`, the floor holds. -/
def checkTextBodenWahr : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { let x: u64 = 3; return x >= 2; } floor x >= 2 }"

/-- The failing floor: the probe answers `false`, the floor fails -- a completed
    measurement with a negative verdict, never a missing run. -/
def checkTextBodenFalsch : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { let x: u64 = 3; return x >= 4; } floor x >= 4 }"

-- The complete original strings pass the certified lexer/parser phases; the
-- resulting unit is the canonical elaborator's output, not a hand-built fixture.
private theorem bodenWahr_characters :
    checkTextBodenWahr = String.ofList passingCharacters := by cbv

private theorem bodenFalsch_characters :
    checkTextBodenFalsch = String.ofList failingCharacters := by cbv

private theorem bodenWahr_source : elabText checkTextBodenWahr = .ok floorPassingUnitMade.val :=
  (elabText_phases bodenWahr_characters passing_lexed passing_parsed).trans floorPassing_unit

private theorem bodenFalsch_source : elabText checkTextBodenFalsch = .ok floorFailingUnitMade.val :=
  (elabText_phases bodenFalsch_characters failing_lexed failing_parsed).trans floorFailing_unit

/-- Both floored units elaborate. -/
theorem checkTextBodenWahr_ok : (elabText checkTextBodenWahr).toOption.isSome = true := by
  rw [bodenWahr_source]
  rfl

theorem checkTextBodenFalsch_ok : (elabText checkTextBodenFalsch).toOption.isSome = true := by
  rw [bodenFalsch_source]
  rfl

/-- The elaborated units behind the floor witnesses. -/
def uBodenWahr : UProg := (elabText checkTextBodenWahr).toOption.get checkTextBodenWahr_ok

def uBodenFalsch : UProg := (elabText checkTextBodenFalsch).toOption.get checkTextBodenFalsch_ok

private theorem bodenWahr_facts : CheckWitness uBodenWahr 1 := by
  simpa only [uBodenWahr, bodenWahr_source, Except.toOption, Option.get_some] using floorPassing_facts

private theorem bodenFalsch_facts : CheckWitness uBodenFalsch 1 := by
  simpa only [uBodenFalsch, bodenFalsch_source, Except.toOption, Option.get_some] using floorFailing_facts

/-- The floors elaborate to the retained comparison predicates. -/
example : (elabText checkTextBodenWahr).map (fun u => u.checks.map (·.boeden.length)) =
    .ok [1] := by
  rw [bodenWahr_source]
  exact congrArg (fun xs : List Nat => (Except.ok xs : Except String (List Nat)))
    floorPassing_facts.sourceFloors

/-- Both units lower. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uBodenWahr_lowered : (lowerAllg uBodenWahr).toOption.isSome = true := bodenWahr_facts.lowered

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uBodenFalsch_lowered : (lowerAllg uBodenFalsch).toOption.isSome = true := bodenFalsch_facts.lowered

/-- The lowered programs behind the floor witnesses. -/
def checkPBodenWahr : Programm (declOf uBodenWahr) :=
  ((lowerAllg uBodenWahr).toOption.get uBodenWahr_lowered).1

def checkPBodenFalsch : Programm (declOf uBodenFalsch) :=
  ((lowerAllg uBodenFalsch).toOption.get uBodenFalsch_lowered).1

/-- The checks derive, each with one floor entry. -/
theorem uBodenWahr_checks_ok : (uCheckDecls uBodenWahr).toOption.isSome = true := bodenWahr_facts.derived

theorem uBodenFalsch_checks_ok : (uCheckDecls uBodenFalsch).toOption.isSome = true := bodenFalsch_facts.derived

def checkChecksBodenWahr : List (CheckDecl (declOf uBodenWahr)) :=
  (uCheckDecls uBodenWahr).toOption.get uBodenWahr_checks_ok

def checkChecksBodenFalsch : List (CheckDecl (declOf uBodenFalsch)) :=
  (uCheckDecls uBodenFalsch).toOption.get uBodenFalsch_checks_ok

/-! ## The Duty is declared and threaded, non-vacuously -/

/-- The derived checks travel under their elaborated names. -/
theorem bodenWahr_namen :
    (uCheckDecls uBodenWahr).map (List.map CheckDecl.name) = .ok ["p"] := bodenWahr_facts.names

theorem bodenFalsch_namen :
    (uCheckDecls uBodenFalsch).map (List.map CheckDecl.name) = .ok ["p"] := bodenFalsch_facts.names

/-- The Duty is the declared mark `p#duty` at stage 0. -/
theorem bodenWahr_duty_marke :
    (uCheckDecls uBodenWahr).map
      (List.map fun d => (uBodenWahr.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := bodenWahr_facts.duty

theorem bodenFalsch_duty_marke :
    (uCheckDecls uBodenFalsch).map
      (List.map fun d => (uBodenFalsch.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := bodenFalsch_facts.duty

/-- Every derived Duty resolves to a name in the mark table. -/
theorem bodenWahr_duty_deklariert :
    (uCheckDecls uBodenWahr).map (fun cs => cs.all fun d =>
      decide (uBodenWahr.marken.get d.duty.1 ∈ uBodenWahr.marken)) = .ok true := bodenWahr_facts.declared

theorem bodenFalsch_duty_deklariert :
    (uCheckDecls uBodenFalsch).map (fun cs => cs.all fun d =>
      decide (uBodenFalsch.marken.get d.duty.1 ∈ uBodenFalsch.marken)) = .ok true := bodenFalsch_facts.declared

/-- The probe threads exactly the Duty in its lowered signature. -/
theorem bodenWahr_probe_threadet :
    (uCheckDecls uBodenWahr).map (fun cs => cs.all fun d =>
      decide (((declOf uBodenWahr).signatur d.probe).konsumiert = [d.duty]) &&
      decide (((declOf uBodenWahr).signatur d.probe).produziert = [d.duty])) =
    .ok true := bodenWahr_facts.probe

theorem bodenFalsch_probe_threadet :
    (uCheckDecls uBodenFalsch).map (fun cs => cs.all fun d =>
      decide (((declOf uBodenFalsch).signatur d.probe).konsumiert = [d.duty]) &&
      decide (((declOf uBodenFalsch).signatur d.probe).produziert = [d.duty])) =
    .ok true := bodenFalsch_facts.probe

/-- Every gate wrapper discharges that same Duty. -/
theorem bodenWahr_tor_threadet :
    (uCheckDecls uBodenWahr).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf uBodenWahr).signatur g).konsumiert)) =
    .ok true := bodenWahr_facts.gates

theorem bodenFalsch_tor_threadet :
    (uCheckDecls uBodenFalsch).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf uBodenFalsch).signatur g).konsumiert)) =
    .ok true := bodenFalsch_facts.gates

/-- Every derived check carries exactly one floor entry. -/
theorem bodenWahr_boeden :
    (checkChecksBodenWahr.map fun d => d.boden.length) = [1] := bodenWahr_facts.floorCounts

theorem bodenFalsch_boeden :
    (checkChecksBodenFalsch.map fun d => d.boden.length) = [1] := bodenFalsch_facts.floorCounts

/-- Every derived gate list names exactly the one wrapper. -/
theorem bodenWahr_tore :
    (checkChecksBodenWahr.map fun d => d.gates.length) = [1] := bodenWahr_facts.gateCounts

theorem bodenFalsch_tore :
    (checkChecksBodenFalsch.map fun d => d.gates.length) = [1] := bodenFalsch_facts.gateCounts

/-! ## Acceptance with the real Duty -/

/-- The lowered units with their derived checks are admitted. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem bodenWahr_checkB :
    checkB checkPBodenWahr [] [] (List.finRange uBodenWahr.fns.length) checkChecksBodenWahr = true := bodenWahr_facts.admitted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem bodenFalsch_checkB :
    checkB checkPBodenFalsch [] [] (List.finRange uBodenFalsch.fns.length) checkChecksBodenFalsch = true := bodenFalsch_facts.admitted

/-- End-to-end acceptance from source text with a real Duty. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem bodenWahr_akzeptiert :
    AkzeptiertX checkPBodenWahr (Cover.Differenz.sperrFamilie uBodenWahr)
      (List.finRange uBodenWahr.fns.length) [] [] [] [] checkChecksBodenWahr = true := bodenWahr_facts.accepted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem bodenFalsch_akzeptiert :
    AkzeptiertX checkPBodenFalsch (Cover.Differenz.sperrFamilie uBodenFalsch)
      (List.finRange uBodenFalsch.fns.length) [] [] [] [] checkChecksBodenFalsch = true := bodenFalsch_facts.accepted

/-- The floored units have no tables and no statics. -/
theorem uBodenWahr_tabs_leer : uBodenWahr.tabs = [] := bodenWahr_facts.tabs

theorem uBodenWahr_globs_leer : uBodenWahr.globs = [] := bodenWahr_facts.globs

theorem uBodenFalsch_tabs_leer : uBodenFalsch.tabs = [] := bodenFalsch_facts.tabs

theorem uBodenFalsch_globs_leer : uBodenFalsch.globs = [] := bodenFalsch_facts.globs

/-- The admission Props follow from the Bools. -/
theorem bodenWahr_admission :
    CheckAdmission checkPBodenWahr (List.finRange uBodenWahr.fns.length) checkChecksBodenWahr :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : uBodenWahr.tabs.length = 0 := by rw [uBodenWahr_tabs_leer]
      have t' : Fin uBodenWahr.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : uBodenWahr.globs.length = 0 := by rw [uBodenWahr_globs_leer]
      have g' : Fin uBodenWahr.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp bodenWahr_checkB

theorem bodenFalsch_admission :
    CheckAdmission checkPBodenFalsch (List.finRange uBodenFalsch.fns.length) checkChecksBodenFalsch :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : uBodenFalsch.tabs.length = 0 := by rw [uBodenFalsch_tabs_leer]
      have t' : Fin uBodenFalsch.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : uBodenFalsch.globs.length = 0 := by rw [uBodenFalsch_globs_leer]
      have g' : Fin uBodenFalsch.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp bodenFalsch_checkB

/-! ## Both verdicts complete the Duty -/

/-- Every derived check of the passing unit has exactly one floor entry. -/
theorem bodenWahr_boden_laenge (d : CheckDecl (declOf uBodenWahr))
    (hd : d ∈ checkChecksBodenWahr) : d.boden.length = 1 := by
  have hm : d.boden.length ∈ checkChecksBodenWahr.map (fun d => d.boden.length) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [bodenWahr_boeden] at hm
  exact List.mem_singleton.mp hm

/-- Every derived check of the failing unit has exactly one floor entry. -/
theorem bodenFalsch_boden_laenge (d : CheckDecl (declOf uBodenFalsch))
    (hd : d ∈ checkChecksBodenFalsch) : d.boden.length = 1 := by
  have hm : d.boden.length ∈ checkChecksBodenFalsch.map (fun d => d.boden.length) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [bodenFalsch_boeden] at hm
  exact List.mem_singleton.mp hm

/-- The passing report completes every derived check of the passing unit:
    the sample was read, the one floor holds, the verdict records it. -/
theorem bodenWahr_abschluss (d : CheckDecl (declOf uBodenWahr))
    (hd : d ∈ checkChecksBodenWahr) :
    CheckAbschluss checkPBodenWahr d messBerichtWahr := by
  obtain ⟨hexp, _, _, _, _⟩ := bodenWahr_admission
  refine ⟨hexp d hd, by decide, ?_⟩
  show messBerichtWahr.boeden.length = d.boden.length
  rw [show messBerichtWahr.boeden.length = 1 from rfl, bodenWahr_boden_laenge d hd]

/-- The failing report completes every derived check of the failing unit:
    the sample was read, the one floor failed, the negative verdict records it --
    and the same Duty is produced. -/
theorem bodenFalsch_abschluss (d : CheckDecl (declOf uBodenFalsch))
    (hd : d ∈ checkChecksBodenFalsch) :
    CheckAbschluss checkPBodenFalsch d messBerichtFalsch := by
  obtain ⟨hexp, _, _, _, _⟩ := bodenFalsch_admission
  refine ⟨hexp d hd, by decide, ?_⟩
  show messBerichtFalsch.boeden.length = d.boden.length
  rw [show messBerichtFalsch.boeden.length = 1 from rfl, bodenFalsch_boden_laenge d hd]

/-- The gate wrapper discharges the completed passing report. -/
theorem bodenWahr_entladung (d : CheckDecl (declOf uBodenWahr))
    (hd : d ∈ checkChecksBodenWahr) :
    ∃ g, CheckEntladung checkPBodenWahr d messBerichtWahr g := by
  have hlen : d.gates.length = 1 := by
    have hm : d.gates.length ∈ checkChecksBodenWahr.map (fun d => d.gates.length) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [bodenWahr_tore] at hm
    exact List.mem_singleton.mp hm
  match hg : d.gates with
  | [] => simp [hg] at hlen
  | g :: _ =>
    refine ⟨g, bodenWahr_abschluss d hd, ?_, List.mem_cons.mpr (Or.inl rfl)⟩
    have hall : (checkChecksBodenWahr.all fun d =>
        d.gates.all fun g =>
          decide (d.duty ∈ ((declOf uBodenWahr).signatur g).konsumiert)) = true := by
      have threaded := bodenWahr_tor_threadet
      have derived : uCheckDecls uBodenWahr = .ok checkChecksBodenWahr :=
        except_ok_get uBodenWahr_checks_ok
      rw [derived] at threaded
      exact Except.ok.inj threaded
    have h1 := List.all_eq_true.mp hall d hd
    have hmem : g ∈ d.gates := hg ▸ List.mem_cons_self
    have h2 := List.all_eq_true.mp h1 g hmem
    exact of_decide_eq_true h2

/-- The gate wrapper discharges the completed failing report too. -/
theorem bodenFalsch_entladung (d : CheckDecl (declOf uBodenFalsch))
    (hd : d ∈ checkChecksBodenFalsch) :
    ∃ g, CheckEntladung checkPBodenFalsch d messBerichtFalsch g := by
  have hlen : d.gates.length = 1 := by
    have hm : d.gates.length ∈ checkChecksBodenFalsch.map (fun d => d.gates.length) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [bodenFalsch_tore] at hm
    exact List.mem_singleton.mp hm
  match hg : d.gates with
  | [] => simp [hg] at hlen
  | g :: _ =>
    refine ⟨g, bodenFalsch_abschluss d hd, ?_, List.mem_cons.mpr (Or.inl rfl)⟩
    have hall : (checkChecksBodenFalsch.all fun d =>
        d.gates.all fun g =>
          decide (d.duty ∈ ((declOf uBodenFalsch).signatur g).konsumiert)) = true := by
      have threaded := bodenFalsch_tor_threadet
      have derived : uCheckDecls uBodenFalsch = .ok checkChecksBodenFalsch :=
        except_ok_get uBodenFalsch_checks_ok
      rw [derived] at threaded
      exact Except.ok.inj threaded
    have h1 := List.all_eq_true.mp hall d hd
    have hmem : g ∈ d.gates := hg ▸ List.mem_cons_self
    have h2 := List.all_eq_true.mp h1 g hmem
    exact of_decide_eq_true h2

/-- The discharged passing entry satisfies the goal leg. -/
theorem bodenWahr_treue (d : CheckDecl (declOf uBodenWahr))
    (hd : d ∈ checkChecksBodenWahr) (g : (declOf uBodenWahr).Fn)
    (h : CheckEntladung checkPBodenWahr d messBerichtWahr g) :
    Zielsatz.CheckTreueG checkPBodenWahr [d] [⟨d.probe, messBerichtWahr, false, some g⟩] :=
  treue_aus_entladung h

/-- The discharged failing entry satisfies the goal leg. -/
theorem bodenFalsch_treue (d : CheckDecl (declOf uBodenFalsch))
    (hd : d ∈ checkChecksBodenFalsch) (g : (declOf uBodenFalsch).Fn)
    (h : CheckEntladung checkPBodenFalsch d messBerichtFalsch g) :
    Zielsatz.CheckTreueG checkPBodenFalsch [d] [⟨d.probe, messBerichtFalsch, false, some g⟩] :=
  treue_aus_entladung h

/-- The emitted probe retains the comparison on the sampled local. -/
example : (uBodenWahr.fns.find? (fun f => strEq f.name "p#probe")).map
    (fun f => f.ret) =
    some (.bool (.var "#checkReport")) := bodenWahr_facts.probeReturn

example : (uBodenFalsch.fns.find? (fun f => strEq f.name "p#probe")).map
    (fun f => f.ret) =
    some (.bool (.var "#checkReport")) := bodenFalsch_facts.probeReturn

/-- A local floor cannot read a value before the local is defined. -/
example : (elabText
    "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return true; } floor x >= 2 }").toOption.isNone = true := by
  have source :
      "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return true; } floor x >= 2 }" =
        String.ofList absentCharacters := by cbv
  rw [elabText_phases source absent_lexed absent_parsed]
  exact floor_absent_refused

/-- A failed floor cannot be bypassed with an unrelated true return. -/
example : (elabText
    "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { let x: u64 = 3; return true; } floor x >= 4 }").map
    (fun u => (u.fns.find? (fun f => strEq f.name "p#report#0")).map (·.ret)) =
    .ok (some (.bool (.and (.var "v") (.var "f0")))) := by
  have source :
      "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { let x: u64 = 3; return true; } floor x >= 4 }" =
        String.ofList bypassCharacters := by cbv
  rw [elabText_phases source bypass_lexed bypass_parsed, floorBypassUnit.property]
  exact congrArg (fun ret => (Except.ok ret : Except String (Option URet))) floor_bypass_report

end Gabbro.Grammatik.Parser.Uebersetze
