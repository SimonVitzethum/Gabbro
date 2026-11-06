/- C16 close-out (4): end-to-end acceptance from source text with a real Duty.

    From `checkText` through lex/parse/elaborate (`elabText`), lowering
    (`lowerAllg`) and the derived `CheckDecl`s (`uCheckDecls`): the unit's Duty
    is a declared mark of its own declaration (`checkU_duty_marke`,
    `checkU_duty_deklariert`), the probe threads it through its lowered
    signature and the gate wrapper discharges it (`checkU_probe_threadet`,
    `checkU_tor_threadet`), and `AkzeptiertX` accepts the unit with the derived
    checks (`checkU_akzeptiert`) -- no vacuous leg. The admission Prop follows
    (`checkU_admission`). A dropped Duty is refused, never silently admitted:
    without the wrapper the derivation fails (`checkU_ohne_huelle`), and with
    the probe's `gibt` emptied `checkB` answers `false`
    (`checkU_gibt_abgelehnt`). -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.UebersetzeAllg3
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Admission
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Export

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

local instance (u : UProg) : DecidableEq (declOf u).Ax :=
  inferInstanceAs (DecidableEq (Fin u.axs.length))

private theorem admission_source : elabText checkText = .ok admissionUnitMade.val :=
  (elabText_phases text_source text_lexed text_parsed).trans admission_unit

/-- The source-text unit elaborates. -/
theorem checkText_ok : (elabText checkText).toOption.isSome = true := by
  rw [admission_source]
  rfl

/-- The elaborated unit behind the end-to-end witness. -/
def checkU : UProg := (elabText checkText).toOption.get checkText_ok

private theorem admission_unit_actual : checkU = admissionUnitMade.val :=
  Except.ok.inj ((except_ok_get (x := elabText checkText) checkText_ok).symm.trans admission_source)

private theorem admission_facts_actual : CheckWitness checkU 0 :=
  Eq.mpr (congrArg (fun unit : UProg => CheckWitness unit 0) admission_unit_actual) admission_facts

/-- The unit carries its Duty in the mark table. -/
theorem checkU_marken : checkU.marken = ["p#duty"] := admission_facts_actual.marks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The unit lowers. -/
theorem checkU_lowered : (lowerAllg checkU).toOption.isSome = true := admission_facts_actual.lowered

/-- The lowered program behind the end-to-end witness. -/
def checkP : Programm (declOf checkU) :=
  ((lowerAllg checkU).toOption.get checkU_lowered).1

/-- The checks derive. -/
theorem checkU_checks_ok : (uCheckDecls checkU).toOption.isSome = true := admission_facts_actual.derived

/-- The derived checks behind the end-to-end witness. -/
def checkChecks : List (CheckDecl (declOf checkU)) :=
  (uCheckDecls checkU).toOption.get checkU_checks_ok

/-! ## The Duty is declared and threaded, non-vacuously -/

/-- The derived check travels under its elaborated name: the acceptance below
    is non-vacuous. -/
theorem checkU_checks_namen :
    (uCheckDecls checkU).map (List.map CheckDecl.name) = .ok ["p"] := admission_facts_actual.names

/-- The Duty is the declared mark `p#duty` at stage 0. -/
theorem checkU_duty_marke :
    (uCheckDecls checkU).map
      (List.map fun d => (checkU.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := admission_facts_actual.duty

/-- Every derived Duty resolves to a name in the mark table: declared, never
    invented. -/
theorem checkU_duty_deklariert :
    (uCheckDecls checkU).map (fun cs => cs.all fun d =>
      decide (checkU.marken.get d.duty.1 ∈ checkU.marken)) = .ok true := admission_facts_actual.declared

/-- The probe consumes and produces exactly the Duty in its lowered
    signature: nothing is dropped at lowering. -/
theorem checkU_probe_threadet :
    (uCheckDecls checkU).map (fun cs => cs.all fun d =>
      decide (((declOf checkU).signatur d.probe).konsumiert = [d.duty]) &&
      decide (((declOf checkU).signatur d.probe).produziert = [d.duty])) =
    .ok true := admission_facts_actual.probe

/-- Every gate wrapper discharges that same Duty. -/
theorem checkU_tor_threadet :
    (uCheckDecls checkU).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf checkU).signatur g).konsumiert)) =
    .ok true := admission_facts_actual.gates

/-! ## Acceptance with the real Duty -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The lowered unit with its derived checks is admitted by `checkB`: the
    Duty mark of every check is declared, threaded and discharged. -/
theorem checkU_checkB :
    checkB checkP [] [] (List.finRange checkU.fns.length) checkChecks = true := admission_facts_actual.admitted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- End-to-end acceptance from source text with a real, non-vacuous Duty:
    `AkzeptiertX` holds with the derived checks, not the empty leg. -/
theorem checkU_akzeptiert :
    AkzeptiertX checkP (Cover.Differenz.sperrFamilie checkU)
      (List.finRange checkU.fns.length) [] [] [] [] checkChecks = true := admission_facts_actual.accepted

/-- The unit has no tables and no statics: the admission below quantifies over
    empty carrier lists. -/
theorem checkU_tabs_leer : checkU.tabs = [] := admission_facts_actual.tabs

theorem checkU_globs_leer : checkU.globs = [] := admission_facts_actual.globs

/-- The admission Prop follows from the Bool: the derived check expands
    exactly over the lowered program. -/
theorem checkU_admission :
    CheckAdmission checkP (List.finRange checkU.fns.length) checkChecks :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : checkU.tabs.length = 0 := congrArg List.length checkU_tabs_leer
      have t' : Fin checkU.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : checkU.globs.length = 0 := congrArg List.length checkU_globs_leer
      have g' : Fin checkU.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp checkU_checkB

/-! ## Refusals: a dropped Duty is refused -/

/-- Without its wrapper the check does not derive: the Duty-consuming gate
    is gone, refused by name instead of silently admitted. -/
def checkUOhneHuellen : UProg :=
  { checkU with fns := checkU.fns.filter fun f => !(strEq f.name "p#tor#g") }

/-- The wrapper-less unit derives nothing. -/
theorem checkU_ohne_huelle :
    uCheckDecls checkUOhneHuellen = .error "function unknown: p#tor#g" := by
  unfold checkUOhneHuellen
  rw [admission_unit_actual, admissionWithoutWrappersMade.property]
  exact admission_wrapper_refused

/-- The probe with its `gibt` emptied: the Duty would be dropped. -/
def checkUOhneGibt : UProg :=
  { checkU with fns := checkU.fns.map fun f =>
    (if strEq f.name "p#probe" then { f with gibt := [] } else f) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Removing `gibt` cannot silently drop a physical mark at return: the
    actual body still holds it, so ordinary lowering refuses the mismatch. -/
theorem checkU_gibt_abgelehnt :
    (lowerAllg checkUOhneGibt).toOption.isNone = true := by
  unfold checkUOhneGibt
  rw [admission_unit_actual, admissionWithoutGivesMade.property]
  exact admission_gives_refused

end Gabbro.Grammatik.Parser.Uebersetze
