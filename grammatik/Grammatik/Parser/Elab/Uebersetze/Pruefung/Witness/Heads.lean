module

public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg2.CallArguments
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.Generic.SignatureData
import all Grammatik.Parser.Elab.Generic.C09Flows

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- These are precisely the canonical lowRufKopf guards. Keep their domains
-- symbolic while deriving the full RufPasst proof, before any fixture unit.
private structure CheckCallGuards (u : UProg) (caller callee : Fin u.fns.length)
    (Λ : List (Res (declOf u))) : Prop where
  writes : ∀ t : Fin u.tabs.length, writesAt u (fnAt u callee) t = true →
    writesAt u (fnAt u caller) t = true
  globals : ∀ g : Fin u.globs.length, writesGAt u (fnAt u callee) g = true →
    writesGAt u (fnAt u caller) g = true
  held : ∀ L ∈ ((declOf u).signatur callee).haelt, Res.held (D := declOf u) L ∈ Λ
  floor : floorLeB u caller callee = true
  extra : ∀ L ∈ heldLocksD u Λ,
    L ∈ ((declOf u).signatur callee).haelt ∨ floorUeberB u callee L = true
  marks : decide (Untermulti (((declOf u).signatur callee).inputMarks.map
    (Res.vonMarke (declOf u))) Λ) = true
  owner : ownerReadyB u ((declOf u).signatur callee) = true

private theorem check_call_permission (u : UProg) (caller callee : Fin u.fns.length)
    (Λ : List (Res (declOf u))) (ready : CheckCallGuards u caller callee Λ) :
    RufPasst (declOf u) (verOf u caller) ((declOf u).signatur callee) Λ := by
  refine {
    hw := ?_
    hg := ?_
    hk := rufHk_ok u callee Λ ready.marks
    hh := ready.held
    hx := ?_
    hb := rufHb_ok u caller callee ready.floor
    ownerReady := ownerReadyB_ok u _ ready.owner }
  · intro table allowed
    rw [sigSchreibt_eq u callee table] at allowed
    rw [vSchreibt_eq u caller table]
    exact ready.writes table allowed
  · intro global allowed
    rw [sigGSchreibt_eq u callee global] at allowed
    rw [vGSchreibt_eq u caller global]
    exact ready.globals global allowed
  · intro lock member absent
    rcases ready.extra lock (heldLocksD_mem u Λ lock member) with held | below
    · exact False.elim (absent held)
    · rw [sigBoden_eq u callee]
      unfold floorUeberB at below
      cases floor : (fnAt u callee).boden with
      | none => rw [floor] at below; cases below
      | some bound =>
        rw [floor] at below
        exact ⟨bound, rfl, of_decide_eq_true below⟩

private def check_call_head (u : UProg) (caller callee : Fin u.fns.length)
    (Γ : Ctx) (Λ : List (Res (declOf u)))
    (arguments : Args (declOf u) Γ Λ ((declOf u).params callee))
    (ready : CheckCallGuards u caller callee Λ) : RufKopf u caller Γ Λ :=
  { callee := callee, args := arguments, hp := check_call_permission u caller callee Λ ready }

-- No accepted-call assumption is introduced: every guard and the actual
-- lookup and argument results are separate premises of this internal equation.
private theorem check_call_success (u : UProg) (caller callee : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u))) (name : String) (source : List UArg)
    (arguments : Args (declOf u) Γ Λ ((declOf u).params callee))
    (found : fnIdx u.fns name = .ok callee)
    (made : lowCallArgsAuxL u caller Γ fn Λ (fnAt u callee).kinds
      ((declOf u).params callee) source = .ok arguments)
    (ready : CheckCallGuards u caller callee Λ) :
    lowRufKopf u caller Γ fn Λ name source =
      .ok (check_call_head u caller callee Γ Λ arguments ready) := by
  simp only [lowRufKopf, found, made, dif_pos ready.writes, dif_pos ready.globals,
    dif_pos ready.held, dif_pos ready.floor, dif_pos ready.extra,
    dif_pos ready.marks, dif_pos ready.owner] <;> rfl

-- Transport the complete actual argument result along the canonical params
-- equality, rather than asking concrete dependent type unification to decode
-- the entire declaration while selecting a scalar argument.
private def check_arguments_cast (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    {actual recorded : List Ty} (same : actual = recorded)
    (arguments : Args (declOf u) Γ Λ recorded) : Args (declOf u) Γ Λ actual :=
  Eq.mpr (congrArg (Args (declOf u) Γ Λ) same) arguments

private theorem check_arguments_types (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u))) (kinds : List UParamArt)
    (source : List UArg) (actual recorded : List Ty) (same : actual = recorded) :
    lowCallArgsAuxL u caller Γ fn Λ kinds actual source =
      (lowCallArgsAuxL u caller Γ fn Λ kinds recorded source).map
        (check_arguments_cast u Γ Λ same) := by
  cases same
  cases lowCallArgsAuxL u caller Γ fn Λ kinds actual source <;> rfl

-- Both argument failures and successful full heads are retained. All other
-- failure branches are discharged only by the complete checked guard bundle.
private theorem check_call_phase (u : UProg) (caller callee : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u))) (name : String) (source : List UArg)
    (found : fnIdx u.fns name = .ok callee)
    (ready : CheckCallGuards u caller callee Λ) :
    lowRufKopf u caller Γ fn Λ name source =
      (lowCallArgsAuxL u caller Γ fn Λ (fnAt u callee).kinds
        ((fnAt u callee).params.map (·.2)) source).map
        (fun arguments => check_call_head u caller callee Γ Λ
          (check_arguments_cast u Γ Λ (params_eq u callee) arguments) ready) := by
  have transported := check_arguments_types u caller Γ fn Λ (fnAt u callee).kinds source
    ((declOf u).params callee) ((fnAt u callee).params.map (·.2)) (params_eq u callee)
  cases made : lowCallArgsAuxL u caller Γ fn Λ (fnAt u callee).kinds
      ((fnAt u callee).params.map (·.2)) source with
  | error error =>
    simp only [made, Except.map] at transported
    simp only [lowRufKopf, found, transported, made, Except.map]
  | ok arguments =>
    simp only [made, Except.map] at transported
    rw [check_call_success u caller callee Γ fn Λ name source
      (check_arguments_cast u Γ Λ (params_eq u callee) arguments) found transported ready]
    rfl

private theorem check_empty_flow (u : UProg) (callee : Fin u.fns.length)
    (takes : (fnAt u callee).nimmt = []) (loans : (fnAt u callee).leiht = [])
    (moves : (fnAt u callee).bewegt = []) (mints : (fnAt u callee).praegt = []) :
    ((declOf u).signatur callee).konsumiert = [] ∧
      ((declOf u).signatur callee).owner = {} := by
  change (sigAt u callee.val).konsumiert = [] ∧ (sigAt u callee.val).owner = {}
  rw [sigAt_get u callee]
  simp [mkSig, nimmtAt, leihtAt, ownerMovesAt, bewegtMovesAt, bewegtAt,
    terminalMovesAt, praegtAt, takes, loans, moves, mints]

private theorem check_no_lock (u : UProg) (empty : u.locks = [])
    (lock : (declOf u).Lock) : False := by
  have impossible : lock.val < 0 := by
    simpa only [empty, List.length_nil] using lock.isLt
  exact Nat.not_lt_zero lock.val impossible

-- A source-derived sufficient certificate for the actual gate/reporter calls.
-- The general constructor above still retains arbitrary spaces/owners/marks.
private theorem check_empty_call_guards (u : UProg) (caller callee : Fin u.fns.length)
    (Λ : List (Res (declOf u))) (tables : u.tabs = []) (globals : u.globs = [])
    (locks : u.locks = []) (callerFloor : (fnAt u caller).boden = none)
    (takes : (fnAt u callee).nimmt = []) (loans : (fnAt u callee).leiht = [])
    (moves : (fnAt u callee).bewegt = []) (mints : (fnAt u callee).praegt = []) :
    CheckCallGuards u caller callee Λ := by
  obtain ⟨ordinary, owner⟩ := check_empty_flow u callee takes loans moves mints
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro table _
    exact False.elim (Nat.not_lt_zero table.val (by
      simpa only [tables, List.length_nil] using table.isLt))
  · intro global _
    exact False.elim (Nat.not_lt_zero global.val (by
      simpa only [globals, List.length_nil] using global.isLt))
  · intro lock _
    exact False.elim (check_no_lock u locks lock)
  · simp only [floorLeB, callerFloor]
  · intro lock _
    exact False.elim (check_no_lock u locks lock)
  · have empty : ((declOf u).signatur callee).inputMarks = [] := by
      simp only [Signatur.inputMarks, ordinary, owner, OwnerFlow.inputs,
        List.map_nil, List.nil_append]
    rw [empty, List.map_nil, decide_eq_true_eq]
    exact ⟨[], List.Perm.refl [], List.nil_sublist Λ⟩
  · simp [ownerReadyB, owner, ordinary, OwnerFlow.inputs, OwnerFlow.validB, OwnerFlow.Valid]

-- These are source facts, not an admitted call or a second call checker.
-- The same source certificate supplies every caller; no dependent Fin split.
private structure CheckCallUnit (u : UProg) : Prop where
  tables : u.tabs = []
  globals : u.globs = []
  locks : u.locks = []
  headers : ∀ fn ∈ u.fns, fn.boden = none ∧ fn.leiht = [] ∧ fn.bewegt = [] ∧ fn.praegt = []

private theorem check_unit_call_ready (u : UProg) (data : CheckCallUnit u)
    (caller callee : Fin u.fns.length) (Λ : List (Res (declOf u)))
    (takes : (fnAt u callee).nimmt = []) : CheckCallGuards u caller callee Λ := by
  have callerFields := data.headers (fnAt u caller) (List.get_mem u.fns caller)
  have calleeFields := data.headers (fnAt u callee) (List.get_mem u.fns callee)
  exact check_empty_call_guards u caller callee Λ data.tables data.globals data.locks
    callerFields.1 takes calleeFields.2.1 calleeFields.2.2.1 calleeFields.2.2.2

end Gabbro.Grammatik.Parser.Uebersetze
