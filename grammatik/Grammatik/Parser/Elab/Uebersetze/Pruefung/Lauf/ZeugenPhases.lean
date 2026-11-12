module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Units
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Calls
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Heads
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Assembly
import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
import all Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Ende
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.UebersetzeAllg3.Transition
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.Generic.StaticConformance
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


public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The source is the complete check/floor/gate fixture. Driver policy is
    explicit configuration: execute `p`, and consume its report through `g`. -/
@[expose] def retiringSelection : CheckConsumerSelection := ⟨"p", "g"⟩

-- Only the stable fixture selection/report are public. Every computation
-- packet below belongs to the private proof path, never to an exposed value.
@[expose] def retiringReport : CheckReport :=
  { proben := [⟨"x", 0, 3, true⟩], boeden := [true], urteil := true }

namespace RetiringWitness

-- Resolve the dictionary at the abstract unit, before any checker projection.
local instance retiringPhaseAxiomEquality (u : UProg) : DecidableEq (declOf u).Ax :=
  inferInstanceAs (DecidableEq (Fin u.axs.length))
local instance retiringPhaseFunctionEquality (u : UProg) : DecidableEq (declOf u).Fn :=
  inferInstanceAs (DecidableEq (Fin u.fns.length))

private def selected : {unit : UProg //
    ((elabText checkTextBodenWahr).bind fun original =>
      uSelectCheckConsumers original [retiringSelection]) = .ok unit} := by
  refine ⟨?unit, ?produced⟩
  case produced =>
    rw [bodenWahr_source]
    cbv <;> exact Eq.refl _

@[reducible, no_expose] def unit : UProg := selected.val

-- Select the actual scalar calls and returning channels at symbolic types.
-- lowRufKopf remains the complete resource/owner/footprint dispatcher here;
-- lowBodyF uses the unchanged actual statement-list length plus one.
attribute [local cbv_opaque] lowCallArgOneL lowCallArgsAuxL withErg lowErg lowEnd
attribute [local cbv_eval] check_argument_bool check_argument_integer
  check_arguments_nil check_arguments_cons
  check_result_select check_return_empty check_return_bool check_end_empty check_end_bool
  floor_name_self floor_mark_self
attribute [local cbv_eval] lowWertE.eq_def lowCmp.eq_def lowEns.eq_def

private abbrev FunctionType (index : Fin unit.fns.length) :=
  EnsTy unit index × RumpTy unit index × ReqTy unit index

private def index0 : Fin unit.fns.length := ⟨0, by change 0 < 6; decide⟩

private def reportIndex : Fin unit.fns.length := ⟨2, by change 2 < 6; decide⟩

private theorem retiring_call_data : CheckCallUnit unit := by
  have headers : unit.fns.all (fun fn =>
      decide (fn.boden = none ∧ fn.leiht = [] ∧ fn.bewegt = [] ∧ fn.praegt = [])) = true := by cbv
  exact ⟨rfl, rfl, rfl, fun fn member =>
    of_decide_eq_true (List.all_eq_true.mp headers fn member)⟩

private theorem retiring_call_ready (caller callee : Fin unit.fns.length)
    (Λ : List (Res (declOf unit))) (takes : (fnAt unit callee).nimmt = []) :
    CheckCallGuards unit caller callee Λ :=
  check_unit_call_ready unit retiring_call_data caller callee Λ takes

-- The original gate/report calls use the same complete checked head as the
-- source fixture. Close its guards before entering the dependent arguments.
private theorem retiring_gate_call (caller : Fin unit.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf unit))) (source : List UArg) :
    lowRufKopf unit caller Γ fn Λ "g" source =
      (lowCallArgsAuxL unit caller Γ fn Λ (fnAt unit index0).kinds
        ((fnAt unit index0).params.map (·.2)) source).map
        (fun arguments => check_call_head unit caller index0 Γ Λ
          (check_arguments_cast unit Γ Λ (params_eq unit index0) arguments)
          (retiring_call_ready caller index0 Λ rfl)) := by
  have found : fnIdx unit.fns "g" = .ok index0 := by cbv
  exact check_call_phase unit caller index0 Γ fn Λ "g" source found
    (retiring_call_ready caller index0 Λ rfl)

private theorem retiring_report_call (caller : Fin unit.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf unit))) (source : List UArg) :
    lowRufKopf unit caller Γ fn Λ "p#report#0" source =
      (lowCallArgsAuxL unit caller Γ fn Λ (fnAt unit reportIndex).kinds
        ((fnAt unit reportIndex).params.map (·.2)) source).map
        (fun arguments => check_call_head unit caller reportIndex Γ Λ
          (check_arguments_cast unit Γ Λ (params_eq unit reportIndex) arguments)
          (retiring_call_ready caller reportIndex Λ rfl)) := by
  have found : fnIdx unit.fns "p#report#0" = .ok reportIndex := by cbv
  exact check_call_phase unit caller reportIndex Γ fn Λ "p#report#0" source found
    (retiring_call_ready caller reportIndex Λ rfl)

attribute [local cbv_opaque] lowRufKopf
attribute [local cbv_eval] retiring_gate_call retiring_report_call

private def function0 : {result : FunctionType index0 //
    lowerFnAt unit index0 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def index1 : Fin unit.fns.length := ⟨1, by change 1 < 6; decide⟩

private def function1 : {result : FunctionType index1 //
    lowerFnAt unit index1 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def index2 : Fin unit.fns.length := ⟨2, by change 2 < 6; decide⟩

private def function2 : {result : FunctionType index2 //
    lowerFnAt unit index2 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def index3 : Fin unit.fns.length := ⟨3, by change 3 < 6; decide⟩

private def function3 : {result : FunctionType index3 //
    lowerFnAt unit index3 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def index4 : Fin unit.fns.length := ⟨4, by change 4 < 6; decide⟩

private def function4 : {result : FunctionType index4 //
    lowerFnAt unit index4 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def index5 : Fin unit.fns.length := ⟨5, by change 5 < 6; decide⟩

private def function5 : {result : FunctionType index5 //
    lowerFnAt unit index5 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

-- Close each dependent function result before constructing the finite selector.
private def functions (index : Fin unit.fns.length) :
    {result : FunctionType index // lowerFnAt unit index = .ok result} :=
  Fin.cases function0
    (Fin.cases function1
      (Fin.cases function2
        (Fin.cases function3
          (Fin.cases function4
            (Fin.cases function5 (fun i => Fin.elim0 i)))))) index

private theorem function_made (index : Fin unit.fns.length) :
    lowerFnAt unit index = .ok (functions index).val := (functions index).property

private theorem each_made :
    lowerEach unit (List.finRange unit.fns.length) = .ok () := by
  change lowerEach unit [index0, index1, index2, index3, index4, index5] = .ok ()
  simp only [lowerEach, function_made]

private theorem invariants_made :
    lowerInvs unit (List.finRange unit.invs.length) = .ok () := by cbv

private theorem contracts_made : contractGate unit = true := by cbv

private def measures : {result : Measures.Export unit // Measures.lowerMeasures unit = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private theorem measures_made (P : Programm (declOf unit)) :
    @Eq (Except String (Programm (declOf unit) × List (declOf unit).Fn))
      (Measures.checkedProgram unit P) (.ok (P, List.finRange unit.fns.length)) := by
  apply check_measure_gate _ measures.val measures.property
  have absent : unit.fns.all (fun fn => decide (fn.decreases = none)) = true := by cbv
  intro fn member
  exact of_decide_eq_true (List.all_eq_true.mp absent fn member)

-- This is the canonical assembler, with all six previously closed function
-- certificates and the unchanged invariant, contract and measure gates.
private def program : {result : Programm (declOf unit) × List (declOf unit).Fn //
    lowerAllg unit = .ok result} :=
  ⟨(progOfFn unit
      (fun f => (functions f).val.1)
      (fun f => (functions f).val.2.1)
      (fun f => (functions f).val.2.2)
      (fun i => lowerInvGut unit i
        (lowerInvs_all_ok unit _ i (List.mem_finRange i) invariants_made))
      (ptrVertragOf unit)
      (fun a => axVertragOf unit a (Bool.and_eq_true_iff.mp contracts_made).2),
      List.finRange unit.fns.length), by
    exact check_assembly unit (fun f => (functions f).val)
      function_made invariants_made each_made contracts_made measures_made⟩

private def checks : {result : List (CheckDecl (declOf unit)) // uCheckDecls unit = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private theorem program_made : lowerAllg unit = .ok program.val := program.property
private theorem checks_made : uCheckDecls unit = .ok checks.val := checks.property

attribute [local cbv_opaque] lowerAllg uCheckDecls
attribute [local cbv_eval] program_made checks_made

private theorem common : CheckWitness unit 1 := by
  constructor <;> cbv

-- These equations retain the actual call and resource transitions, selecting
-- a single reader node before any concrete edited unit is substituted.
set_option maxHeartbeats 400000
private def source_call_ready (u : UProg) (caller callee : Fin u.fns.length)
    (Λ : List (Res (declOf u))) (tables : u.tabs = []) (globals : u.globs = [])
    (locks : u.locks = []) (floor : (fnAt u caller).boden = none)
    (marks : decide (Untermulti (((declOf u).signatur callee).inputMarks.map
      (Res.vonMarke (declOf u))) Λ) = true)
    (owner : ownerReadyB u ((declOf u).signatur callee) = true) :
    CheckCallGuards u caller callee Λ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, marks, owner⟩
  · intro table _
    exact False.elim (Nat.not_lt_zero table.val (by
      simpa only [tables, List.length_nil] using table.isLt))
  · intro global _
    exact False.elim (Nat.not_lt_zero global.val (by
      simpa only [globals, List.length_nil] using global.isLt))
  · intro lock _
    exact False.elim (check_no_lock u locks lock)
  · simp only [floorLeB, floor]
  · intro lock _
    exact False.elim (check_no_lock u locks lock)

-- Eliminate the whole list-indexed result while the list is still a variable.
-- No dependent match over fnAt.params is rewritten after taking its value.
private def empty_parameter_arguments (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (types : List Ty) (empty : types = []) :
    {arguments : Args (declOf u) Γ Λ types //
      lowCallArgsAuxL u caller Γ fn Λ [] types [] = .ok arguments} := by
  subst types
  exact ⟨Args.nil, rfl⟩

private def nullary_arguments (u : UProg) (caller callee : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (kinds : (fnAt u callee).kinds = []) (parameters : (fnAt u callee).params = []) :
    {arguments : Args (declOf u) Γ Λ ((declOf u).params callee) //
      lowCallArgsAuxL u caller Γ fn Λ (fnAt u callee).kinds ((declOf u).params callee) [] = .ok arguments} := by
  let packet := empty_parameter_arguments u caller Γ fn Λ
    ((fnAt u callee).params.map (·.2)) (by simp only [parameters, List.map_nil])
  let recorded := packet.val
  have read : lowCallArgsAuxL u caller Γ fn Λ (fnAt u callee).kinds
      ((fnAt u callee).params.map (·.2)) [] = .ok recorded := by
    rw [kinds]
    exact packet.property
  refine ⟨check_arguments_cast u Γ Λ (params_eq u callee) recorded, ?_⟩
  exact (check_arguments_types u caller Γ fn Λ (fnAt u callee).kinds []
    ((declOf u).params callee) ((fnAt u callee).params.map (·.2)) (params_eq u callee)).trans
      (congrArg (fun answer => answer.map (check_arguments_cast u Γ Λ (params_eq u callee))) read)

private def permitted_head (u : UProg) (caller callee : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u))) (name : String)
    (found : fnIdx u.fns name = .ok callee) (ready : CheckCallGuards u caller callee Λ)
    (arguments : {actual : Args (declOf u) Γ Λ ((declOf u).params callee) //
      lowCallArgsAuxL u caller Γ fn Λ (fnAt u callee).kinds ((declOf u).params callee) [] = .ok actual}) :
    {head : RufKopf u caller Γ Λ // lowRufKopf u caller Γ fn Λ name [] = .ok head} :=
  ⟨check_call_head u caller callee Γ Λ arguments.val ready,
    check_call_success u caller callee Γ fn Λ name [] arguments.val found arguments.property ready⟩

private theorem bind_failure (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (binder name : String)
    (rest : List UStmt) (returning : URet) (error : String)
    (head : {actual : RufKopf u caller Γ Λ // lowRufKopf u caller Γ fn Λ name [] = .ok actual})
    (result : (fnAt u head.val.callee).ergTy = some .bool)
    (failed : lowBodyF u caller (.bool :: Γ) (fn.mitTy binder .bool) fuel
      (nach (declOf u) head.val.callee Λ) rest returning = .error error) :
    lowBodyF u caller Γ fn (fuel + 1) Λ (.bindCall binder name [] :: rest) returning = .error error := by
  rw [lowBodyF]
  simp only [head.property]
  rw [check_result_select, check_result_transport _ _ result]
  simp only [check_result_value, mitRuf_bool, failed]

private theorem empty_return_failure (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (result : (fnAt u caller).ergTy = none)
    (unreturned : decide (Λ.Perm (verOf u caller).ende) = false) :
    lowBodyF u caller Γ fn 1 Λ [] .empty = .error "lower: return without produced marks" := by
  have produced : ∃ value : ErgExpr (declOf u) Γ Λ (verOf u caller).erg,
      lowErg u caller Γ Λ fn .empty = .ok value := by
    rw [check_return_empty]
    split
    · exact ⟨_, rfl⟩
    all_goals simp_all
  obtain ⟨value, made⟩ := produced
  rw [lowBodyF, check_end_empty, made]
  simp only [unreturned, Bool.false_eq_true, dite_false]

-- The unconditional equation of the existing call node avoids the generated
-- catch-all equation's separate nonmatching-constructor proof obligations.
private theorem call_body_equation (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (name : String)
    (rest : List UStmt) (returning : URet) :
    lowBodyF u caller Γ fn (fuel + 1) Λ (.call name [] :: rest) returning =
      (match lowStmtL u caller Γ fn Λ (.call name []) with
      | .error error => .error error
      | .ok ⟨after, statement⟩ =>
        match lowBodyF u caller Γ fn fuel after rest returning with
        | .error error => .error error
        | .ok ending => .ok (Endblock.cons statement ending)) := by
  cases returning <;> rfl

private theorem call_failure (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (name error : String)
    (rest : List UStmt) (returning : URet)
    (failed : lowRufKopf u caller Γ fn Λ name [] = .error error) :
    lowBodyF u caller Γ fn (fuel + 1) Λ (.call name [] :: rest) returning = .error error := by
  rw [call_body_equation]
  simp only [lowStmtL, lowCallL, failed]

private theorem after_call_failure (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (name error : String)
    (rest : List UStmt) (returning : URet)
    (step : {actual : Σ after, Stmt (declOf u) (verOf u caller) false Γ Λ after //
      lowStmtL u caller Γ fn Λ (.call name []) = .ok actual})
    (failed : lowBodyF u caller Γ fn fuel step.val.1 rest returning = .error error) :
    lowBodyF u caller Γ fn (fuel + 1) Λ (.call name [] :: rest) returning = .error error := by
  obtain ⟨⟨after, statement⟩, made⟩ := step
  rw [call_body_equation]
  simp only [made, failed]

-- The first invocation's checked writes/floor remain identical. With no locks,
-- the two remaining lock guards hold also at the actual post-consumer inventory.
-- The marks test is still the canonical first failing guard, before ownerReadyB.
private theorem missing_mark_failure (u : UProg) (caller callee : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (before after : List (Res (declOf u))) (name : String)
    (locks : u.locks = []) (ready : CheckCallGuards u caller callee before)
    (found : fnIdx u.fns name = .ok callee)
    (arguments : {actual : Args (declOf u) Γ after ((declOf u).params callee) //
      lowCallArgsAuxL u caller Γ fn after (fnAt u callee).kinds ((declOf u).params callee) [] = .ok actual})
    (missing : decide (Untermulti (((declOf u).signatur callee).inputMarks.map
      (Res.vonMarke (declOf u))) after) = false) :
    lowRufKopf u caller Γ fn after name [] = .error "call without held mark" := by
  have held : ∀ L ∈ ((declOf u).signatur callee).haelt, Res.held (D := declOf u) L ∈ after :=
    fun L _ => False.elim (check_no_lock u locks L)
  have extra : ∀ L ∈ heldLocksD u after,
      L ∈ ((declOf u).signatur callee).haelt ∨ floorUeberB u callee L = true :=
    fun L _ => False.elim (check_no_lock u locks L)
  simp only [lowRufKopf, found, arguments.property, dif_pos ready.writes,
    dif_pos ready.globals, dif_pos held, dif_pos ready.floor, dif_pos extra,
    missing, Bool.false_eq_true, dite_false]

end RetiringWitness
end Gabbro.Grammatik.Parser.Uebersetze
