module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Units
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Calls
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Assembly
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

private abbrev unit : UProg := selected.val

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

end RetiringWitness

end Gabbro.Grammatik.Parser.Uebersetze

namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

local instance retiringFactsAxiomEquality (u : UProg) : DecidableEq (declOf u).Ax :=
  inferInstanceAs (DecidableEq (Fin u.axs.length))
local instance retiringFactsFunctionEquality (u : UProg) : DecidableEq (declOf u).Fn :=
  inferInstanceAs (DecidableEq (Fin u.fns.length))

namespace RetiringWitness

-- This proposition contains the original getter-facing statements, together
-- with the actual header/index facts needed by their typed consumers. It is
-- transported as a whole; none of its computational packets is public data.
private structure RetiringFacts (u : UProg) : Prop where
  common : CheckWitness u 1
  functionCount : u.fns.length = 6
  checkCount : ((uCheckDecls u).toOption.get common.derived).length = 1
  driverEnd : ∀ f : (declOf u).Fn, f.val = 5 → (vertragVon (declOf u) f).ende = []
  resources : ∀ c ∈ (uCheckDecls u).toOption.get common.derived,
    ∀ producer consumer : (declOf u).Fn, producer.val = 1 → consumer.val = 4 →
      ((declOf u).signatur producer).inputMarks = [c.duty] ∧
      ((declOf u).signatur producer).outputMarks = [c.duty] ∧
      ((declOf u).signatur consumer).inputMarks = [c.duty] ∧
      ((declOf u).signatur consumer).outputMarks = []
  descriptor : ∀ c ∈ (uCheckDecls u).toOption.get common.derived,
    c.name = "p" ∧ c.probe.val = 1 ∧ c.gates.map Fin.val = [3]
  boolResult : ∀ f : (declOf u).Fn, f.val = 1 ∨ f.val = 2 →
    (declOf u).erg f = some .bool
  capture : ∀ (f : (declOf u).Fn), f.val = 2 →
    ∀ (env : Env (declOf u) ((declOf u).params f))
      (truth : (declOf u).erg f = some .bool),
      checkEnvAtoms env = [some (.number 3), some (.truth true), some (.truth true)] →
      actualCheckReturn u f env (Eq.mpr (congrArg (ErgVal (declOf u)) truth) true) =
        some ("p", retiringReport)
  verdict : ∀ c ∈ (uCheckDecls u).toOption.get common.derived,
    ∀ (f : (declOf u).Fn), f.val = 1 →
      ∀ (env : Env (declOf u) ((declOf u).params f))
        (truth : (declOf u).erg f = some .bool) (before after : World (declOf u)),
        rueckUrteil c (.rueck f env
          (Eq.mpr (congrArg (ErgVal (declOf u)) truth) true) before after) = some true
  unconsumed : (lowerAllg {u with fns := u.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      {f with body := [.bindCall "verdict" "p#probe" []]} else f}).toOption.isNone = true
  double : (lowerAllg {u with fns := u.fns.map fun f =>
    if strEq f.name "p#driver#g" then
      {f with body := f.body ++ [.call "p#consume#g" []]} else f}).toOption.isNone = true

private theorem actual_checks : (uCheckDecls unit).toOption.get common.derived = checks.val :=
  Except.ok.inj ((except_ok_get (x := uCheckDecls unit) common.derived).symm.trans checks_made)

private theorem single_check : checks.val = [checks.val.get ⟨0, by change 0 < 1; decide⟩] := rfl

private theorem check_member {c : CheckDecl (declOf unit)}
    (member : c ∈ (uCheckDecls unit).toOption.get common.derived) :
    c = checks.val.get ⟨0, by change 0 < 1; decide⟩ := by
  rw [actual_checks, single_check] at member
  exact List.mem_singleton.mp member

private theorem check_descriptor : ∀ c ∈ (uCheckDecls unit).toOption.get common.derived,
    c.name = "p" ∧ c.probe.val = 1 ∧ c.gates.map Fin.val = [3] := by
  intro c member
  obtain rfl := check_member member
  cbv

private theorem check_resources : ∀ c ∈ (uCheckDecls unit).toOption.get common.derived,
    ∀ producer consumer : (declOf unit).Fn, producer.val = 1 → consumer.val = 4 →
      ((declOf unit).signatur producer).inputMarks = [c.duty] ∧
      ((declOf unit).signatur producer).outputMarks = [c.duty] ∧
      ((declOf unit).signatur consumer).inputMarks = [c.duty] ∧
      ((declOf unit).signatur consumer).outputMarks = [] := by
  intro c member producer consumer producerAt consumerAt
  have producerEq : producer = index1 := Fin.ext producerAt
  have consumerEq : consumer = index4 := Fin.ext consumerAt
  subst producer
  subst consumer
  obtain rfl := check_member member
  cbv

-- Read the actual saved reporter metadata once, without spelling another
-- return-site schema or assuming a completed source/IR outcome.
private def reporterSite : {site : UCheckReturn //
    (fnAt unit index2).checkReturn = some site} := by
  refine ⟨?site, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private theorem check_capture : ∀ (f : (declOf unit).Fn), f.val = 2 →
    ∀ (env : Env (declOf unit) ((declOf unit).params f))
      (truth : (declOf unit).erg f = some .bool),
      checkEnvAtoms env = [some (.number 3), some (.truth true), some (.truth true)] →
      actualCheckReturn unit f env (Eq.mpr (congrArg (ErgVal (declOf unit)) truth) true) =
        some ("p", retiringReport) := by
  intro f position env truth atoms
  have same : f = index2 := Fin.ext position
  subst f
  unfold actualCheckReturn
  rw [reporterSite.property]
  change (do
    let report ← decodeCheckReturn reporterSite.val (checkEnvAtoms env) true
    pure ("p", report)) = some ("p", retiringReport)
  rw [atoms]
  cbv

private theorem check_verdict : ∀ c ∈ (uCheckDecls unit).toOption.get common.derived,
    ∀ (f : (declOf unit).Fn), f.val = 1 →
      ∀ (env : Env (declOf unit) ((declOf unit).params f))
        (truth : (declOf unit).erg f = some .bool) (before after : World (declOf unit)),
        rueckUrteil c (.rueck f env
          (Eq.mpr (congrArg (ErgVal (declOf unit)) truth) true) before after) = some true := by
  intro c member f position env truth before after
  have same : f = index1 := Fin.ext position
  subst f
  have probe : c.probe = index1 := Fin.ext (check_descriptor c member).2.1
  unfold rueckUrteil
  change (if index1 = c.probe then some true else none) = some true
  exact if_pos probe.symm

-- Every resource-refusal witness is an actual failed function of the same
-- assembler. This implication neither bypasses nor duplicates that assembler.
private theorem function_refused (u : UProg) (f : Fin u.fns.length)
    (error : String) (rejected : lowerFnAt u f = .error error) :
    (lowerAllg u).toOption.isNone = true := by
  cases made : lowerAllg u with
  | error error => rfl
  | ok result =>
    obtain ⟨fields, produced, _, _, _⟩ := lowerAllg_fields u result.1 result.2 made f
    rw [rejected] at produced
    cases produced

attribute [local cbv_opaque] lowCallArgOneL lowCallArgsAuxL withErg lowErg lowEnd
attribute [local cbv_eval] check_argument_bool check_argument_integer
  check_arguments_nil check_arguments_cons
  check_result_select check_return_empty check_return_bool check_end_empty check_end_bool
  floor_name_self floor_mark_self

private theorem selected_unconsumed :
    (lowerAllg {unit with fns := unit.fns.map fun f =>
      if strEq f.name "p#driver#g" then
        {f with body := [.bindCall "verdict" "p#probe" []]} else f}).toOption.isNone = true := by
  have failed : ∃ error : String,
      lowerFnAt {unit with fns := unit.fns.map fun f =>
        if strEq f.name "p#driver#g" then
          {f with body := [.bindCall "verdict" "p#probe" []]} else f}
        ⟨5, by change 5 < 6; decide⟩ = .error error := by
    refine ⟨?error, ?rejected⟩
    case rejected => cbv <;> exact Eq.refl _
  obtain ⟨error, rejected⟩ := failed
  exact function_refused _ _ error rejected

private theorem selected_double :
    (lowerAllg {unit with fns := unit.fns.map fun f =>
      if strEq f.name "p#driver#g" then
        {f with body := f.body ++ [.call "p#consume#g" []]} else f}).toOption.isNone = true := by
  have failed : ∃ error : String,
      lowerFnAt {unit with fns := unit.fns.map fun f =>
        if strEq f.name "p#driver#g" then
          {f with body := f.body ++ [.call "p#consume#g" []]} else f}
        ⟨5, by change 5 < 6; decide⟩ = .error error := by
    refine ⟨?error, ?rejected⟩
    case rejected => cbv <;> exact Eq.refl _
  obtain ⟨error, rejected⟩ := failed
  exact function_refused _ _ error rejected

private theorem facts : RetiringFacts unit := by
  refine ⟨common, rfl, ?_, ?_, check_resources, check_descriptor, ?_,
    check_capture, check_verdict, selected_unconsumed, selected_double⟩
  · rw [actual_checks]
    rfl
  · intro f position
    have same : f = index5 := Fin.ext position
    subst f
    rfl
  · have all : (List.finRange unit.fns.length).all (fun f =>
        decide ((f.val = 1 ∨ f.val = 2) → (declOf unit).erg f = some .bool)) = true := by cbv
    intro f position
    exact of_decide_eq_true (List.all_eq_true.mp all f (List.mem_finRange f)) position

end RetiringWitness
end Gabbro.Grammatik.Parser.Uebersetze
