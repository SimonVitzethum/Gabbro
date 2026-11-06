module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.ZeugenPhases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.ZeugenPhases
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Units
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Calls
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Heads
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


import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults

public section

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
  unconsumed : (lowerAllg {u with
    fns := u.fns.map fun f =>
      if strEq f.name "p#driver#g" then
        {f with body := [.bindCall "verdict" "p#probe" []]} else f}).toOption.isNone = true
  double : (lowerAllg {u with
    fns := u.fns.map fun f =>
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
  exact ⟨rfl, rfl, rfl, rfl⟩

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
  simp only [rueckUrteil, if_pos probe.symm]
  cbv

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

private def unconsumedUnit : {actual : UProg // {unit with
      fns := unit.fns.map fun f =>
        if strEq f.name "p#driver#g" then
          {f with body := [.bindCall "verdict" "p#probe" []]} else f} = actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def doubledUnit : {actual : UProg // {unit with
      fns := unit.fns.map fun f =>
        if strEq f.name "p#driver#g" then
          {f with body := f.body ++ [.call "p#consume#g" []]} else f} = actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def unconsumedDriver : Fin unconsumedUnit.val.fns.length := ⟨5, by change 5 < 6; decide⟩
private def unconsumedProducer : Fin unconsumedUnit.val.fns.length := ⟨1, by change 1 < 6; decide⟩
private abbrev unconsumedCtx := ctxOf unconsumedUnit.val unconsumedDriver
private abbrev unconsumedFn := fnAt unconsumedUnit.val unconsumedDriver
private abbrev unconsumedPermit := resOf unconsumedUnit.val unconsumedDriver
private theorem unconsumed_header : PlainFunctionHeader unconsumedUnit.val unconsumedDriver := by constructor <;> cbv
private theorem unconsumed_producer_found : fnIdx unconsumedUnit.val.fns "p#probe" = .ok unconsumedProducer := by cbv
private theorem unconsumed_producer_ready : CheckCallGuards unconsumedUnit.val unconsumedDriver unconsumedProducer unconsumedPermit :=
  source_call_ready unconsumedUnit.val unconsumedDriver unconsumedProducer unconsumedPermit
    (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
private def unconsumedArguments := nullary_arguments unconsumedUnit.val unconsumedDriver unconsumedProducer
  unconsumedCtx unconsumedFn unconsumedPermit (by cbv) (by cbv)
private def unconsumedHead := permitted_head unconsumedUnit.val unconsumedDriver unconsumedProducer
  unconsumedCtx unconsumedFn unconsumedPermit "p#probe" unconsumed_producer_found unconsumed_producer_ready unconsumedArguments
private theorem unconsumed_producer_result : (fnAt unconsumedUnit.val unconsumedHead.val.callee).ergTy = some .bool := by cbv
private abbrev unconsumedAfter := nach (declOf unconsumedUnit.val) unconsumedHead.val.callee unconsumedPermit
private abbrev unconsumedBoundFn := unconsumedFn.mitTy "verdict" .bool

private def doubleDriver : Fin doubledUnit.val.fns.length := ⟨5, by change 5 < 6; decide⟩
private def doubleProducer : Fin doubledUnit.val.fns.length := ⟨1, by change 1 < 6; decide⟩
private abbrev doubleCtx := ctxOf doubledUnit.val doubleDriver
private abbrev doubleFn := fnAt doubledUnit.val doubleDriver
private abbrev doublePermit := resOf doubledUnit.val doubleDriver
private theorem double_header : PlainFunctionHeader doubledUnit.val doubleDriver := by constructor <;> cbv
private theorem double_producer_found : fnIdx doubledUnit.val.fns "p#probe" = .ok doubleProducer := by cbv
private theorem double_producer_ready : CheckCallGuards doubledUnit.val doubleDriver doubleProducer doublePermit :=
  source_call_ready doubledUnit.val doubleDriver doubleProducer doublePermit
    (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
private def doubleArguments := nullary_arguments doubledUnit.val doubleDriver doubleProducer
  doubleCtx doubleFn doublePermit (by cbv) (by cbv)
private def doubleHead := permitted_head doubledUnit.val doubleDriver doubleProducer
  doubleCtx doubleFn doublePermit "p#probe" double_producer_found double_producer_ready doubleArguments
private theorem double_producer_result : (fnAt doubledUnit.val doubleHead.val.callee).ergTy = some .bool := by cbv
private abbrev doubleAfter := nach (declOf doubledUnit.val) doubleHead.val.callee doublePermit
private abbrev doubleBoundFn := doubleFn.mitTy "verdict" .bool

private theorem unconsumed_shape : unconsumedFn.body = [.bindCall "verdict" "p#probe" []] ∧
    unconsumedFn.ret = .empty := by cbv
private theorem unconsumed_result : (fnAt unconsumedUnit.val unconsumedDriver).ergTy = none := by cbv
private theorem unconsumed_return_unready :
    decide (unconsumedAfter.Perm (verOf unconsumedUnit.val unconsumedDriver).ende) = false := by cbv
private theorem unconsumed_end :
    lowBodyF unconsumedUnit.val unconsumedDriver (.bool :: unconsumedCtx) unconsumedBoundFn
      1 unconsumedAfter [] .empty = .error "lower: return without produced marks" :=
  empty_return_failure unconsumedUnit.val unconsumedDriver (.bool :: unconsumedCtx)
    unconsumedBoundFn unconsumedAfter unconsumed_result unconsumed_return_unready
private theorem unconsumed_body :
    lowBody unconsumedUnit.val unconsumedDriver unconsumedFn.body unconsumedFn.ret =
      .error "lower: return without produced marks" := by
  have failed := bind_failure unconsumedUnit.val unconsumedDriver unconsumedCtx unconsumedFn 1
    unconsumedPermit "verdict" "p#probe" [] .empty "lower: return without produced marks"
    unconsumedHead unconsumed_producer_result unconsumed_end
  simpa only [lowBody, unconsumed_shape.1, unconsumed_shape.2, List.length_cons, List.length_nil] using failed
private theorem unconsumed_function : lowerFnAt unconsumedUnit.val unconsumedDriver =
    .error "lower: return without produced marks" :=
  lowerFnAt_error_from_body unconsumed_header unconsumed_body

private def doubleConsumer : Fin doubledUnit.val.fns.length := ⟨4, by change 4 < 6; decide⟩
private theorem double_shape : doubleFn.body =
    [.bindCall "verdict" "p#probe" [], .call "p#consume#g" [], .call "p#consume#g" []] ∧
    doubleFn.ret = .empty := by cbv
private theorem double_consumer_found : fnIdx doubledUnit.val.fns "p#consume#g" = .ok doubleConsumer := by cbv
private theorem double_consumer_ready : CheckCallGuards doubledUnit.val doubleDriver doubleConsumer doubleAfter :=
  source_call_ready doubledUnit.val doubleDriver doubleConsumer doubleAfter
    (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
private def doubleConsumerArguments := nullary_arguments doubledUnit.val doubleDriver doubleConsumer
  (.bool :: doubleCtx) doubleBoundFn doubleAfter (by cbv) (by cbv)
private def doubleConsumerHead := permitted_head doubledUnit.val doubleDriver doubleConsumer
  (.bool :: doubleCtx) doubleBoundFn doubleAfter "p#consume#g"
  double_consumer_found double_consumer_ready doubleConsumerArguments
private theorem double_consumer_reason : (declOf doubledUnit.val).gruende doubleConsumerHead.val.callee = 0 := by cbv

-- The first consumer is the already checked body with its actual retireMark.
-- Its call transformer, not a guessed empty list, determines the second call's resources.
private def doubleConsumerStep : {step : Σ after, Stmt (declOf doubledUnit.val)
      (verOf doubledUnit.val doubleDriver) false (.bool :: doubleCtx) doubleAfter after //
    lowStmtL doubledUnit.val doubleDriver (.bool :: doubleCtx) doubleBoundFn doubleAfter
      (.call "p#consume#g" []) = .ok step} := by
  refine ⟨⟨nach (declOf doubledUnit.val) doubleConsumerHead.val.callee doubleAfter,
    Stmt.call (D := declOf doubledUnit.val) doubleConsumerHead.val.callee doubleConsumerHead.val.args doubleConsumerHead.val.hp
      double_consumer_reason⟩, ?_⟩
  simp only [lowStmtL, lowCallL, doubleConsumerHead.property, dif_pos double_consumer_reason]
private def doubleAgainArguments := nullary_arguments doubledUnit.val doubleDriver doubleConsumer
  (.bool :: doubleCtx) doubleBoundFn doubleConsumerStep.val.1 (by cbv) (by cbv)
private theorem double_locks_empty : doubledUnit.val.locks = [] := by cbv
private theorem double_missing_mark :
    decide (Untermulti (((declOf doubledUnit.val).signatur doubleConsumer).inputMarks.map
      (Res.vonMarke (declOf doubledUnit.val))) doubleConsumerStep.val.1) = false := by cbv
private theorem double_again_rejected :
    lowRufKopf doubledUnit.val doubleDriver (.bool :: doubleCtx) doubleBoundFn doubleConsumerStep.val.1
      "p#consume#g" [] = .error "call without held mark" :=
  missing_mark_failure doubledUnit.val doubleDriver doubleConsumer (.bool :: doubleCtx) doubleBoundFn
    doubleAfter doubleConsumerStep.val.1 "p#consume#g" double_locks_empty double_consumer_ready
    double_consumer_found doubleAgainArguments double_missing_mark
private theorem double_tail :
    lowBodyF doubledUnit.val doubleDriver (.bool :: doubleCtx) doubleBoundFn 2 doubleConsumerStep.val.1
      [.call "p#consume#g" []] .empty = .error "call without held mark" :=
  call_failure doubledUnit.val doubleDriver (.bool :: doubleCtx) doubleBoundFn 1 doubleConsumerStep.val.1
    "p#consume#g" "call without held mark" [] .empty double_again_rejected
private theorem double_consumer_prefix :
    lowBodyF doubledUnit.val doubleDriver (.bool :: doubleCtx) doubleBoundFn 3 doubleAfter
      [.call "p#consume#g" [], .call "p#consume#g" []] .empty = .error "call without held mark" :=
  after_call_failure doubledUnit.val doubleDriver (.bool :: doubleCtx) doubleBoundFn 2 doubleAfter
    "p#consume#g" "call without held mark" [.call "p#consume#g" []] .empty doubleConsumerStep double_tail
private theorem double_body :
    lowBody doubledUnit.val doubleDriver doubleFn.body doubleFn.ret = .error "call without held mark" := by
  have failed := bind_failure doubledUnit.val doubleDriver doubleCtx doubleFn 3 doublePermit
    "verdict" "p#probe" [.call "p#consume#g" [], .call "p#consume#g" []] .empty "call without held mark"
    doubleHead double_producer_result double_consumer_prefix
  simpa only [lowBody, double_shape.1, double_shape.2, List.length_cons, List.length_nil] using failed
private theorem double_function : lowerFnAt doubledUnit.val doubleDriver = .error "call without held mark" :=
  lowerFnAt_error_from_body double_header double_body

private theorem selected_unconsumed :
    (lowerAllg {unit with
      fns := unit.fns.map fun f =>
        if strEq f.name "p#driver#g" then
          {f with body := [.bindCall "verdict" "p#probe" []]} else f}).toOption.isNone = true := by
  rw [unconsumedUnit.property]
  exact function_refused _ _ "lower: return without produced marks" unconsumed_function

private theorem selected_double :
    (lowerAllg {unit with
      fns := unit.fns.map fun f =>
        if strEq f.name "p#driver#g" then
          {f with body := f.body ++ [.call "p#consume#g" []]} else f}).toOption.isNone = true := by
  rw [doubledUnit.property]
  exact function_refused _ _ "call without held mark" double_function

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
