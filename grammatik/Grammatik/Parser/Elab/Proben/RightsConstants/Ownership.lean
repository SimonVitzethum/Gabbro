module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Phases
import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
import all Grammatik.Parser.Elab.Proben.RightsConstants.OwnershipSteps
import all Grammatik.Kern.Syntax.Typen.Shape
import all Grammatik.Parser.Elab.Uebersetze.Kontext.Eigner
import all Grammatik.Parser.Elab.Generic.SignatureData
import all Grammatik.Parser.Elab.Generic.C09Flows
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg.TableCapabilities
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg2.CallArguments
import all Grammatik.Parser.Elab.UebersetzeAllg2.Marken
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Returns
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
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
namespace Gabbro.Grammatik.Parser.UebersetzeProben11
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben (stufe)
open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
set_option maxRecDepth 100000

-- Preserve the original logarithm equation and select only the used canonical fuel operations.
attribute [local cbv_eval] Nat.log2_def
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL uFloatLimit
attribute [local cbv_eval] UebersetzeProben2.seq_select UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

-- Evaluate the selected node of the canonical typed mutual before projecting
-- its result, as in the generic count-reader witnesses.
attribute [local cbv_eval] lowWertE.eq_def lowCmp.eq_def lowEns.eq_def
  lowArrayValue.eq_def lowSeiteZ.eq_def

-- Each declaration retains data inferred solely from one actual phase equation.
-- Later function certificates therefore read the unit rather than replaying Elab.
scoped macro "ownership_phase " name:ident " from " supplied:term : command => do
  let items := Lean.mkIdentFrom name (name.getId.appendAfter "_items")
  let unit := Lean.mkIdentFrom name (name.getId.appendAfter "_unit")
  let parsed : Lean.TSyntax `command ← `(command|
    private def $items : { actual : List SItemTief //
        parseTopTief ($supplied).tokens = .ok actual } := by
      refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let elaborated : Lean.TSyntax `command ← `(command|
    private def $unit : { actual : UProg //
        elabU (pre108 ($items).val) = .ok actual } := by
      refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  return ⟨Lean.mkNullNode #[parsed, elaborated]⟩

-- Fix the complete typed result before inspecting its success/refusal tag.
scoped macro "ownership_function " name:ident " for " unit:ident " at " number:num " with_body " supplied:term : command => do
  let index := Lean.mkIdentFrom name (name.getId.appendAfter "_index")
  let header := Lean.mkIdentFrom name (name.getId.appendAfter "_header")
  let body := Lean.mkIdentFrom name (name.getId.appendAfter "_body")
  let ordinal : Lean.TSyntax `term := ⟨number.raw⟩
  let member : Lean.TSyntax `command ← `(command|
    private def $index : Fin ($unit).val.fns.length := ⟨$ordinal, by decide +kernel⟩)
  let gates : Lean.TSyntax `command ← `(command|
    private theorem $header : PlainFunctionHeader ($unit).val $index := by constructor <;> cbv)
  let lowered : Lean.TSyntax `command ← `(command|
    private def $body : { actual : PlainFunctionBody ($unit).val $index //
        lowBody ($unit).val $index (fnAt ($unit).val $index).body
          (fnAt ($unit).val $index).ret = .ok actual } := by
      exact $supplied)
  let result : Lean.TSyntax `command ← `(command|
    private def $name : { actual :
        EnsTy ($unit).val $index × RumpTy ($unit).val $index × ReqTy ($unit).val $index //
        lowerFnAt ($unit).val $index = .ok actual } := lowerFnAt_from_body $header $body)
  return ⟨Lean.mkNullNode #[member, gates, lowered, result]⟩

scoped macro "ownership_refusal " name:ident " for " unit:ident " at " number:num
    " with_reason " error:term " with_body " supplied:term : command => do
  let index := Lean.mkIdentFrom name (name.getId.appendAfter "_index")
  let header := Lean.mkIdentFrom name (name.getId.appendAfter "_header")
  let body := Lean.mkIdentFrom name (name.getId.appendAfter "_body")
  let ordinal : Lean.TSyntax `term := ⟨number.raw⟩
  let member : Lean.TSyntax `command ← `(command|
    private def $index : Fin ($unit).val.fns.length := ⟨$ordinal, by decide +kernel⟩)
  let gates : Lean.TSyntax `command ← `(command|
    private theorem $header : PlainFunctionHeader ($unit).val $index := by constructor <;> cbv)
  let refused : Lean.TSyntax `command ← `(command|
    private theorem $body : lowBody ($unit).val $index (fnAt ($unit).val $index).body
        (fnAt ($unit).val $index).ret = .error $error := $supplied)
  let result : Lean.TSyntax `command ← `(command|
    private theorem $name : lowerFnAt ($unit).val $index = .error $error :=
      lowerFnAt_error_from_body $header $body)
  return ⟨Lean.mkNullNode #[member, gates, refused, result]⟩

open scoped Gabbro.Grammatik.Parser.UebersetzeProben11

scoped macro "ownership_retire_step " name:ident " for " unit:ident " at " index:ident
    " named " text:term : command => do
  let mark := Lean.mkIdentFrom name (name.getId.appendAfter "_mark")
  let entry := Lean.mkIdentFrom name (name.getId.appendAfter "_entry")
  let stage := Lean.mkIdentFrom name (name.getId.appendAfter "_stage")
  let loan := Lean.mkIdentFrom name (name.getId.appendAfter "_loan")
  let held := Lean.mkIdentFrom name (name.getId.appendAfter "_held")
  let remaining := Lean.mkIdentFrom name (name.getId.appendAfter "_remaining")
  let a ← `(command| private def $mark : { actual : Fin ($unit).val.marken.length //
      markFin ($unit).val.marken $text = some actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let b ← `(command| private def $entry : { actual : List (Res (declOf ($unit).val)) //
      resOf ($unit).val $index = actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| private def $stage : { actual : Nat //
      heldMarkStage (D := declOf ($unit).val) ($mark).val ($entry).val = some actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let d ← `(command| private theorem $loan :
      (fnAt ($unit).val $index).leiht.any (strEq · $text) = false := by cbv)
  let e ← `(command| private theorem $held :
      heldMarkStage (D := declOf ($unit).val) ($mark).val (resOf ($unit).val $index) = some ($stage).val :=
    (congrArg (heldMarkStage (D := declOf ($unit).val) ($mark).val) ($entry).property).trans ($stage).property)
  let f ← `(command| private def $name : { actual : BodyStep ($unit).val $index (resOf ($unit).val $index) //
      lowStmtL (l := false) ($unit).val $index (ctxOf ($unit).val $index) (fnAt ($unit).val $index)
        (resOf ($unit).val $index) (.retires $text) = .ok actual } :=
    retire_step ($unit).val $index $text ($mark).val ($stage).val $loan ($mark).property $held)
  let g ← `(command| private theorem $remaining : ($name).val.1 =
      ($entry).val.erase (.marke ($mark).val ($stage).val) :=
    congrArg (fun resources : List (Res (declOf ($unit).val)) => resources.erase (.marke ($mark).val ($stage).val)) ($entry).property)
  return ⟨Lean.mkNullNode #[a, b, c, d, e, f, g]⟩

scoped macro "ownership_call_step " name:ident " for " unit:ident " at " index:ident
    " named " text:term " arguments " raw:term : command => do
  let callee := Lean.mkIdentFrom name (name.getId.appendAfter "_callee")
  let args := Lean.mkIdentFrom name (name.getId.appendAfter "_arguments")
  let writes := Lean.mkIdentFrom name (name.getId.appendAfter "_writes")
  let globals := Lean.mkIdentFrom name (name.getId.appendAfter "_globals")
  let held := Lean.mkIdentFrom name (name.getId.appendAfter "_held")
  let floor := Lean.mkIdentFrom name (name.getId.appendAfter "_floor")
  let extra := Lean.mkIdentFrom name (name.getId.appendAfter "_extra")
  let inventory := Lean.mkIdentFrom name (name.getId.appendAfter "_inputs")
  let owners := Lean.mkIdentFrom name (name.getId.appendAfter "_owners")
  let head := Lean.mkIdentFrom name (name.getId.appendAfter "_head")
  let reason := Lean.mkIdentFrom name (name.getId.appendAfter "_reason")
  let after := Lean.mkIdentFrom name (name.getId.appendAfter "_after")
  let remaining := Lean.mkIdentFrom name (name.getId.appendAfter "_remaining")
  let a ← `(command| private def $callee : { actual : Fin ($unit).val.fns.length //
      fnIdx ($unit).val.fns $text = .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let b ← `(command| private def $args : { actual : Args (declOf ($unit).val) (ctxOf ($unit).val $index)
      (resOf ($unit).val $index) ((declOf ($unit).val).params ($callee).val) //
      lowCallArgsAuxL ($unit).val $index (ctxOf ($unit).val $index) (fnAt ($unit).val $index)
        (resOf ($unit).val $index) (fnAt ($unit).val ($callee).val).kinds
          ((declOf ($unit).val).params ($callee).val) $raw = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| private theorem $writes : ∀ t : Fin ($unit).val.tabs.length,
      writesAt ($unit).val (fnAt ($unit).val ($callee).val) t = true →
        writesAt ($unit).val (fnAt ($unit).val $index) t = true := by decide +kernel)
  let d ← `(command| private theorem $globals : ∀ g : Fin ($unit).val.globs.length,
      writesGAt ($unit).val (fnAt ($unit).val ($callee).val) g = true →
        writesGAt ($unit).val (fnAt ($unit).val $index) g = true := by decide +kernel)
  let e ← `(command| private theorem $held : ∀ L ∈ ((declOf ($unit).val).signatur ($callee).val).haelt,
      Res.held (D := declOf ($unit).val) L ∈ resOf ($unit).val $index := by decide +kernel)
  let f ← `(command| private theorem $floor : floorLeB ($unit).val $index ($callee).val = true := by cbv)
  let g ← `(command| private theorem $extra : ∀ L ∈ heldLocksD ($unit).val (resOf ($unit).val $index),
      L ∈ ((declOf ($unit).val).signatur ($callee).val).haelt ∨
        floorUeberB ($unit).val ($callee).val L = true := by decide +kernel)
  let h ← `(command| private theorem $inventory : decide (Untermulti
      (((declOf ($unit).val).signatur ($callee).val).inputMarks.map (Res.vonMarke (declOf ($unit).val)))
        (resOf ($unit).val $index)) = true := by decide +kernel)
  let i ← `(command| private theorem $owners :
      ownerReadyB ($unit).val ((declOf ($unit).val).signatur ($callee).val) = true := by cbv)
  let j ← `(command| private def $head : { actual : RufKopf ($unit).val $index
      (ctxOf ($unit).val $index) (resOf ($unit).val $index) //
      lowRufKopf ($unit).val $index (ctxOf ($unit).val $index) (fnAt ($unit).val $index)
        (resOf ($unit).val $index) $text $raw = .ok actual } :=
    call_head ($unit).val $index ($callee).val $text $raw ($callee).property $args
      ⟨$writes, $globals, $held, $floor, $extra, $inventory, $owners⟩)
  let k ← `(command| private theorem $reason : (declOf ($unit).val).gruende ($head).val.callee = 0 := by cbv)
  let l ← `(command| private def $name : { actual : BodyStep ($unit).val $index (resOf ($unit).val $index) //
      lowStmtL (l := false) ($unit).val $index (ctxOf ($unit).val $index) (fnAt ($unit).val $index)
        (resOf ($unit).val $index) (.call $text $raw) = .ok actual } :=
    call_step ($unit).val $index $text $raw $head $reason)
  let m ← `(command| private def $after : { actual : List (Res (declOf ($unit).val)) //
      nach (declOf ($unit).val) ($head).val.callee (resOf ($unit).val $index) = actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let n ← `(command| private theorem $remaining : ($name).val.1 = ($after).val := ($after).property)
  return ⟨Lean.mkNullNode #[a, b, c, d, e, f, g, h, i, j, k, l, m, n]⟩

-- The source shape is inferred from the actual unit, not supplied as an AST.
scoped macro "ownership_call_body " name:ident " for " unit:ident " at " number:num : command => do
  let index := Lean.mkIdentFrom name (name.getId.appendAfter "_index")
  let shape := Lean.mkIdentFrom name (name.getId.appendAfter "_shape")
  let step := Lean.mkIdentFrom name (name.getId.appendAfter "_step")
  let ending := Lean.mkIdentFrom name (name.getId.appendAfter "_end")
  let ordinal : Lean.TSyntax `term := ⟨number.raw⟩
  let a ← `(command| private def $index : Fin ($unit).val.fns.length := ⟨$ordinal, by decide +kernel⟩)
  let b ← `(command| private def $shape : { actual : String × List UArg //
      (fnAt ($unit).val $index).body = [.call actual.1 actual.2] } := by
    refine ⟨(?_, ?_), by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| ownership_call_step $step for $unit at $index
    named ($shape).val.1 arguments ($shape).val.2)
  let d ← `(command| private def $ending : { actual : Endblock (declOf ($unit).val)
      (verOf ($unit).val $index) false (ctxOf ($unit).val $index) ($step).val.1 //
      lowEnd ($unit).val $index (ctxOf ($unit).val $index) ($step).val.1 (fnAt ($unit).val $index)
        (fnAt ($unit).val $index).ret = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let e ← `(command| private def $name : { actual : PlainFunctionBody ($unit).val $index //
      lowBody ($unit).val $index (fnAt ($unit).val $index).body (fnAt ($unit).val $index).ret = .ok actual } := by
    refine ⟨Endblock.cons ($step).val.2 ($ending).val, ?_⟩
    exact (call_body _ _ _ _ ($shape).property ($step).val ($step).property).trans
      ((congrArg (fun answer => answer.map (Endblock.cons ($step).val.2)) ($ending).property).trans (by rfl)))
  return ⟨Lean.mkNullNode #[a, b, c, d, e]⟩

scoped macro "ownership_retire_body " name:ident " for " unit:ident " at " number:num : command => do
  let index := Lean.mkIdentFrom name (name.getId.appendAfter "_index")
  let shape := Lean.mkIdentFrom name (name.getId.appendAfter "_shape")
  let step := Lean.mkIdentFrom name (name.getId.appendAfter "_step")
  let ending := Lean.mkIdentFrom name (name.getId.appendAfter "_end")
  let ordinal : Lean.TSyntax `term := ⟨number.raw⟩
  let a ← `(command| private def $index : Fin ($unit).val.fns.length := ⟨$ordinal, by decide +kernel⟩)
  let b ← `(command| private def $shape : { actual : String //
      (fnAt ($unit).val $index).body = [.retires actual] } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| ownership_retire_step $step for $unit at $index named ($shape).val)
  let d ← `(command| private def $ending : { actual : Endblock (declOf ($unit).val)
      (verOf ($unit).val $index) false (ctxOf ($unit).val $index) ($step).val.1 //
      lowEnd ($unit).val $index (ctxOf ($unit).val $index) ($step).val.1 (fnAt ($unit).val $index)
        (fnAt ($unit).val $index).ret = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let e ← `(command| private def $name : { actual : PlainFunctionBody ($unit).val $index //
      lowBody ($unit).val $index (fnAt ($unit).val $index).body (fnAt ($unit).val $index).ret = .ok actual } := by
    refine ⟨Endblock.cons ($step).val.2 ($ending).val, ?_⟩
    exact (retire_body _ _ _ ($shape).property ($step).val ($step).property).trans
      ((congrArg (fun answer => answer.map (Endblock.cons ($step).val.2)) ($ending).property).trans (by rfl)))
  return ⟨Lean.mkNullNode #[a, b, c, d, e]⟩

scoped macro "ownership_retire_refusal " name:ident " for " unit:ident " at " number:num
    " with_reason " error:term : command => do
  let index := Lean.mkIdentFrom name (name.getId.appendAfter "_index")
  let shape := Lean.mkIdentFrom name (name.getId.appendAfter "_shape")
  let step := Lean.mkIdentFrom name (name.getId.appendAfter "_step")
  let ending := Lean.mkIdentFrom name (name.getId.appendAfter "_end")
  let ordinal : Lean.TSyntax `term := ⟨number.raw⟩
  let a ← `(command| private def $index : Fin ($unit).val.fns.length := ⟨$ordinal, by decide +kernel⟩)
  let b ← `(command| private def $shape : { actual : String //
      (fnAt ($unit).val $index).body = [.retires actual] } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| ownership_retire_step $step for $unit at $index named ($shape).val)
  let d ← `(command| private theorem $ending : lowEnd ($unit).val $index (ctxOf ($unit).val $index)
      ($step).val.1 (fnAt ($unit).val $index) (fnAt ($unit).val $index).ret = .error $error := by cbv)
  let e ← `(command| private theorem $name : lowBody ($unit).val $index (fnAt ($unit).val $index).body
      (fnAt ($unit).val $index).ret = .error $error := by
    exact (retire_body _ _ _ ($shape).property ($step).val ($step).property).trans
      ((congrArg (fun answer => answer.map (Endblock.cons ($step).val.2)) $ending).trans (by rfl)))
  return ⟨Lean.mkNullNode #[a, b, c, d, e]⟩

scoped macro "ownership_repeat_refusal " name:ident " for " unit:ident " at " number:num
    " with_reason " error:term : command => do
  let index := Lean.mkIdentFrom name (name.getId.appendAfter "_index")
  let shape := Lean.mkIdentFrom name (name.getId.appendAfter "_shape")
  let step := Lean.mkIdentFrom name (name.getId.appendAfter "_step")
  let failed := Lean.mkIdentFrom name (name.getId.appendAfter "_failed")
  let ordinal : Lean.TSyntax `term := ⟨number.raw⟩
  let a ← `(command| private def $index : Fin ($unit).val.fns.length := ⟨$ordinal, by decide +kernel⟩)
  let b ← `(command| private def $shape : { actual : String × String //
      (fnAt ($unit).val $index).body = [.retires actual.1, .retires actual.2] } := by
    refine ⟨(?_, ?_), by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| ownership_retire_step $step for $unit at $index named ($shape).val.1)
  let d ← `(command| private theorem $failed : lowStmtL (l := false) ($unit).val $index (ctxOf ($unit).val $index)
      (fnAt ($unit).val $index) ($step).val.1 (.retires ($shape).val.2) = .error $error := by cbv)
  let e ← `(command| private theorem $name : lowBody ($unit).val $index (fnAt ($unit).val $index).body
      (fnAt ($unit).val $index).ret = .error $error :=
    repeated_body _ _ _ _ _ ($shape).property ($step).val ($step).property $failed)
  return ⟨Lean.mkNullNode #[a, b, c, d, e]⟩

private theorem function_accepted {unit : UProg} {f : Fin unit.fns.length}
    (result : { actual : EnsTy unit f × RumpTy unit f × ReqTy unit f //
      lowerFnAt unit f = .ok actual }) :
    (lowerFnAt unit f).toOption.isSome = true := by
  rw [result.property]
  rfl

ownership_phase ownMove from Phases.Inputs.moveAtMarke
ownership_phase ownTerminal from Phases.Inputs.terminalMoveRetires
ownership_phase ownDropped from Phases.Inputs.terminalMoveDropped
ownership_phase ownRepeated from Phases.Inputs.repeatedRetire
ownership_phase ownOrdinary from Phases.Inputs.ordinaryRetire
ownership_phase ownHandback from Phases.Inputs.handbackRetire
ownership_phase ownReason from Phases.Inputs.terminalReasonRetire

ownership_call_body moveCaller for ownMove_unit at 1
ownership_retire_body terminalCallee for ownTerminal_unit at 0
ownership_call_body terminalCaller for ownTerminal_unit at 1
ownership_call_body droppedCaller for ownDropped_unit at 1
ownership_call_body repeatedCaller for ownRepeated_unit at 1
ownership_call_body ordinaryCaller for ownOrdinary_unit at 1
ownership_retire_body reasonCallee for ownReason_unit at 0
ownership_repeat_refusal repeatedCallee for ownRepeated_unit at 0 with_reason "retire without held mark: Marke"
ownership_retire_refusal handbackCallee for ownHandback_unit at 0 with_reason "lower: return without produced marks"

ownership_function ownMove0 for ownMove_unit at 0 with_body (by refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
ownership_function ownMove1 for ownMove_unit at 1 with_body moveCaller
ownership_function ownTerminal0 for ownTerminal_unit at 0 with_body terminalCallee
ownership_function ownTerminal1 for ownTerminal_unit at 1 with_body terminalCaller
ownership_refusal ownDropped0 for ownDropped_unit at 0 with_reason "lower: return without produced marks" with_body (by cbv)
ownership_function ownDropped1 for ownDropped_unit at 1 with_body droppedCaller
ownership_refusal ownRepeated0 for ownRepeated_unit at 0 with_reason "retire without held mark: Marke" with_body repeatedCallee
ownership_function ownRepeated1 for ownRepeated_unit at 1 with_body repeatedCaller
ownership_function ownOrdinary0 for ownOrdinary_unit at 0 with_body (by refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
ownership_function ownOrdinary1 for ownOrdinary_unit at 1 with_body ordinaryCaller
ownership_refusal ownHandback0 for ownHandback_unit at 0 with_reason "lower: return without produced marks" with_body handbackCallee
ownership_function ownReason0 for ownReason_unit at 0 with_body reasonCallee

-- These finite selectors are formed only after both complete results exist.
private theorem move_members : ∀ f : Fin ownMove_unit.val.fns.length,
    (lowerFnAt ownMove_unit.val f).toOption.isSome = true ∧
      (fnAt ownMove_unit.val f).decreases = none := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun f => Fin.elim0 f))
  · exact ⟨function_accepted ownMove0, by cbv⟩
  · exact ⟨function_accepted ownMove1, by cbv⟩

private theorem terminal_members : ∀ f : Fin ownTerminal_unit.val.fns.length,
    (lowerFnAt ownTerminal_unit.val f).toOption.isSome = true ∧
      (fnAt ownTerminal_unit.val f).decreases = none := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun f => Fin.elim0 f))
  · exact ⟨function_accepted ownTerminal0, by cbv⟩
  · exact ⟨function_accepted ownTerminal1, by cbv⟩

private theorem ordinary_members : ∀ f : Fin ownOrdinary_unit.val.fns.length,
    (lowerFnAt ownOrdinary_unit.val f).toOption.isSome = true ∧
      (fnAt ownOrdinary_unit.val f).decreases = none := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun f => Fin.elim0 f))
  · exact ⟨function_accepted ownOrdinary0, by cbv⟩
  · exact ⟨function_accepted ownOrdinary1, by cbv⟩

private theorem reason_members : ∀ f : Fin ownReason_unit.val.fns.length,
    (lowerFnAt ownReason_unit.val f).toOption.isSome = true ∧
      (fnAt ownReason_unit.val f).decreases = none := by
  refine Fin.cases ?_ (fun f => Fin.elim0 f)
  exact ⟨function_accepted ownReason0, by cbv⟩

private theorem dropped_members : ∀ f : Fin ownDropped_unit.val.fns.length,
    lowerFnAt ownDropped_unit.val f = .error "lower: return without produced marks" ∨
      (lowerFnAt ownDropped_unit.val f).toOption.isSome = true := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun f => Fin.elim0 f))
  · exact Or.inl ownDropped0
  · exact Or.inr (function_accepted ownDropped1)

private theorem repeated_members : ∀ f : Fin ownRepeated_unit.val.fns.length,
    lowerFnAt ownRepeated_unit.val f = .error "retire without held mark: Marke" ∨
      (lowerFnAt ownRepeated_unit.val f).toOption.isSome = true := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun f => Fin.elim0 f))
  · exact Or.inl ownRepeated0
  · exact Or.inr (function_accepted ownRepeated1)

private theorem handback_members : ∀ f : Fin ownHandback_unit.val.fns.length,
    lowerFnAt ownHandback_unit.val f = .error "lower: return without produced marks" ∨
      (lowerFnAt ownHandback_unit.val f).toOption.isSome = true := by
  refine Fin.cases ?_ (fun f => Fin.elim0 f)
  exact Or.inl ownHandback0

/-! ## C09: owner mint and linear handoff -/

theorem mintAtMarke_ok : stufe mintAtMarke = "OK" := by
  rights_ok Phases.Inputs.mintAtMarke

theorem moveAtMarke_ok : stufe moveAtMarke = "OK" := by
  exact Phases.lower_ok Phases.Inputs.moveAtMarke ownMove_items.property ownMove_unit.property
    (by cbv) (by cbv) move_members

theorem moveReasonAtMarke_ok : stufe moveReasonAtMarke = "OK" := by
  rights_ok Phases.Inputs.moveReasonAtMarke

theorem mintTwice_refused : stufe mintTwice = "elab: duplicate mint: Marke" := by
  rights_elab_error Phases.Inputs.mintTwice with_reason "duplicate mint: Marke"

theorem mintFremd_refused : stufe mintFremd = "elab: mint without owner: Fremd" := by
  rights_elab_error Phases.Inputs.mintFremd with_reason "mint without owner: Fremd"

theorem moveFremd_refused : stufe moveFremd = "elab: move without owner: Fremd" := by
  rights_elab_error Phases.Inputs.moveFremd with_reason "move without owner: Fremd"

theorem moveBorrowed_refused :
    stufe moveBorrowed = "elab: mark both borrowed and moved: Marke" := by
  rights_elab_error Phases.Inputs.moveBorrowed with_reason "mark both borrowed and moved: Marke"

theorem moveDropped_refused :
    stufe moveDropped = "lower: call without held mark" := by
  rights_lower_error Phases.Inputs.moveDropped with_reason "call without held mark" at_member 1

/-! ## C09 terminal moves and C16 ordinary consumption -/

theorem terminalMoveRetires_zeuge : stufe terminalMoveRetires = "OK" := by
  exact Phases.lower_ok Phases.Inputs.terminalMoveRetires ownTerminal_items.property ownTerminal_unit.property
    (by cbv) (by cbv) terminal_members

/-- Omitting retire leaves an input outside `ende`; exact return inventory
    refuses the body even though the terminal call signature is valid. -/
theorem terminalMoveDropped_refused :
    stufe (terminalMoveSource "") = "lower: lower: return without produced marks" := by
  exact Phases.lower_error Phases.Inputs.terminalMoveDropped ownDropped_items.property ownDropped_unit.property
    (by cbv) dropped_members ⟨ownDropped0_index, ownDropped0⟩

theorem borrowedRetire_refused :
    stufe borrowedRetire = "lower: retire of borrowed mark: Marke" := by
  rights_lower_error Phases.Inputs.borrowedRetire with_reason "retire of borrowed mark: Marke" at_member 0

theorem unheldRetire_refused :
    stufe unheldRetire = "lower: retire without held mark: Marke" := by
  rights_lower_error Phases.Inputs.unheldRetire with_reason "retire without held mark: Marke" at_member 0

theorem repeatedRetire_refused :
    stufe (terminalMoveSource "retires Marke; retires Marke;") =
      "lower: retire without held mark: Marke" := by
  exact Phases.lower_error Phases.Inputs.repeatedRetire ownRepeated_items.property ownRepeated_unit.property
    (by cbv) repeated_members ⟨ownRepeated0_index, ownRepeated0⟩

theorem ordinaryRetire_zeuge : stufe ordinaryRetire = "OK" := by
  exact Phases.lower_ok Phases.Inputs.ordinaryRetire ownOrdinary_items.property ownOrdinary_unit.property
    (by cbv) (by cbv) ordinary_members

theorem handbackRetire_refused :
    stufe handbackRetire = "lower: lower: return without produced marks" := by
  exact Phases.lower_error Phases.Inputs.handbackRetire ownHandback_items.property ownHandback_unit.property
    (by cbv) handback_members ⟨ownHandback0_index, ownHandback0⟩

theorem terminalReasonRetire_ok : stufe terminalReasonRetire = "OK" := by
  exact Phases.lower_ok Phases.Inputs.terminalReasonRetire ownReason_items.property ownReason_unit.property
    (by cbv) (by cbv) reason_members

end Gabbro.Grammatik.Parser.UebersetzeProben11
