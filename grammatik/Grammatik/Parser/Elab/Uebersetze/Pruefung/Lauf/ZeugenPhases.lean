module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Boden
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
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


@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The source is the complete check/floor/gate fixture. Driver policy is
    explicit configuration: execute `p`, and consume its report through `g`. -/
def retiringSelection : CheckConsumerSelection := ⟨"p", "g"⟩

namespace RetiringWitness

-- Infer the actual selected data once, after the existing whole-source theorem.
-- No source getter or lexer/parser proof is part of the downstream unit data.
def selected : {unit : UProg //
    ((elabText checkTextBodenWahr).bind fun original =>
      uSelectCheckConsumers original [retiringSelection]) = .ok unit} := by
  refine ⟨?unit, ?produced⟩
  case produced =>
    rw [bodenWahr_source]
    cbv <;> exact Eq.refl _

end RetiringWitness

theorem retiringSource_selected :
    ((elabText checkTextBodenWahr).bind fun u =>
      uSelectCheckConsumers u [retiringSelection]).toOption.isSome = true := by
  rw [RetiringWitness.selected.property]
  rfl

def retiringU : UProg := RetiringWitness.selected.val

namespace RetiringWitness

-- Select the actual scalar calls and returning channels at symbolic types.
-- lowRufKopf remains the complete resource/owner/footprint dispatcher here;
-- lowBodyF uses the unchanged actual statement-list length plus one.
attribute [local cbv_opaque] lowCallArgOneL lowCallArgsAuxL withErg lowErg lowEnd
attribute [local cbv_eval] check_argument_bool check_argument_integer
  check_arguments_nil check_arguments_cons
  check_result_select check_return_empty check_return_bool check_end_empty check_end_bool
  floor_name_self floor_mark_self

abbrev FunctionType (index : Fin retiringU.fns.length) :=
  EnsTy retiringU index × RumpTy retiringU index × ReqTy retiringU index

def index0 : Fin retiringU.fns.length := ⟨0, by change 0 < 6; decide⟩

def function0 : {result : FunctionType index0 //
    lowerFnAt retiringU index0 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def index1 : Fin retiringU.fns.length := ⟨1, by change 1 < 6; decide⟩

def function1 : {result : FunctionType index1 //
    lowerFnAt retiringU index1 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def index2 : Fin retiringU.fns.length := ⟨2, by change 2 < 6; decide⟩

def function2 : {result : FunctionType index2 //
    lowerFnAt retiringU index2 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def index3 : Fin retiringU.fns.length := ⟨3, by change 3 < 6; decide⟩

def function3 : {result : FunctionType index3 //
    lowerFnAt retiringU index3 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def index4 : Fin retiringU.fns.length := ⟨4, by change 4 < 6; decide⟩

def function4 : {result : FunctionType index4 //
    lowerFnAt retiringU index4 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def index5 : Fin retiringU.fns.length := ⟨5, by change 5 < 6; decide⟩

def function5 : {result : FunctionType index5 //
    lowerFnAt retiringU index5 = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

-- Close each dependent function result before constructing the finite selector.
def functions (index : Fin retiringU.fns.length) :
    {result : FunctionType index // lowerFnAt retiringU index = .ok result} :=
  Fin.cases function0
    (Fin.cases function1
      (Fin.cases function2
        (Fin.cases function3
          (Fin.cases function4
            (Fin.cases function5 (fun i => Fin.elim0 i)))))) index

private theorem function_made (index : Fin retiringU.fns.length) :
    lowerFnAt retiringU index = .ok (functions index).val := (functions index).property

private theorem each_made :
    lowerEach retiringU (List.finRange retiringU.fns.length) = .ok () := by
  change lowerEach retiringU [index0, index1, index2, index3, index4, index5] = .ok ()
  simp only [lowerEach, function_made]

private theorem invariants_made :
    lowerInvs retiringU (List.finRange retiringU.invs.length) = .ok () := by cbv

private theorem contracts_made : contractGate retiringU = true := by cbv

private def measures : {result : Measures.Export retiringU // Measures.lowerMeasures retiringU = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private theorem measures_made (P : Programm (declOf retiringU)) :
    @Eq (Except String (Programm (declOf retiringU) × List (declOf retiringU).Fn))
      (Measures.checkedProgram retiringU P) (.ok (P, List.finRange retiringU.fns.length)) := by
  apply check_measure_gate _ measures.val measures.property
  have absent : retiringU.fns.all (fun fn => decide (fn.decreases = none)) = true := by cbv
  intro fn member
  exact of_decide_eq_true (List.all_eq_true.mp absent fn member)

-- This is the canonical assembler, with all six previously closed function
-- certificates and the unchanged invariant, contract and measure gates.
def program : {result : Programm (declOf retiringU) × List (declOf retiringU).Fn //
    lowerAllg retiringU = .ok result} :=
  ⟨(progOfFn retiringU
      (fun f => (functions f).val.1)
      (fun f => (functions f).val.2.1)
      (fun f => (functions f).val.2.2)
      (fun i => lowerInvGut retiringU i
        (lowerInvs_all_ok retiringU _ i (List.mem_finRange i) invariants_made))
      (ptrVertragOf retiringU)
      (fun a => axVertragOf retiringU a (Bool.and_eq_true_iff.mp contracts_made).2),
      List.finRange retiringU.fns.length), by
    exact check_assembly retiringU (fun f => (functions f).val)
      function_made invariants_made each_made contracts_made measures_made⟩

def checks : {result : List (CheckDecl (declOf retiringU)) // uCheckDecls retiringU = .ok result} := by
  refine ⟨?result, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

end RetiringWitness

theorem retiringU_lowered : (lowerAllg retiringU).toOption.isSome = true := by
  rw [RetiringWitness.program.property]
  rfl

def retiringP : Programm (declOf retiringU) := RetiringWitness.program.val.1

theorem retiringU_checks : (uCheckDecls retiringU).toOption.isSome = true := by
  rw [RetiringWitness.checks.property]
  rfl

def retiringChecks : List (CheckDecl (declOf retiringU)) := RetiringWitness.checks.val

def retiringCheck : CheckDecl (declOf retiringU) :=
  retiringChecks.get ⟨0, by change 0 < 1; decide⟩

def retiringProbe : (declOf retiringU).Fn := RetiringWitness.index1
def retiringReporter : (declOf retiringU).Fn := RetiringWitness.index2
def retiringWrapper : (declOf retiringU).Fn := RetiringWitness.index3
def retiringConsumer : (declOf retiringU).Fn := RetiringWitness.index4
def retiringDriver : (declOf retiringU).Fn := RetiringWitness.index5

end Gabbro.Grammatik.Parser.Uebersetze
