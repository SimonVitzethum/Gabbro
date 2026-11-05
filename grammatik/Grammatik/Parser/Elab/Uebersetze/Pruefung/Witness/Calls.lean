module

public import Grammatik.Parser.Elab.UebersetzeAllg2.CallArguments
public import Grammatik.Parser.Elab.UebersetzeAllg3.Returns
import all Grammatik.Parser.Elab.UebersetzeAllg2.CallArguments
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
import all Grammatik.Parser.Elab.UebersetzeAllg3.Returns

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- Select the real scalar argument branch while the declaration, context and
-- resources are still symbolic. No capability/type matcher is instantiated at
-- a concrete check unit merely to pass its Bool or integer argument.
private theorem check_argument_bool (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u))) (value : UEns) :
    lowCallArgOneL u caller Γ fn Λ .bool .bool (.bval value) =
      lowEns u Γ Λ fn none value := by
  rfl

private theorem check_argument_integer (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (lo hi : Int) (value : USide) :
    lowCallArgOneL u caller Γ fn Λ .int (.int lo hi) (.val value) =
      lowWertAt u Γ Λ fn lo hi value := by
  change (match lowWertAt u Γ Λ fn lo hi value with
    | .error error => Except.error error
    | .ok term => Except.ok term) = _
  cases lowWertAt u Γ Λ fn lo hi value <;> rfl

private theorem check_arguments_nil (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u))) :
    lowCallArgsAuxL u caller Γ fn Λ [] [] [] = .ok Args.nil := by
  rfl

-- Retain all three lists and the exact dependent Args.cons endpoint, including
-- both error branches. The tail is the actual canonical recursive collector.
private theorem check_arguments_cons (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (kind : UParamArt) (kinds : List UParamArt) (ty : Ty) (types : List Ty)
    (argument : UArg) (arguments : List UArg) :
    lowCallArgsAuxL u caller Γ fn Λ (kind :: kinds) (ty :: types)
      (argument :: arguments) =
      match lowCallArgOneL u caller Γ fn Λ kind ty argument with
      | .error error => .error error
      | .ok term =>
        match lowCallArgsAuxL u caller Γ fn Λ kinds types arguments with
        | .error error => .error error
        | .ok rest => .ok (Args.cons term rest) := by
  rfl

-- Equality transport is proved before the actual unit is substituted. The
-- result selector reads the recorded result, with the canonical erg_eq proof
-- supplying the same declaration-indexed equality to the original callback.
private def check_result_value {α : Type} :
    (result : Option Ty) →
    ((ty : Ty) → result = some ty → Except String α) → Except String α
  | none, _ => Except.error "call without a value"
  | some ty, callback => callback ty rfl

private theorem check_result_transport {α : Type} (actual recorded : Option Ty)
    (same : actual = recorded)
    (callback : (ty : Ty) → actual = some ty → Except String α) :
    check_result_value actual callback =
      check_result_value recorded (fun ty found => callback ty (same.trans found)) := by
  cases same
  rfl

private theorem check_result_select {α : Type} (u : UProg) (callee : Fin u.fns.length)
    (callback : (ty : Ty) → (declOf u).erg callee = some ty → Except String α) :
    withErg u callee callback =
      check_result_value (fnAt u callee).ergTy
        (fun ty found => callback ty ((erg_eq u callee).trans found)) := by
  have selected : withErg u callee callback =
      check_result_value ((declOf u).erg callee) callback := by
    unfold withErg
    generalize actual : (declOf u).erg callee = result at callback ⊢
    cases result <;> rfl
  exact selected.trans (check_result_transport _ _ (erg_eq u callee) callback)

-- Return values keep the original result-index transport. In particular, a
-- Bool is lowered in the complete current Γ/Λ, rather than in a fixed rest.
private theorem check_return_empty (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) :
    lowErg u caller Γ Λ fn .empty =
      match found : (fnAt u caller).ergTy with
      | none =>
        have result : (verOf u caller).erg = none := by
          show (vertragVon (declOf u) caller).erg = none
          rw [vErg_eq u caller, found]
        .ok (by
          show ErgExpr (declOf u) Γ Λ (verOf u caller).erg
          rw [result]
          exact ErgExpr.empty)
      | some _ => .error "return without value with result" := by
  rfl

private theorem check_return_bool (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (value : UEns) :
    lowErg u caller Γ Λ fn (.bool value) =
      match found : (fnAt u caller).ergTy with
      | some .bool =>
        match lowEns u Γ Λ fn none value with
        | .error error => .error error
        | .ok term => .ok (by
            show ErgExpr (declOf u) Γ Λ (verOf u caller).erg
            rw [show (verOf u caller).erg = (vertragVon (declOf u) caller).erg from rfl,
              vErg_eq u caller, found]
            exact ErgExpr.val term)
      | some _ => .error "truth value returned for a non-bool result"
      | none => .error "return with value without result" := by
  rfl

-- The success and refusal equations share the very same resource permutation
-- test. In particular, the missing-gibt witness must still fail this test.
private theorem check_end_empty (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) :
    lowEnd u caller Γ Λ fn .empty =
      match lowErg u caller Γ Λ fn .empty with
      | .error error => .error error
      | .ok value =>
        if ready : decide (Λ.Perm (verOf u caller).ende) = true then
          .ok (Endblock.ret value (of_decide_eq_true ready))
        else .error "lower: return without produced marks" := by
  rfl

private theorem check_end_bool (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (value : UEns) :
    lowEnd u caller Γ Λ fn (.bool value) =
      match lowErg u caller Γ Λ fn (.bool value) with
      | .error error => .error error
      | .ok term =>
        if ready : decide (Λ.Perm (verOf u caller).ende) = true then
          .ok (Endblock.ret term (of_decide_eq_true ready))
        else .error "lower: return without produced marks" := by
  rfl

end Gabbro.Grammatik.Parser.Uebersetze
