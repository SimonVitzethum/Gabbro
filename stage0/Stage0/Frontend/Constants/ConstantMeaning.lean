module
public import Stage0.Frontend.Environments
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


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- A named scalar has its original canonical type and exactly its original initializer value
    in the final scope. Non-scalars defer to the mandatory ArrayMeaning check, which validates
    every original constant with the canonical typed literal elaborator. -/
def ConstantMeaning (types : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) : Prop :=
  match item with
  | .constT name ty (.one expr) => match uFeldTyp types ty with
    | .error _ => True
    | .ok (lo, hi) => ∃ binding,
    values.find? (fun entry => strEq entry.1 name) = some binding ∧
    uTyp types [] [] ty = .ok (.int lo hi) ∧
    uKonstWert lo hi fns values 64 expr = some binding.2
  | _ => True

/-- Candidate values are never their own certificate: re-evaluate every original initializer
    at the final original declared range, including every checked intermediate value. -/
def checkConstantMeaning (types : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) : Bool :=
  match item with
  | .constT name ty (.one expr) =>
    match values.find? (fun entry => strEq entry.1 name), uFeldTyp types ty with
    | some binding, .ok (lo, hi) => decide (uKonstWert lo hi fns values 64 expr = some binding.2)
    | _, .error _ => true
    | none, .ok _ => false
  | _ => true

theorem checkConstantMeaning_sound (types : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief)
    (h : checkConstantMeaning types fns values item = true) : ConstantMeaning types fns values item := by
  cases item <;> try trivial
  case constT name ty payload =>
    cases payload with
    | rows xs => trivial
    | one expr =>
      cases ht : uFeldTyp types ty with
      | error e => simp only [ConstantMeaning, ht]
      | ok range =>
        rcases range with ⟨lo, hi⟩
        cases hn : values.find? (fun entry => strEq entry.1 name) with
        | none => simp only [checkConstantMeaning, hn, ht, Bool.false_eq_true] at h
        | some binding =>
          simp only [checkConstantMeaning, hn, ht] at h
          simp only [ConstantMeaning, ht]
          exact ⟨binding, hn, fieldType_sound _ _ _ _ ht, of_decide_eq_true h⟩

/-- At the actual source-derived scope, every scalar retains the old typed step guarantee.
    The classifier premise of typedItem_sound is derived here, never supplied by a caller.
    Deferred types still require the compiler's mandatory ArrayMeaning certificate. -/
def ScalarStep {items : List SItemTief} (scope : Scopes items) (item : SItemTief) : Prop :=
  match item with
  | .constT name ty (.one expr) => match uFeldTyp scope.types ty with
    | .error _ => True
    | .ok _ => ∃ lo hi value,
      uTyp scope.types [] [] ty = .ok (.int lo hi) ∧
      uKonstWert lo hi scope.functions scope.values 64 expr = some value ∧
      typedItem scope.declared scope.functions scope.values item =
        some (scope.values ++ [(name, value)])
  | _ => True

theorem constantMeaning_scalarStep {items : List SItemTief} (scope : Scopes items) (item : SItemTief)
    (meaning : ConstantMeaning scope.types scope.functions scope.values item) : ScalarStep scope item := by
  cases item <;> try trivial
  case constT name ty payload =>
    cases payload with
    | rows _ => trivial
    | one expr =>
      cases ht : uFeldTyp scope.types ty with
      | error e => simp only [ScalarStep, ht]
      | ok range =>
        rcases range with ⟨lo, hi⟩
        simp only [ConstantMeaning, ht] at meaning
        obtain ⟨binding, _, _, value⟩ := meaning
        have scalar : (uFeldTyp (scope.declared ++ scope.values.map
            (fun c => (c.1, (c.2, c.2)))) ty).toOption.isSome = true := by
          change (uFeldTyp scope.types ty).toOption.isSome = true
          simp only [ht, Except.toOption, Option.isSome_some]
        have step : typedItem scope.declared scope.functions scope.values
            (.constT name ty (.one expr)) = some (scope.values ++ [(name, binding.2)]) := by
          change (match uFeldTyp scope.types ty with
            | .error _ => some scope.values
            | .ok range => (uKonstWert range.1 range.2 scope.functions scope.values 64 expr).map
              (fun value => scope.values ++ [(name, value)])) = _
          simp only [ht, value, Option.map_some]
        obtain ⟨a, b, result, typed, evaluated, collected⟩ :=
          typedItem_sound scope.declared scope.functions scope.values
            (scope.values ++ [(name, binding.2)]) name ty expr scalar step
        simp only [ScalarStep, ht]
        refine ⟨a, b, result, typed, evaluated, ?_⟩
        rw [← collected]
        exact step

/-- The meaning check accepts a forward binding and rejects a fabricated discovery value. -/
theorem checkConstantMeaning_sound_zeuge :
    ConstantMeaning [] [] [("LATER", 42), ("ANSWER", 42)]
      (.constT "ANSWER" (.atom "u8") (.one (.variable "LATER"))) :=
  checkConstantMeaning_sound _ _ _ _ (by decide +kernel)

theorem checkConstantMeaning_refused_zeuge :
    checkConstantMeaning [] [] [("LATER", 42), ("ANSWER", 41)]
      (.constT "ANSWER" (.atom "u8") (.one (.variable "LATER"))) = false := by decide +kernel

end Gabbro.Stage0.Frontend
