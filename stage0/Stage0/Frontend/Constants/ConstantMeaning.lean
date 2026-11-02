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
    in the final scope. Arrays retain their separate ArrayMeaning check in the actual compiler. -/
def ConstantMeaning (types : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) : Prop :=
  match item with
  | .constT name ty (.one expr) => ∃ lo hi binding,
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
    | _, _ => false
  | _ => true

theorem checkConstantMeaning_sound (types : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief)
    (h : checkConstantMeaning types fns values item = true) : ConstantMeaning types fns values item := by
  cases item <;> try trivial
  case constT name ty payload =>
    cases payload with
    | rows xs => trivial
    | one expr =>
      cases hn : values.find? (fun entry => strEq entry.1 name) <;>
        cases ht : uFeldTyp types ty <;>
        simp only [checkConstantMeaning, hn, ht, Bool.false_eq_true] at h
      rename_i binding range
      rcases range with ⟨lo, hi⟩
      exact ⟨lo, hi, binding, hn, fieldType_sound _ _ _ _ ht, of_decide_eq_true h⟩

/-- The meaning check accepts a forward binding and rejects a fabricated discovery value. -/
theorem checkConstantMeaning_sound_zeuge :
    ConstantMeaning [] [] [("LATER", 42), ("ANSWER", 42)]
      (.constT "ANSWER" (.atom "u8") (.one (.variable "LATER"))) :=
  checkConstantMeaning_sound _ _ _ _ (by decide +kernel)

theorem checkConstantMeaning_refused_zeuge :
    checkConstantMeaning [] [] [("LATER", 42), ("ANSWER", 41)]
      (.constT "ANSWER" (.atom "u8") (.one (.variable "LATER"))) = false := by decide +kernel

end Gabbro.Stage0.Frontend
