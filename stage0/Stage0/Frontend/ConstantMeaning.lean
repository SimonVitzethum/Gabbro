import Stage0.Frontend.Environments

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- A named scalar has its original canonical type and exactly its original initializer value
    in the final scope. Arrays retain their separate ArrayMeaning check in the actual compiler. -/
def ConstantMeaning (types : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) : Prop :=
  match item with
  | .constT name ty (.one expr) => ∃ lo hi binding,
    values.find? (fun entry => strEq entry.1 name) = some binding ∧
    uTyp types [] ty = .ok (.int lo hi) ∧
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
