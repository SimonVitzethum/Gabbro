module
public import Stage0.Frontend.Functions
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- The integer alias forms handled by the canonical alias adapter. -/
def integerAlias (item : SItemTief) : Option (String × STyp) :=
  match item with
  | .typeT _ name [] _ (some ty@(.atom _))
  | .typeT _ name [] _ (some ty@(.range _ _ _ _)) => some (name, ty)
  | _ => none

/-- Each original integer alias denotes exactly its canonical source type in the final scope.
    This fact is independent of discovery candidates and the alias scheduling algorithm. -/
def AliasMeaning (types : List (String × (Int × Int))) (item : SItemTief) : Prop :=
  match integerAlias item with
  | none => True
  | some (name, ty) => ∃ lo hi,
    uTypName types name = .ok (lo, hi) ∧ uTyp types [] ty = .ok (.int lo hi)

/-- Independently recheck the named range against canonical elaboration of the original body. -/
def checkAliasMeaning (types : List (String × (Int × Int))) (item : SItemTief) : Bool :=
  match integerAlias item with
  | none => true
  | some (name, ty) =>
    match uTypName types name, uFeldTyp types ty with
    | .ok named, .ok body => decide (named = body)
    | _, _ => false

theorem checkAliasMeaning_sound (types : List (String × (Int × Int))) (item : SItemTief)
    (h : checkAliasMeaning types item = true) : AliasMeaning types item := by
  cases ha : integerAlias item with
  | none => simp only [AliasMeaning, ha]
  | some alias =>
    rcases alias with ⟨name, ty⟩
    simp only [AliasMeaning, ha]
    cases hn : uTypName types name <;> cases ht : uFeldTyp types ty <;>
      simp only [checkAliasMeaning, ha, hn, ht, Bool.false_eq_true, decide_eq_true_eq] at h
    rename_i named body
    cases h
    rcases named with ⟨lo, hi⟩
    exact ⟨lo, hi, rfl, fieldType_sound types ty lo hi ht⟩

theorem checkAliasMeaning_sound_zeuge :
    AliasMeaning [("Byte", (0, 255)), ("Count", (0, 255))]
      (.typeT [] "Count" [] [] (some (.atom "Byte"))) :=
  checkAliasMeaning_sound _ _ (by decide +kernel)

/-- A successful name lookup alone cannot certify a wrong alias range. -/
theorem checkAliasMeaning_refused_zeuge :
    checkAliasMeaning [("Byte", (0, 255)), ("Count", (0, 100))]
      (.typeT [] "Count" [] [] (some (.atom "Byte"))) = false := by decide +kernel

end Gabbro.Stage0.Frontend
