module
public import Stage0.Frontend.Functions
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
    uTypName types name = .ok (lo, hi) ∧ uTyp types [] [] [] ty = .ok (.int lo hi)

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
