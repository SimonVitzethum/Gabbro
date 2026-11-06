module
public import Grammatik.Parser.Elab.Konst.Scopes.Folds
public import Stage0.Frontend.Correctness
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

/-- The canonical constant collector composes in declaration order, including its failure branches. -/
theorem constants_append (fns : List UKonstFn) (first rest : List SItemTief)
    (values : List (String × Int)) :
    uConstsRech fns (first ++ rest) values =
      uConstsRech fns rest (uConstsRech fns first values) := by
  induction first generalizing values with
  | nil => rfl
  | cons item items ih =>
    cases item <;> try simpa only [List.cons_append, uConstsRech] using ih values
    case constT name ty payload =>
      cases payload with
      | rows xs => simpa only [List.cons_append, uConstsRech] using ih values
      | one expr =>
        cases expr <;> cases ty <;> simp [uConstsRech, ih]
        all_goals split <;> try simp_all
        all_goals split <;> try simp_all

/-- A scalar fold preserves every type declaration, including dependencies on constants. -/
theorem constant_aliases (external : List (String × Int))
    (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) :
    uAliase external [constant env fns values item] = uAliase external [item] := by
  rcases constant_sound env fns values item with h | h
  · rw [← h]
  · rcases h with ⟨name, ty, expr, lo, hi, v, hs, ht, _⟩ |
        ⟨name, ty, expr, outTy, outExpr, lo, hi, v, hs, ht, _⟩
    all_goals rw [ht, hs]; rfl

/-- The actual canonical alias collector after scalar folding sees exactly the original type
    declarations at the final constant environment, including dependent range bounds. -/
theorem constants_aliases (external : List (String × Int))
    (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (items : List SItemTief) :
    uAliase external (constants env fns values items) = uAliase external items := by
  induction items generalizing values with
  | nil => rfl
  | cons item rest ih =>
    change uAliase external ([constant env fns values item] ++
      constants env fns (uConstsRech fns [constant env fns values item] values) rest) = _
    rw [aliases_append, ih, constant_aliases]
    exact (aliases_append external [item] rest).symm

/-- Operational fold step for the nonnegative scalar adapter, derived from the canonical
    evaluator. Unchanged cases retain baseline collection; this is not whole-source semantics. -/
def constantStep (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) : List (String × Int) :=
  match item with
  | .constT name ty (.one expr) =>
    match uFeldTyp env ty with
    | .ok (lo, hi) =>
      match uKonstWert lo hi fns values 64 expr with
      | some v => if 0 ≤ v then values ++ [(name, v)]
          else uConstsRech fns [negative env fns values name ty expr lo hi v] values
      | none => uConstsRech fns [item] values
    | .error _ => uConstsRech fns [item] values
  | _ => uConstsRech fns [item] values

theorem constantStep_correct (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) :
    uConstsRech fns [constant env fns values item] values = constantStep env fns values item := by
  cases item <;> try rfl
  case constT name ty payload =>
    cases payload with
    | rows xs => rfl
    | one expr =>
      cases ht : uFeldTyp env ty with
      | error e => simp [constantStep, constant, ht]
      | ok range =>
        rcases range with ⟨lo, hi⟩
        cases he : uKonstWert lo hi fns values 64 expr with
        | none => simp [constantStep, constant, ht, he]
        | some v =>
          by_cases hv : 0 ≤ v
          · simpa [constantStep, constant, ht, he, hv] using
              (constant_correct env fns values name ty expr lo hi v ht he hv).2
          · simp [constantStep, constant, ht, he, hv]

/-- The emitted constant declarations collect exactly the source's typed, declaration-order fold. -/
theorem constants_collected (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (items : List SItemTief) :
    uConstsRech fns (constants env fns values items) values =
      items.foldl (constantStep env fns) values := by
  induction items generalizing values with
  | nil => rfl
  | cons item rest ih =>
    change uConstsRech fns ([constant env fns values item] ++
      constants env fns (uConstsRech fns [constant env fns values item] values) rest) values = _
    rw [constants_append, ih, constantStep_correct]
    rfl

end Gabbro.Stage0.Frontend
