module
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

/-- Canonical alias collection preserves source order across list concatenation. -/
theorem aliases_append (values : List (String × Int)) (first rest : List SItemTief) :
    uAliase values (first ++ rest) = uAliase values first ++ uAliase values rest := by
  induction first with
  | nil => rfl
  | cons item items ih =>
    cases item <;> try simpa only [List.cons_append, uAliase, List.nil_append] using ih
    case typeT flags name args order body =>
      cases body with
      | none => simpa only [List.cons_append, uAliase, List.nil_append] using ih
      | some ty =>
        cases ty <;> simp [uAliase, ih]
        all_goals split <;> simp_all

/-- The rewritten declaration really enters the frozen elaborator's alias environment with exactly
    the range resolved from the source name, not merely an equivalent unused type expression. -/
theorem aliasItem_collected (values : List (String × Int))
    (env : List (String × (Int × Int))) (flags : List String) (name : String)
    (order : List String) (original : String) (lo hi : Int)
    (h : uTypName env original = .ok (lo, hi)) :
    uAliase values [aliasItem env (.typeT flags name [] order (some (.atom original)))] =
      [(name, (lo, hi))] := by
  have hb := (aliasBody_correct env [] original lo hi h).1
  simp [aliasItem, hb, uAliase, bound_correct]

/-- A source alias extends its declaration environment with the exact canonical target range. -/
def aliasStep (values : List (String × Int))
    (env : List (String × (Int × Int))) (item : SItemTief) : List (String × (Int × Int)) :=
  match item with
  | .typeT _ name [] _ (some (.atom original)) =>
    match uTypName env original with
    | .ok range => env ++ [(name, range)]
    | .error _ => env ++ uAliase values [item]
  | _ => env ++ uAliase values [item]

theorem aliasStep_correct (values : List (String × Int))
    (env : List (String × (Int × Int))) (item : SItemTief) :
    env ++ uAliase values [aliasItem env item] = aliasStep values env item := by
  cases item <;> try rfl
  case typeT flags name args order body =>
    cases args with
    | cons a rest => rfl
    | nil =>
      cases body with
      | none => rfl
      | some ty =>
        cases ty <;> try rfl
        case atom original =>
          cases ht : uTypName env original with
          | error e =>
            have hb : aliasBody env original = .error e := by
              simp only [aliasBody, ht]
              rfl
            simp [aliasItem, hb, ht, aliasStep]
          | ok range =>
            rcases range with ⟨lo, hi⟩
            rw [aliasItem_collected values env flags name order original lo hi ht]
            simp [aliasStep, ht]

/-- Full alias-environment collection, not just local type equivalence. -/
theorem aliases_collected (values : List (String × Int))
    (env : List (String × (Int × Int))) (items : List SItemTief) :
    env ++ uAliase values (aliases values env items) = items.foldl (aliasStep values) env := by
  induction items generalizing env with
  | nil => simp [aliases, rewrite, uAliase]
  | cons item rest ih =>
    change env ++ uAliase values
      ([aliasItem env item] ++ aliases values (env ++ uAliase values [aliasItem env item]) rest) = _
    rw [aliases_append, ← List.append_assoc, ih, aliasStep_correct]
    rfl

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

/-- One scalar declaration is evaluated at its exact canonical source type. Earlier scalar
    values supply singleton bounds, in the same lookup order as the canonical runtime type scope. -/
def typedItem (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) : SItemTief → Option (List (String × Int))
  | .constT name ty (.one expr) => do
    match uFeldTyp (env ++ values.map (fun c => (c.1, (c.2, c.2)))) ty with
    | .error _ => pure values -- Deferred to the mandatory whole-source typed literal check.
    | .ok range => do
      let value ← uKonstWert range.1 range.2 fns values 64 expr
      pure (values ++ [(name, value)])
  | _ => some values

/-- The scalar specialization keeps the canonical evaluator and appends to the complete
    ordered scope. Optional aggregate leaf adapters cannot alter this numeric step. -/
theorem typedItem_scalar_eq (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (name : String) (ty : STyp) (expr : SExpr) (lo hi : Int)
    (typed : uFeldTyp (env ++ values.map (fun c => (c.1, (c.2, c.2)))) ty = .ok (lo, hi)) :
    typedItem env fns values (.constT name ty (.one expr)) =
      (uKonstWert lo hi fns values 64 expr).map (fun value => values ++ [(name, value)]) := by
  cases evaluated : uKonstWert lo hi fns values 64 expr <;> simp [typedItem, typed, evaluated]

/-- Every successful step extends the complete ordered scope. Deferred declarations preserve
    it exactly; numeric declarations append one checked binding, including negative values. -/
theorem typedItem_extends (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values result : List (String × Int)) (item : SItemTief)
    (accepted : typedItem env fns values item = some result) :
    ∃ suffix, result = values ++ suffix := by
  cases item <;> try exact ⟨[], by simpa only [List.append_nil] using (Option.some.inj accepted).symm⟩
  case constT name ty payload =>
    cases payload with
    | rows _ => exact ⟨[], by simpa only [List.append_nil] using (Option.some.inj accepted).symm⟩
    | one expr =>
      cases typed : uFeldTyp (env ++ values.map (fun c => (c.1, (c.2, c.2)))) ty with
      | error e =>
        have same : values = result := by simpa [typedItem, typed] using accepted
        exact ⟨[], by simpa only [List.append_nil] using same.symm⟩
      | ok range =>
        rcases range with ⟨lo, hi⟩
        rw [typedItem_scalar_eq env fns values name ty expr lo hi typed] at accepted
        cases evaluated : uKonstWert lo hi fns values 64 expr with
        | none => simp only [evaluated, Option.map_none, reduceCtorEq] at accepted
        | some value =>
          simp only [evaluated, Option.map_some, Option.some.injEq] at accepted
          exact ⟨[(name, value)], accepted.symm⟩

/-- Every successful scalar step checks the original type through canonical elaboration and
    every expression intermediate through the existing exact-range evaluator. -/
theorem typedItem_sound (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values result : List (String × Int)) (name : String) (ty : STyp) (expr : SExpr)
    (scalar : (uFeldTyp (env ++ values.map (fun c => (c.1, (c.2, c.2)))) ty).toOption.isSome = true)
    (h : typedItem env fns values (.constT name ty (.one expr)) = some result) :
    ∃ lo hi value,
      uTyp (env ++ values.map (fun c => (c.1, (c.2, c.2)))) [] [] ty = .ok (.int lo hi) ∧
      uKonstWert lo hi fns values 64 expr = some value ∧ result = values ++ [(name, value)] := by
  cases ht : uFeldTyp (env ++ values.map (fun c => (c.1, (c.2, c.2)))) ty with
  | error e => simp [ht, Except.toOption] at scalar
  | ok range =>
    rcases range with ⟨lo, hi⟩
    rw [typedItem_scalar_eq env fns values name ty expr lo hi ht] at h
    cases hv : uKonstWert lo hi fns values 64 expr with
    | none => simp only [hv, Option.map_none, reduceCtorEq] at h
    | some value =>
      simp only [hv, Option.map_some, Option.some.injEq] at h
      exact ⟨lo, hi, value, fieldType_sound _ _ _ _ ht, hv, h.symm⟩


end Gabbro.Stage0.Frontend
