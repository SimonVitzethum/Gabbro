import Stage0.Frontend.Correctness

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

/-- Total declaration-order collection succeeds only when each scalar initializer is evaluated
    in its declared canonical range. Negative and duplicate bindings are retained without filtering. -/
def typedConstants (env : List (String × (Int × Int))) (fns : List UKonstFn) :
    List SItemTief → List (String × Int) → Option (List (String × Int))
  | [], values => some values
  | .constT name ty (.one expr) :: rest, values => do
    let range ← (uFeldTyp env ty).toOption
    let value ← uKonstWert range.1 range.2 fns values 64 expr
    typedConstants env fns rest (values ++ [(name, value)])
  | _ :: rest, values => typedConstants env fns rest values

/-- Full ordered canonical environments must agree with the typed source declaration fold.
    Also require stability of alias ranges when newly folded constants become visible. -/
def EnvironmentCompatible (source target : List SItemTief) : Prop :=
  let p := prepare source
  let final := uConstsRech (uKonstFns target) target []
  typedConstants p.env p.fns p.expanded [] = some final ∧
    uAliase final p.expanded = p.env

instance (source target : List SItemTief) : Decidable (EnvironmentCompatible source target) := by
  unfold EnvironmentCompatible
  infer_instance

/-- Exact environments used by the downstream canonical elaborator, not merely output values. -/
def EnvironmentFacts (source target : List SItemTief) : Prop :=
  let p := prepare source
  let final := uConstsRech (uKonstFns target) target []
  typedConstants p.env p.fns p.expanded [] = some final ∧
    uAliase final target = p.env ∧
    uAliase p.initial p.expanded = source.foldl (aliasStep p.initial) []

/-- The checked equality supplies accepted-subset preservation; alias declaration collection is
    proved generically at arbitrary final constant environments. This is not total coverage. -/
theorem normalize_environments (items : List SItemTief)
    (h : EnvironmentCompatible items (normalizeAliases items)) :
    EnvironmentFacts items (normalizeAliases items) := by
  obtain ⟨hc, ha⟩ := h
  refine ⟨hc, ?_, ?_⟩
  · change uAliase _ (constants _ _ [] _) = _
    rw [constants_aliases]
    exact ha
  · simpa only [prepare, List.nil_append] using
      aliases_collected (prepare items).initial [] items

end Gabbro.Stage0.Frontend
