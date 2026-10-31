import Stage0.Frontend.Functions

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Shared source-derived environments for the two frontend normalization phases. -/
structure Prepared where
  initial : List (String × Int)
  expanded : List SItemTief
  env : List (String × (Int × Int))
  fns : List UKonstFn

def prepare (items : List SItemTief) : Prepared :=
  let initial := uConstsRech (uKonstFns items) items []
  let expanded := aliases initial [] items
  let env := uAliase initial expanded
  ⟨initial, expanded, env, constantFunctions env expanded⟩

/-- Names and visibility have already been resolved by the canonical preprocessing. -/
def normalizeAliases (items : List SItemTief) : List SItemTief :=
  let p := prepare items
  constants p.env p.fns [] p.expanded

/-- Every changed alias declaration preserves its metadata and its canonical type denotation
    in the declaration environment; all other declarations are identical. -/
def AliasEquivalent (env : List (String × (Int × Int))) (source target : SItemTief) : Prop :=
  source = target ∨ ∃ flags name order original body,
    source = .typeT flags name [] order (some (.atom original)) ∧
    target = .typeT flags name [] order (some body) ∧
    uTyp env [] (.atom original) = uTyp env [] body

theorem aliasBody_sound {env : List (String × (Int × Int))} {name : String} {body : STyp}
    (h : aliasBody env name = .ok body) : uTyp env [] (.atom name) = uTyp env [] body := by
  cases ht : uTypName env name with
  | error e =>
    simp only [aliasBody, ht] at h
    change Except.error e = Except.ok body at h
    contradiction
  | ok range =>
    rcases range with ⟨lo, hi⟩
    have hb : body = .range (.atom name) (bound lo) (bound hi) false := by
      simp only [aliasBody, ht] at h
      change Except.ok (.range (.atom name) (bound lo) (bound hi) false) = Except.ok body at h
      exact (Except.ok.inj h).symm
    rw [hb]
    simp [uTyp, ht, bound_correct]

theorem aliasItem_sound (env : List (String × (Int × Int))) (item : SItemTief) :
    AliasEquivalent env item (aliasItem env item) := by
  cases item <;> try exact Or.inl rfl
  case typeT flags name args order body =>
    cases args with
    | cons a rest => exact Or.inl rfl
    | nil =>
      cases body with
      | none => exact Or.inl rfl
      | some ty =>
        cases ty <;> try exact Or.inl rfl
        case atom original =>
          cases hb : aliasBody env original with
          | error e => exact Or.inl (by simp [aliasItem, hb])
          | ok ty =>
            exact Or.inr ⟨flags, name, order, original, ty, rfl,
              by simp [aliasItem, hb], aliasBody_sound hb⟩

/-- A changed constant preserves its name and type and is the exact result of the canonical
    evaluator in its original range and declaration-order environment. -/
def ConstantEquivalent (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (source target : SItemTief) : Prop :=
  source = target ∨ ∃ name ty expr lo hi v,
    source = .constT name ty (.one expr) ∧
    target = .constT name ty (.one (.lit v.toNat)) ∧
    uFeldTyp env ty = .ok (lo, hi) ∧
    uKonstWert lo hi fns values 64 expr = some v ∧ 0 ≤ v

theorem constant_sound (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) :
    ConstantEquivalent env fns values item (constant env fns values item) := by
  cases item <;> try exact Or.inl rfl
  case constT name ty payload =>
    cases payload with
    | rows xs => exact Or.inl rfl
    | one expr =>
      cases ht : uFeldTyp env ty with
      | error e => exact Or.inl (by simp [constant, ht])
      | ok range =>
        rcases range with ⟨lo, hi⟩
        cases he : uKonstWert lo hi fns values 64 expr with
        | none => exact Or.inl (by simp [constant, ht, he])
        | some v =>
          by_cases hv : 0 ≤ v
          · exact Or.inr ⟨name, ty, expr, lo, hi, v, rfl,
              by simp [constant, ht, he, hv], ht, he, hv⟩
          · exact Or.inl (by simp [constant, ht, he, hv])

/-- A compositional derivation of the rewrite, including every intermediate declaration state. -/
inductive Rewrite (meaning : σ → SItemTief → SItemTief → Prop)
    (advance : σ → SItemTief → σ) : σ → List SItemTief → List SItemTief → Prop
  | nil (state) : Rewrite meaning advance state [] []
  | cons {state source target rest output} : meaning state source target →
      Rewrite meaning advance (advance state target) rest output →
      Rewrite meaning advance state (source :: rest) (target :: output)

theorem rewrite_sound (step : σ → SItemTief → SItemTief) (advance : σ → SItemTief → σ)
    (meaning : σ → SItemTief → SItemTief → Prop)
    (sound : ∀ state item, meaning state item (step state item)) (state : σ) (items : List SItemTief) :
    Rewrite meaning advance state items (rewrite step advance state items) := by
  induction items generalizing state with
  | nil => exact .nil state
  | cons item rest ih => exact .cons (sound state item) (ih _)

/-- The complete frontend normalization derivation, before canonical program elaboration. -/
def Normalization (source target : List SItemTief) : Prop :=
  let values := uConstsRech (uKonstFns source) source []
  ∃ expanded,
    Rewrite AliasEquivalent (fun env item => env ++ uAliase values [item]) [] source expanded ∧
    (∀ fn ∈ constantFunctions (uAliase values expanded) expanded,
      ∃ item ∈ expanded, FunctionMeaning (uAliase values expanded) item fn) ∧
    Rewrite (ConstantEquivalent (uAliase values expanded)
      (constantFunctions (uAliase values expanded) expanded))
      (fun collected item => uConstsRech (constantFunctions (uAliase values expanded) expanded) [item] collected)
      [] expanded target

theorem normalizeAliases_sound (items : List SItemTief) :
    Normalization items (normalizeAliases items) := by
  refine ⟨_, rewrite_sound _ _ _ aliasItem_sound [] items, constantFunctions_sound _ _, ?_⟩
  exact rewrite_sound _ _ _ (constant_sound _ _) [] _

/-- The actual compiler consumes this proof-carrying result. Proofs erase during execution. -/
def normalize (items : List SItemTief) : { output // Normalization items output } :=
  ⟨normalizeAliases items, normalizeAliases_sound items⟩

theorem normalizeAliases_sound_zeuge :
    Normalization [.typeT [] "Small" [] [] (some (.atom "u8")),
      .typeT [] "Count" [] [] (some (.atom "Small")),
      .constT "N" (.atom "Count") (.one (.bin "+" (.lit 40) (.lit 2)))]
    (normalizeAliases [.typeT [] "Small" [] [] (some (.atom "u8")),
      .typeT [] "Count" [] [] (some (.atom "Small")),
      .constT "N" (.atom "Count") (.one (.bin "+" (.lit 40) (.lit 2)))]) :=
  normalizeAliases_sound _

end Gabbro.Stage0.Frontend
