import Grammatik.Parser.Elab.UebersetzePipeline

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- A signed bound in the existing canonical range-expression syntax. -/
def bound (v : Int) : SExpr :=
  if 0 ≤ v then .lit v.toNat else .un "-" (.lit (-v).toNat)

/-- Encoding a bound preserves the canonical compile-time integer denotation. -/
theorem bound_correct (env : List (String × (Int × Int))) (v : Int) :
    uSchranke env (bound v) = some v := by
  unfold bound
  split <;> simp [uSchranke, *] <;> omega

/-- Resolve an alias body using already declared aliases, retaining its exact range. The base
    remains the declared name; canonical range semantics depends on its explicit bounds. -/
def aliasBody (env : List (String × (Int × Int))) (name : String) : Except String STyp := do
  let (lo, hi) ← uTypName env name
  pure (.range (.atom name) (bound lo) (bound hi) false)

/-- The adapter elaborates to exactly the canonical type denoted by the alias, including signed
    and arbitrary-width ranges. No ABI representation or arithmetic width is chosen here. -/
theorem aliasBody_correct (env : List (String × (Int × Int))) (tabs : List UTab)
    (name : String) (lo hi : Int) (h : uTypName env name = .ok (lo, hi)) :
    aliasBody env name = .ok (.range (.atom name) (bound lo) (bound hi) false) ∧
    uTyp env tabs (.range (.atom name) (bound lo) (bound hi) false) = .ok (.int lo hi) := by
  constructor
  · simp only [aliasBody, h]
    rfl
  · simp [uTyp, bound_correct]

/-- One alias declaration, expanded using the canonical type denotation of its target. -/
def aliasItem (env : List (String × (Int × Int))) (item : SItemTief) : SItemTief :=
  match item with
  | .typeT flags name [] order (some (.atom target)) =>
    match aliasBody env target with
    | .ok body => .typeT flags name [] order (some body)
    | .error _ => item
  | _ => item

/-- A shared declaration-order rewrite; the state advances using the emitted declaration. -/
def rewrite (step : σ → SItemTief → SItemTief) (advance : σ → SItemTief → σ) :
    σ → List SItemTief → List SItemTief
  | _, [] => []
  | state, item :: rest =>
    let item' := step state item
    item' :: rewrite step advance (advance state item') rest

/-- Expand alias chains without selecting an ABI representation. -/
def aliases (consts : List (String × Int)) :=
  rewrite aliasItem (fun env item => env ++ uAliase consts [item])

/-- Fold scalar constants at their declared canonical range. A nonnegative result can be
    represented by the frozen elaborator's literal constructor without changing its declared type.
    Negative results retain the existing path until a signed literal adapter is available. -/
def constant (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) : SItemTief :=
  match item with
  | .constT name ty (.one expr) =>
    match uFeldTyp env ty with
    | .ok (lo, hi) =>
      match uKonstWert lo hi fns values 64 expr with
      | some v => if 0 ≤ v then .constT name ty (.one (.lit v.toNat)) else item
      | none => item
    | .error _ => item
  | _ => item

/-- Successful folding preserves both the declared type and the exact result of the canonical
    compile-time evaluator; the frozen constant collector receives that same integer. -/
theorem constant_correct (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (name : String) (ty : STyp) (expr : SExpr)
    (lo hi v : Int) (ht : uFeldTyp env ty = .ok (lo, hi))
    (he : uKonstWert lo hi fns values 64 expr = some v) (hv : 0 ≤ v) :
    constant env fns values (.constT name ty (.one expr)) =
      .constT name ty (.one (.lit v.toNat)) ∧
    uConstsRech fns [.constT name ty (.one (.lit v.toNat))] values =
      values ++ [(name, v)] := by
  constructor
  · simp [constant, ht, he, hv]
  · simp [uConstsRech, Int.toNat_of_nonneg hv]

/-- Constants are evaluated in declaration order; function bodies use the existing canonical
    const-function evaluator. Failed evaluation retains the original refusal behavior. -/
def constants (env : List (String × (Int × Int))) (fns : List UKonstFn) :=
  rewrite (constant env fns) (fun values item => uConstsRech fns [item] values)

theorem aliasBody_correct_zeuge :
    aliasBody [("Small", (-4, 9))] "Small" =
      .ok (.range (.atom "Small") (bound (-4)) (bound 9) false) ∧
    uTyp [("Small", (-4, 9))] []
      (.range (.atom "Small") (bound (-4)) (bound 9) false) = .ok (.int (-4) 9) :=
  aliasBody_correct _ _ _ _ _ (by rfl)

theorem constant_correct_zeuge :
    constant [("Small", (0, 100))] [] []
      (.constT "N" (.atom "Small") (.one (.bin "+" (.lit 40) (.lit 2)))) =
      .constT "N" (.atom "Small") (.one (.lit 42)) ∧
    uConstsRech [] [.constT "N" (.atom "Small") (.one (.lit 42))] [] = [("N", 42)] :=
  constant_correct _ _ _ _ _ _ 0 100 42 (by rfl) (by rfl) (by decide)

end Gabbro.Stage0.Frontend
