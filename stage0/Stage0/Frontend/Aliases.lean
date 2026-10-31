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

/-- Expand alias chains in declaration order before the frozen elaborator collects aliases.
    Non-alias declarations and unresolved names retain their original canonical handling. -/
def aliases (consts : List (String × Int)) :
    List (String × (Int × Int)) → List SItemTief → List SItemTief
  | _, [] => []
  | env, item :: rest =>
    let item' := match item with
      | .typeT flags name [] order (some (.atom target)) =>
        match aliasBody env target with
        | .ok body => .typeT flags name [] order (some body)
        | .error _ => item
      | _ => item
    item' :: aliases consts (env ++ uAliase consts [item']) rest

/-- Names and visibility have already been resolved by pre108. -/
def normalizeAliases (items : List SItemTief) : List SItemTief :=
  aliases (uConstsRech (uKonstFns items) items []) [] items

end Gabbro.Stage0.Frontend
