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

/-- Materialize a negative integer through the existing builtin-min/add syntax. Every candidate
    is checked in the exact source range and against the actual frozen constant collector. -/
def negative (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (name : String) (ty : STyp) (expr : SExpr)
    (lo hi value : Int) : SItemTief :=
  let original := SItemTief.constT name ty (.one expr)
  match eingebauteInt.find? (fun entry => entry.2 == (lo, hi)) with
  | none => original
  | some (word, _) =>
    let outTy := STyp.atom word
    let outExpr := SExpr.bin "+" (.field (.variable word) "min") (.lit (value - lo).toNat)
    let output := SItemTief.constT name outTy (.one outExpr)
    if (uFeldTyp env outTy).toOption = some (lo, hi) ∧
        uKonstWert lo hi fns values 64 outExpr = some value ∧
        uConstsRech fns [output] values = values ++ [(name, value)] then output else original

/-- Every negative value in a signed builtin range is min plus an in-range nonnegative offset.
    All intermediate checks use the same canonical range; the signed minimum needs no negation. -/
theorem negative_expression_correct (word : String) (lo hi value : Int)
    (fns : List UKonstFn) (values : List (String × Int))
    (hw : uTypName [] word = .ok (lo, hi)) (hs : lo + hi = -1)
    (hv : lo ≤ value ∧ value < 0) :
    uKonstWert lo hi fns values 64
      (.bin "+" (.field (.variable word) "min") (.lit (value - lo).toNat)) = some value := by
  have h0 : 0 ≤ value - lo := by omega
  have h1 : lo ≤ lo ∧ lo ≤ hi := by omega
  have h2 : lo ≤ value - lo ∧ value - lo ≤ hi := by omega
  have h3 : lo ≤ value ∧ value ≤ hi := by omega
  have hsum : lo + (value - lo) = value := by omega
  simp [uKonstWert, hw, h1, h2, h3, hsum, Int.toNat_of_nonneg h0, strEq]

/-- Coverage of every selected signed builtin range, independently of the source alias spelling. -/
theorem negative_materializes (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (name : String) (ty : STyp) (expr : SExpr)
    (word : String) (lo hi value : Int)
    (hf : eingebauteInt.find? (fun entry => entry.2 == (lo, hi)) = some (word, (lo, hi)))
    (hw : uTypName [] word = .ok (lo, hi)) (ht : uFeldTyp env (.atom word) = .ok (lo, hi))
    (hs : lo + hi = -1) (hv : lo ≤ value ∧ value < 0) :
    negative env fns values name ty expr lo hi value =
      .constT name (.atom word)
        (.one (.bin "+" (.field (.variable word) "min") (.lit (value - lo).toNat))) := by
  have he := negative_expression_correct word lo hi value fns values hw hs hv
  have hc : uConstsRech fns
      [.constT name (.atom word)
        (.one (.bin "+" (.field (.variable word) "min") (.lit (value - lo).toNat)))] values =
        values ++ [(name, value)] := by
    simp [uConstsRech, hw, he]
  simp [negative, hf, ht, Except.toOption, he, hc]

/-- A negative candidate either retains the source or preserves its exact canonical range,
    evaluated value and full ordered collector extension. The source type spelling may be an alias. -/
theorem negative_sound (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (name : String) (ty : STyp) (expr : SExpr) (lo hi value : Int) :
    negative env fns values name ty expr lo hi value = .constT name ty (.one expr) ∨
    ∃ outTy outExpr,
      negative env fns values name ty expr lo hi value = .constT name outTy (.one outExpr) ∧
      uFeldTyp env outTy = .ok (lo, hi) ∧
      uKonstWert lo hi fns values 64 outExpr = some value ∧
      uConstsRech fns [.constT name outTy (.one outExpr)] values = values ++ [(name, value)] := by
  unfold negative
  split
  · exact Or.inl rfl
  · rename_i word range hf
    dsimp only
    split
    · rename_i hc
      rcases hc with ⟨ht, he, hv⟩
      have ht' : uFeldTyp env (.atom word) = .ok (lo, hi) := by
        cases hr : uFeldTyp env (.atom word) with
        | error e =>
          rw [hr] at ht
          change none = some (lo, hi) at ht
          contradiction
        | ok r =>
          have hp : r = (lo, hi) := by simpa only [hr, Except.toOption, Option.some.injEq] using ht
          cases hp
          rfl
      exact Or.inr ⟨_, _, rfl, ht', he, hv⟩
    · exact Or.inl rfl

/-- Fold scalar constants at their declared canonical range. A nonnegative result can be
    represented by the frozen elaborator's literal constructor without changing its declared type.
    Negative results use an exact-range builtin-min/add representation when the canonical collector
    can represent them; unsupported ranges retain the original declaration for explicit validation. -/
def constant (env : List (String × (Int × Int))) (fns : List UKonstFn)
    (values : List (String × Int)) (item : SItemTief) : SItemTief :=
  match item with
  | .constT name ty (.one expr) =>
    match uFeldTyp env ty with
    | .ok (lo, hi) =>
      match uKonstWert lo hi fns values 64 expr with
      | some v => if 0 ≤ v then .constT name ty (.one (.lit v.toNat))
          else negative env fns values name ty expr lo hi v
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

/-- Alias spelling and the signed minimum are represented without widening the canonical type. -/
theorem negative_sound_zeuge :
    negative [("Signed", (-128, 127))] [] [] "MIN" (.atom "Signed")
      (.bin "-" (.bin "-" (.lit 0) (.lit 127)) (.lit 1)) (-128) 127 (-128) =
      .constT "MIN" (.atom "i8") (.one (.bin "+" (.field (.variable "i8") "min") (.lit 0))) := by
  rfl

end Gabbro.Stage0.Frontend
