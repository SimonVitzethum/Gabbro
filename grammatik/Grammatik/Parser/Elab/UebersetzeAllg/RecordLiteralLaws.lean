module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- Fitting a synthesized aggregate keeps its exact type. Array literals
    with a checking-only rule are outside this bridge. -/
theorem lowWertE_aggregate_of_fit {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {source : USide} {target : Ty}
    (aggregate : (∃ n fields, target = .prod n fields) ∨ (∃ ty count, target = .arr ty count))
    (bySynthesis : lowWertAtE u Γ Λ fn er target source =
      (lowWertE u Γ Λ fn er source).bind (fitW target))
    {term : Expr (declOf u) Γ Λ target} (accepted : lowWertAtE u Γ Λ fn er target source = .ok term) :
    ∃ expression, lowWertE u Γ Λ fn er source = .ok ⟨target, expression⟩ := by
  rw [bySynthesis] at accepted
  cases read : lowWertE u Γ Λ fn er source with
  | error diagnostic => simp only [read, Except.bind] at accepted; cases accepted
  | ok value =>
    obtain ⟨ty, expression⟩ := value
    simp only [read, Except.bind, fitW] at accepted
    split at accepted
    · next equal =>
      change ty = target at equal
      subst ty
      exact ⟨expression, rfl⟩
    · rcases aggregate with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases ty <;> cases accepted

/-- Nominal literal construction retains every identity, schema and field-type check. -/
theorem lowLit_product (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (identity actual : Nat) (fields : List Ty) (reordered : Bool) (values : List (Ty × USide)) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) (.prod identity fields) (.product actual reordered values) = (do
      if identity != actual then throw "source export: constant has a foreign record identity"
      let _ ← uRecordOf u.records (.prod identity fields)
      let args ← lowLitFields fields values
      pure (.prod identity args)) := by
  rw [lowLit]

theorem lowLit_bool (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (value : Bool) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) .bool (.truth value) =
      .ok (if value then Expr.tru else Expr.fls) := by
  cases value <;> simp only [lowLit, Bool.false_eq_true, ↓reduceIte]

/-- The literal field helper also checks the carried field type before its recursive step. -/
theorem lowLitFields_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (ty actual : Ty) (fields : List Ty) (value : USide) (values : List (Ty × USide)) :
    lowLitFields (u := u) (Γ := Γ) (Λ := Λ) (ty :: fields) ((actual, value) :: values) = (do
      if ty != actual then throw "source export: constant record field has a foreign type"
      let head ← lowLit ty value
      let tail ← lowLitFields fields values
      pure (.cons head tail)) := by
  rw [lowLitFields]

theorem lowLitFields_nil (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) :
    lowLitFields (u := u) (Γ := Γ) (Λ := Λ) [] [] = .ok .nil := by
  rw [lowLitFields]

/-- Nested literal arrays recurse through the same product-aware literal producer. -/
theorem lowLit_array_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (ty : Ty) (count : Nat) (head tail : USide) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) (.arr ty (count + 1)) (.arrCons head tail) =
      (match lowLit ty head, lowLit (.arr ty count) tail with
       | .ok first, .ok rest => .ok (Expr.arrCons first rest)
       | .error error, _ | _, .error error => .error error) := by
  rw [lowLit]
  cases lowLit (u := u) (Γ := Γ) (Λ := Λ) ty head <;>
    cases lowLit (u := u) (Γ := Γ) (Λ := Λ) (.arr ty count) tail <;> rfl

/-- Product projection and replacement use the canonical semantics, with the whole base footprint. -/
theorem record_replace_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {identity : Nat}
    {fs : List Ty} {field : Ty} (entry state : World D) (env : Env D Γ)
    (value : Expr D Γ Λ (.prod identity fs)) (position : FieldAt fs field)
    (replacement : Expr D Γ Λ field) :
    eval entry (Expr.prodSet value position replacement) state env =
      prodSetW position (eval entry value state env) (eval entry replacement state env) ∧
    (Expr.prodSet value position replacement).orte = value.orte ++ replacement.orte := ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.UebersetzeAllg
