module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Kern.Syntax.Syntax.ProduktZucker

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- The real expression lowerer emits the nominal constructor over the complete field list. -/
theorem record_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (identity : Nat) (reordered : Bool) (sides : List (Ty × USide))
    (args : Args (declOf u) Γ Λ (sides.map (·.1)))
    (gate : u.exportGate = .ok ())
    (lowered : lowProductArgs u Γ Λ fn er sides = .ok args)
    (schema : { s : URecord // s.ty = .prod identity (sides.map (·.1)) })
    (hschema : uRecordOf u.records (.prod identity (sides.map (·.1))) = .ok schema) :
    lowWertE u Γ Λ fn er (.product identity reordered sides) =
      .ok ⟨.prod identity (sides.map (·.1)), Expr.prod identity args⟩ := by
  simp only [lowWertE, gate, hschema, lowered, bind, Except.bind]

/-- Empty products use the canonical empty argument list in the same lexical/result scope. -/
theorem lowProductArgs_nil (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) : lowProductArgs u Γ Λ fn er [] = .ok .nil := by
  rw [lowProductArgs]

/-- Product fields use the actual checking-mode lowerer, with no separate callback instance. -/
theorem lowProductArgs_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (side : USide) (rest : List (Ty × USide)) :
    lowProductArgs u Γ Λ fn er ((ty, side) :: rest) = (do
      let head ← lowWertAtE u Γ Λ fn er ty side
      let tail ← lowProductArgs u Γ Λ fn er rest
      pure (.cons head tail)) := by
  rw [lowProductArgs]

/-- Typed literals travel through the same actual literal lowerer in body and contract scopes. -/
theorem typed_literal_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (raw : USide) :
    lowWertE u Γ Λ fn er (.typed ty raw) = (lowLit ty raw).map (⟨ty, ·⟩) := by
  rw [lowWertE]

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
  cases value <;> rw [lowLit]

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

/-- Product projection and replacement use the canonical semantics, with the whole base footprint. -/
theorem record_replace_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {identity : Nat}
    {fs : List Ty} {field : Ty} (entry state : World D) (env : Env D Γ)
    (value : Expr D Γ Λ (.prod identity fs)) (position : FieldAt fs field)
    (replacement : Expr D Γ Λ field) :
    eval entry (Expr.prodSet value position replacement) state env =
      prodSetW position (eval entry value state env) (eval entry replacement state env) ∧
    (Expr.prodSet value position replacement).orte = value.orte ++ replacement.orte := ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.UebersetzeAllg
