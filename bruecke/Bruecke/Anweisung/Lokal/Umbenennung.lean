module
public import Bruecke.Anweisung.Lokal.Namen
@[expose] public section

/-!
# Renaming the scalar Body expressions of the source bridge

Only variable identifiers are renamed. Carrier names, fields and callee entry identifiers
belong to other namespaces. Unsupported Body forms are refused explicitly. This is a
structural operation on compiler data, never an additional execution path.
-/

namespace Gabbro.Bruecke

open Gabbro.Body

/-- Rename free scalar names; the bridge does not produce binding expressions here. -/
def renameScalar (name : String → Option String) : Expr → Option Expr
  | .lit v => some (.lit v)
  | .name x => some (.name ((name x).getD x))
  | .global x => some (.global x)
  | .place c i f => (renameScalar name i).map (fun e => .place c e f)
  | .un op e => (renameScalar name e).map (Expr.un op)
  | .bin op a b =>
      match renameScalar name a, renameScalar name b with
      | some a', some b' => some (.bin op a' b')
      | _, _ => none
  | .hasShape x sh => some (.hasShape ((name x).getD x) sh)
  | _ => none

/-- Pull a runtime binding back to the source-name view consumed by expression lemmas. -/
def visibleBinding (name : String → Option String) (β : Binding) : Binding :=
  fun x => match name x with
    | some id => β id
    | none => β x

/-- A successful renaming evaluates exactly as its source-name projection. -/
theorem eval_renameScalar (name : String → Option String) (s : State) :
    ∀ (e e' : Expr), renameScalar name e = some e' →
      eval s e' = eval ⟨s.world, visibleBinding name s.local'⟩ e
  | .lit v, e', h => by
      simp only [renameScalar, Option.some.injEq] at h
      subst e'
      rfl
  | .name x, e', h => by
      simp only [renameScalar, Option.some.injEq] at h
      subst e'
      cases hn : name x with
      | none => simp only [eval, visibleBinding, hn, Option.getD_none]
      | some id => simp only [eval, visibleBinding, hn, Option.getD_some]
  | .global x, e', h => by
      simp only [renameScalar, Option.some.injEq] at h
      subst e'
      rfl
  | .place c i f, e', h => by
      simp only [renameScalar] at h
      cases hi : renameScalar name i with
      | none => rw [hi] at h; cases h
      | some i' =>
        rw [hi] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst e'
        simp only [eval, eval_renameScalar name s i i' hi]
  | .un op e, e', h => by
      simp only [renameScalar] at h
      cases he : renameScalar name e with
      | none => rw [he] at h; cases h
      | some a =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst e'
        simp only [eval, eval_renameScalar name s e a he]
  | .bin op a b, e', h => by
      simp only [renameScalar] at h
      cases ha : renameScalar name a with
      | none => rw [ha] at h; cases h
      | some a' =>
        rw [ha] at h
        cases hb : renameScalar name b with
        | none => rw [hb] at h; cases h
        | some b' =>
          rw [hb] at h
          simp only [Option.some.injEq] at h
          subst e'
          have hva := eval_renameScalar name s a a' ha
          have hvb := eval_renameScalar name s b b' hb
          cases op <;> simp only [eval, hva, hvb]
  | .hasShape x sh, e', h => by
      simp only [renameScalar, Option.some.injEq] at h
      subst e'
      cases hn : name x with
      | none => simp only [eval, visibleBinding, hn, Option.getD_none]
      | some id => simp only [eval, visibleBinding, hn, Option.getD_some]
  | .someOf _, _, h | .fieldOf _ _, _, h | .forallSlots _ _ _, _, h
  | .existsSlots _ _ _, _, h | .reaches _ _ _ _ _, _, h | .chainFrom _ _ _ _ _, _, h
  | .wrapTo _ _ _, _, h | .tagOf _ _, _, h => by
      cases h

/-- Rename caller expressions while preserving the callee's declared entry scope and precondition. -/
def renameStep (name : String → Option String) : Stmt → Option Stmt
  | .assign c i f v =>
      match renameScalar name i, renameScalar name v with
      | some i', some v' => some (.assign c i' f v')
      | _, _ => none
  | .call c ps es pre => (renameScalars name es).map (fun es' => .call c ps es' pre)
  | _ => none
where
  renameScalars (name : String → Option String) : List Expr → Option (List Expr)
    | [] => some []
    | e :: es =>
        match renameScalar name e, renameScalars name es with
        | some e', some es' => some (e' :: es')
        | _, _ => none

end Gabbro.Bruecke
