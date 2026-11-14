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

mutual
/-- Rename free value names, including all positional record fields. -/
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
  | .recOf es => (renameScalarFields name es).map Expr.recOf
  | .recGet e i => (renameScalar name e).map (fun e' => .recGet e' i)
  | .recSet e i v => do
      let e' ← renameScalar name e
      let v' ← renameScalar name v
      pure (.recSet e' i v')
  | _ => none

termination_by e => 3 * sizeOf e
decreasing_by all_goals (simp_wf <;> omega)

def renameScalarFields (name : String → Option String) : List Expr → Option (List Expr)
  | [] => some []
  | e :: es => do
      let e' ← renameScalar name e
      let es' ← renameScalarFields name es
      pure (e' :: es')
termination_by es => 3 * sizeOf es + 1
decreasing_by all_goals (simp_wf <;> omega)
end

/-- Pull a runtime binding back to the source-name view consumed by expression lemmas. -/
def visibleBinding (name : String → Option String) (β : Binding) : Binding :=
  fun x => match name x with
    | some id => β id
    | none => β x

mutual
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
  | .recOf es, e', h => by
      cases hr : renameScalarFields name es with
      | none => simp [renameScalar, hr] at h
      | some es' =>
          simp only [renameScalar, hr, Option.map_some, Option.some.injEq] at h
          subst e'
          rw [eval_recOf, eval_recOf, eval_renameScalarFields name s es es' hr]
  | .recGet e i, e', h => by
      cases hr : renameScalar name e with
      | none => simp [renameScalar, hr] at h
      | some base =>
          simp only [renameScalar, hr, Option.map_some, Option.some.injEq] at h
          subst e'
          simp only [eval, eval_renameScalar name s e base hr]
  | .recSet e i v, e', h => by
      cases hr : renameScalar name e with
      | none => simp [renameScalar, hr] at h
      | some base =>
          cases hv : renameScalar name v with
          | none => simp [renameScalar, hr, hv] at h
          | some val =>
              simp only [renameScalar, hr, hv, bind, Option.bind, pure, Option.some.injEq] at h
              subst e'
              simp only [eval, eval_renameScalar name s e base hr, eval_renameScalar name s v val hv]
  | .someOf _, _, h | .fieldOf _ _, _, h | .forallSlots _ _ _, _, h
  | .existsSlots _ _ _, _, h | .reaches _ _ _ _ _, _, h | .chainFrom _ _ _ _ _, _, h
  | .wrapTo _ _ _, _, h | .tagOf _ _, _, h => by
      simp only [renameScalar] at h
      cases h

termination_by e _ _ => 3 * sizeOf e
decreasing_by all_goals (simp_wf <;> omega)

theorem eval_renameScalarFields (name : String → Option String) (s : State) :
    ∀ (es es' : List Expr), renameScalarFields name es = some es' →
      evalAll s es' = evalAll ⟨s.world, visibleBinding name s.local'⟩ es
  | [], es', h => by
      simp only [renameScalarFields, Option.some.injEq] at h
      subst es'
      rfl
  | e :: es, es', h => by
      cases hr : renameScalar name e with
      | none => simp [renameScalarFields, hr] at h
      | some e' =>
          cases hrs : renameScalarFields name es with
          | none => simp [renameScalarFields, hr, hrs] at h
          | some tail =>
              simp only [renameScalarFields, hr, hrs, bind, Option.bind, pure, Option.some.injEq] at h
              subst es'
              simp only [evalAll, eval_renameScalar name s e e' hr,
                eval_renameScalarFields name s es tail hrs]
termination_by es _ _ => 3 * sizeOf es + 1
decreasing_by all_goals (simp_wf <;> omega)
end

/-- Rename caller expressions while preserving the callee's declared entry scope and precondition. -/
def renameStep (name : String → Option String) : Stmt → Option Stmt
  | .assign c i f v =>
      match renameScalar name i, renameScalar name v with
      | some i', some v' => some (.assign c i' f v')
      | _, _ => none
  | .assignGlobal g v => (renameScalar name v).map (Stmt.assignGlobal g)
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
