module

public import Gabbro.Body

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

mutual
/-- Infer literal shapes field by field. Reasons and tagged values still need a target. -/
def literalShape : Value → Option Shape
  | .int n => some (.intIn n n)
  | .bool _ => some .bool
  | .absent | .present _ => some .opt
  | .reason _ | .tagged _ _ => none
  | .record vs => (literalFieldsShape vs).map Shape.record
termination_by structural v => v

def literalFieldsShape : List Value → Option (List Shape)
  | [] => some []
  | v :: vs =>
      match literalShape v, literalFieldsShape vs with
      | some sh, some ss => some (sh :: ss)
      | _, _ => none
termination_by structural vs => vs
end

mutual
theorem literalShape_sicher : ∀ (v : Value) (sh : Shape),
    literalShape v = some sh → v.hasShape sh = true
  | .int n, sh, h => by
      simp only [literalShape, Option.some.injEq] at h
      subst sh
      simp [Value.hasShape]
  | .bool b, sh, h => by
      simp only [literalShape, Option.some.injEq] at h
      subst sh
      rfl
  | .absent, sh, h | .present _, sh, h => by
      simp only [literalShape, Option.some.injEq] at h
      subst sh
      rfl
  | .reason _, _, h | .tagged _ _, _, h => by cases h
  | .record vs, sh, h => by
      simp only [literalShape] at h
      cases hs : literalFieldsShape vs with
      | none => simp only [hs, Option.map_none, reduceCtorEq] at h
      | some ss =>
          simp only [hs, Option.map_some, Option.some.injEq] at h
          subst sh
          obtain ⟨hlen, hf⟩ := literalFieldsShape_sicher vs ss hs
          simp [hlen, hf]
termination_by structural v _ _ => v

theorem literalFieldsShape_sicher : ∀ (vs : List Value) (ss : List Shape),
    literalFieldsShape vs = some ss →
      vs.length = ss.length ∧ Value.fieldsHaveShape vs ss = true
  | [], ss, h => by
      simp only [literalFieldsShape, Option.some.injEq] at h
      subst ss
      exact ⟨rfl, Value.fieldsHaveShape_nil_nil⟩
  | v :: vs, ss, h => by
      simp only [literalFieldsShape] at h
      cases hv : literalShape v with
      | none => simp only [hv, reduceCtorEq] at h
      | some sh =>
          cases ht : literalFieldsShape vs with
          | none => simp only [hv, ht, reduceCtorEq] at h
          | some shapes =>
              simp only [hv, ht, Option.some.injEq] at h
              subst ss
              obtain ⟨hlen, hf⟩ := literalFieldsShape_sicher vs shapes ht
              exact ⟨by simp only [List.length_cons, hlen], by
                simp only [Value.fieldsHaveShape_cons_cons,
                  literalShape_sicher v sh hv, hf, Bool.true_and]⟩
termination_by structural vs _ _ => vs
end

/-- A declared position has a value with precisely that position's shape. -/
theorem fieldsHaveShape_get (vs : List Value) (ss : List Shape) (idx : Nat) (sh : Shape)
    (h : Value.fieldsHaveShape vs ss = true) (hs : ss[idx]? = some sh) :
    ∃ v, vs[idx]? = some v ∧ v.hasShape sh = true := by
  induction vs generalizing ss idx with
  | nil =>
      cases ss with
      | nil => simp at hs
      | cons s ss => simp only [Value.fieldsHaveShape_nil_cons, Bool.false_eq_true] at h
  | cons v vs ih =>
      cases ss with
      | nil => simp only [Value.fieldsHaveShape_cons_nil, Bool.false_eq_true] at h
      | cons s ss =>
          have hh := Bool.and_eq_true_iff.mp h
          cases idx with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
              subst sh
              exact ⟨v, rfl, hh.1⟩
          | succ idx =>
              simp only [List.getElem?_cons_succ] at hs ⊢
              exact ih ss idx hh.2 hs

/-- Replacing both a value and its inferred field shape preserves pointwise typing. -/
theorem fieldsHaveShape_setBoth (vs : List Value) (ss : List Shape) (idx : Nat)
    (v : Value) (sh : Shape) (h : Value.fieldsHaveShape vs ss = true)
    (hv : v.hasShape sh = true) :
    Value.fieldsHaveShape (vs.set idx v) (ss.set idx sh) = true := by
  induction vs generalizing ss idx with
  | nil =>
      cases ss with
      | nil => simp only [List.set_nil, Value.fieldsHaveShape_nil_nil]
      | cons s ss => simp only [Value.fieldsHaveShape_nil_cons, Bool.false_eq_true] at h
  | cons a vs ih =>
      cases ss with
      | nil => simp only [Value.fieldsHaveShape_cons_nil, Bool.false_eq_true] at h
      | cons s ss =>
          have hh := Bool.and_eq_true_iff.mp h
          cases idx with
          | zero =>
              simp only [List.set_cons_zero, Value.fieldsHaveShape_cons_cons,
                hv, hh.2, Bool.true_and]
          | succ idx =>
              simp only [List.set_cons_succ, Value.fieldsHaveShape_cons_cons,
                hh.1, ih ss idx hh.2, Bool.true_and]

end Gabbro.Sicherheit
