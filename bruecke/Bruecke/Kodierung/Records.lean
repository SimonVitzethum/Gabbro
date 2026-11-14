module
public import Bruecke.Kodierung.Teil2
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik

@[simp] theorem valOf_prod {D : Deklaration} (id : Nat) (fs : List Ty)
    (v : Wert D (.prod id fs)) : valOf (.prod id fs) v = .record (valOfProd fs v) := by
  rw [valOf]

@[simp] theorem valOfProd_length {D : Deklaration} : ∀ (fs : List Ty)
    (v : ProdVal D.Fn D.passt fs), (valOfProd fs v).length = fs.length
  | [], _ => rfl
  | _ :: fs, v => by simp only [valOfProd, List.length_cons, valOfProd_length fs (ProdVal.tl v)]

theorem recordIndex_lt {fs : List Ty} {ty : Ty} (i : FieldAt fs ty) : recordIndex i < fs.length := by
  induction i with
  | head => simp [recordIndex]
  | tail i ih => simpa only [recordIndex, List.length_cons, Nat.succ_lt_succ_iff] using ih

/-- The erased index selects exactly the typed G field. No bounds premise is assumed. -/
theorem valOfProd_get {D : Deklaration} {fs : List Ty} {ty : Ty} (i : FieldAt fs ty)
    (v : ProdVal D.Fn D.passt fs) :
    (valOfProd fs v)[recordIndex i]? = some (valOf ty (prodGetW i v)) := by
  induction i with
  | head => rfl
  | tail i ih => exact ih (ProdVal.tl v)

/-- A typed G replacement is precisely the Body list replacement at the erased index. -/
theorem valOfProd_set {D : Deklaration} {fs : List Ty} {ty : Ty} (i : FieldAt fs ty)
    (v : ProdVal D.Fn D.passt fs) (x : Wert D ty) :
    valOfProd fs (prodSetW i v x) = (valOfProd fs v).set (recordIndex i) (valOf ty x) := by
  induction i with
  | head => rfl
  | tail i ih =>
      simp only [prodSetW, valOfProd, recordIndex, List.set_cons_succ]
      exact congrArg (List.cons _) (ih (ProdVal.tl v) x)

mutual
/-- Every representable typed value has its computed Body shape. -/
theorem valOf_shape {D : Deklaration} (ty : Ty) (v : Wert D ty) (sh : Gabbro.Body.Shape)
    (h : shapeOfTy ty = some sh) : (valOf ty v).hasShape sh = true := by
  match ty, v, h with
  | .int lo hi, v, h =>
      simp only [shapeOfTy, Option.some.injEq] at h
      subst sh
      simp [valOf_int, Gabbro.Body.Value.hasShape, v.lo_le, v.le_hi]
  | .bool, v, h =>
      simp only [shapeOfTy, Option.some.injEq] at h
      subst sh
      rfl
  | .prod id fs, v, h =>
      cases hs : shapesOfTys fs with
      | none => simp [shapeOfTy, hs] at h
      | some ss =>
          simp only [shapeOfTy, hs, Option.map_some, Option.some.injEq] at h
          subst sh
          obtain ⟨hlen, hf⟩ := valOfProd_shape fs v ss hs
          simp [valOf_prod, Gabbro.Body.Value.hasShape_record_record, hlen, hf]
  | .opt _, _, h | .sum _, _, h | .why _, _, h | .never, _, h | .fl _ _, _, h
  | .fnptr _, _, h | .ptr _, _, h | .ref _, _, h | .arr _ _, _, h | .str _, _, h =>
      simp [shapeOfTy] at h
termination_by sizeOf ty
decreasing_by all_goals (simp_wf <;> omega)

theorem valOfProd_shape {D : Deklaration} (fs : List Ty) (v : ProdVal D.Fn D.passt fs)
    (ss : List Gabbro.Body.Shape) (h : shapesOfTys fs = some ss) :
    (valOfProd fs v).length = ss.length ∧
      Gabbro.Body.Value.fieldsHaveShape (valOfProd fs v) ss = true := by
  match fs, v, h with
  | [], _, h =>
      simp only [shapesOfTys, Option.some.injEq] at h
      subst ss
      exact ⟨rfl, rfl⟩
  | ty :: fs, v, h =>
      cases ht : shapeOfTy ty with
      | none => simp [shapesOfTys, ht] at h
      | some sh =>
          cases hs : shapesOfTys fs with
          | none => simp [shapesOfTys, ht, hs] at h
          | some rest =>
              simp only [shapesOfTys, ht, hs, bind, Option.bind, pure, Option.some.injEq] at h
              subst ss
              obtain ⟨hlen, hf⟩ := valOfProd_shape fs (ProdVal.tl v) rest hs
              constructor
              · simpa only [valOfProd, List.length_cons] using congrArg Nat.succ hlen
              · simp only [valOfProd, Gabbro.Body.Value.fieldsHaveShape_cons_cons,
                  valOf_shape ty (ProdVal.hd v) sh ht, hf, Bool.true_and]
termination_by sizeOf fs
decreasing_by all_goals (simp_wf <;> omega)
end

/-- Transport a positional environment read to its known source type. -/
theorem nthVal_shape {D : Deklaration} : ∀ {Γ : Ctx} (ρ : Env D Γ) (j : Nat)
    (ty : Ty) (sh : Gabbro.Body.Shape), Γ[j]? = some ty → shapeOfTy ty = some sh →
      (nthVal ρ j).hasShape sh = true
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons v ρ, 0, ty, sh, h, hs => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst ty
      exact valOf_shape _ v sh hs
  | _, .cons _ ρ, j + 1, ty, sh, h, hs => nthVal_shape ρ j ty sh h hs

/-- The canonical option bound is preserved in G; Body entry checks its value constructor. -/
theorem valOf_entryShape {D : Deklaration} (ty : Ty) (v : Wert D ty)
    (sh : Gabbro.Body.Shape) (h : entryShapeOfTy ty = some sh) :
    (valOf ty v).hasShape sh = true := by
  cases ty with
  | opt n =>
    simp only [entryShapeOfTy, Option.some.injEq] at h
    subst sh
    cases v <;> rfl
  | sum cs =>
    simp only [entryShapeOfTy, Option.some.injEq] at h
    subst sh
    change Gabbro.Body.Shape.caseOk _ (caseLabel v.1.val) none = true
    apply List.any_eq_true.mpr
    refine ⟨(caseLabel v.1.val, none), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨v.1.val, List.mem_range.mpr v.1.isLt, rfl⟩
    · simp only [Gabbro.Body.Shape.payloadOk, beq_self_eq_true, Bool.true_and]
  | _ => exact valOf_shape _ v sh h

theorem nthVal_entryShape {D : Deklaration} : ∀ {Γ : Ctx} (ρ : Env D Γ) (j : Nat)
    (ty : Ty) (sh : Gabbro.Body.Shape), Γ[j]? = some ty → entryShapeOfTy ty = some sh →
      (nthVal ρ j).hasShape sh = true
  | _, .nil, _, _, _, h, _ => by simp at h
  | _, .cons v ρ, 0, ty, sh, h, hs => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst ty
      exact valOf_entryShape _ v sh hs
  | _, .cons _ ρ, j + 1, ty, sh, h, hs => nthVal_entryShape ρ j ty sh h hs

end Gabbro.Bruecke
