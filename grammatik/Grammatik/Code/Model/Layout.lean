import Grammatik.Code.Model.Types

/-
  File:      Grammatik/Code/Model/Layout.lean
  Subject:   TRACK L, PHASE L0/L1 -- FACTS ABOUT THE DATA LAYOUT (`Ty.size`, `Ty.fieldOff`,
             `Ty.gepOff`): the bounds and the non-overlap the lowering proofs need.

    * `roundUp_ge`, `align_pos`, `store_le_size`;
    * `endOff_ge`, `fieldOff_end` -- a field lies inside the chain it belongs to;
    * `fieldOff_disj` -- two different fields of one record do not overlap;
    * `endOff_le_size` -- the chain fits in the record's alloc size;
    * `gepOff_slot` -- the offset `gep [n x R], 0, k, i` computes: `k * size R + offset of field i`.
-/

namespace Gabbro.Code

namespace Ty

variable [Conf]

theorem intAlign_pos (w : Nat) : 0 < intAlign w := by
  have := Conf.wb_pos
  unfold intAlign
  dsimp only
  apply Nat.lt_min.mpr
  refine ⟨?_, by omega⟩
  repeat (first | omega | split)

theorem align_pos : ∀ t : Ty, 0 < t.align := by
  intro t
  induction t with
  | int w => exact intAlign_pos w
  | flt => simp [align]
  | dbl => simp [align]
  | ptr => exact Conf.wb_pos
  | void => simp [align]
  | arr n t ih => exact ih
  | fld t r iht ihr => unfold align; omega
  | unit => simp [align]

theorem roundUp_ge (o a : Nat) (h : 0 < a) : o ≤ roundUp o a := by
  unfold roundUp
  have h1 := Nat.div_add_mod (o + a - 1) a
  have h2 := Nat.mod_lt (o + a - 1) h
  have h3 := Nat.mul_comm a ((o + a - 1) / a)
  generalize (o + a - 1) / a = q at *
  generalize (o + a - 1) % a = r at *
  omega

theorem roundUp_zero (a : Nat) (h : 0 < a) : roundUp 0 a = 0 := by
  unfold roundUp
  have : (0 + a - 1) / a = 0 := Nat.div_eq_of_lt (by omega)
  rw [this, Nat.zero_mul]

theorem store_le_size (t : Ty) (h : t.scalar = true) : t.store ≤ t.size := by
  cases t <;> simp_all [scalar, store, size]
  rename_i w
  exact roundUp_ge _ _ (intAlign_pos w)

theorem endOff_ge : ∀ (c : Ty) (o : Nat), o ≤ endOff c o := by
  intro c
  induction c with
  | fld t r iht ihr =>
      intro o
      unfold endOff
      have := roundUp_ge o t.align (align_pos t)
      have := ihr (roundUp o t.align + t.size)
      omega
  | _ => intro o; unfold endOff; exact Nat.le_refl _

theorem fieldOff_end : ∀ (c : Ty) (i o o' : Nat) (t' : Ty), fieldOff c i o = some (o', t') →
    o ≤ o' ∧ o' + t'.size ≤ endOff c o := by
  intro c
  induction c with
  | fld t r iht ihr =>
      intro i o o' t' h
      cases i with
      | zero =>
          simp only [fieldOff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have h1 := roundUp_ge o t.align (align_pos t)
          have h2 := endOff_ge r (roundUp o t.align + t.size)
          unfold endOff
          exact ⟨h1, h2⟩
      | succ i =>
          simp only [fieldOff] at h
          have ⟨h1, h2⟩ := ihr i _ o' t' h
          have h3 := roundUp_ge o t.align (align_pos t)
          unfold endOff
          exact ⟨by omega, h2⟩
  | _ => intro i o o' t' h; simp [fieldOff] at h

theorem fieldOff_disj : ∀ (c : Ty) (i j o o1 o2 : Nat) (t1 t2 : Ty), i < j →
    fieldOff c i o = some (o1, t1) → fieldOff c j o = some (o2, t2) → o1 + t1.size ≤ o2 := by
  intro c
  induction c with
  | fld t r iht ihr =>
      intro i j o o1 o2 t1 t2 hij h1 h2
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [fieldOff, Option.some.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl⟩ := h1
              simp only [fieldOff] at h2
              have := (fieldOff_end r j _ o2 t2 h2).1
              omega
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [fieldOff] at h1 h2
              exact ihr i j _ o1 o2 t1 t2 (by omega) h1 h2
  | _ => intro i j o o1 o2 t1 t2 _ h1; simp [fieldOff] at h1

theorem endOff_le_size (t : Ty) (r : Ty) : endOff (fld t r) 0 ≤ size (fld t r) := by
  have h := roundUp_zero t.align (align_pos t)
  have h1 : endOff (fld t r) 0 = endOff r (roundUp 0 t.align + t.size) := rfl
  rw [h1, h, Nat.zero_add]
  have h2 : size (fld t r) = roundUp (endOff r (size t)) (max (align t) (align r)) := by
    rw [size]
  rw [h2]
  exact roundUp_ge _ _ (by have := align_pos t; omega)

/-- A field of a record lies inside the record's alloc size. -/
theorem field_in_size (t r : Ty) (i o : Nat) (t' : Ty) (h : fieldOff (fld t r) i 0 = some (o, t')) :
    o + t'.size ≤ size (fld t r) := by
  have := (fieldOff_end _ i 0 o t' h).2
  have h2 := endOff_le_size t r
  omega

/-- The offset `gep [n x R], 0, k, i` computes for a record `R` whose field number `i` sits at
    byte `off`: `k * size R + off`. -/
theorem gepOff_slot (n : Nat) (R : Ty) (k : Int) (i off : Nat) (t' : Ty)
    (h : fieldOff R i 0 = some (off, t')) :
    gepOff (.arr n R) [0, k, (i : Int)] = some (k * (size R : Int) + off, t') := by
  cases R with
  | fld t r =>
      simp [gepOff, gepIn, h]
  | _ => simp [fieldOff] at h

end Ty

end Gabbro.Code
