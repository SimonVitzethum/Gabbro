module
public import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T2.Teil1Basis
import all Grammatik.Bausteine.Gleitkomma.Gleitkomma.T2.Teil1Basis

public import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T1

@[expose] public section



namespace Gabbro.Grammatik.Gleitkomma
/-- An exact rational strictly inside `2^emax` converts to a finite value. -/
theorem ofRat_finite (F : Format) (hF : 1 ≤ F.emax) (z : Int) (n : Nat)
    (hd : 0 < n) (hob : z.natAbs < n * 2 ^ F.emax) :
    klasse F (ofRat F z n) = .normal ∨ klasse F (ofRat F z n) = .subnormal
      ∨ klasse F (ofRat F z n) = .null :=
  rundeBruch_finite F ⟨z, n⟩ hF hd hob

/-- The dyadic path never has a zero denominator. -/
theorem exaktBruch_nenner_pos (v : Exakt) : 0 < (exaktBruch v).nenner := by
  unfold exaktBruch
  by_cases h : 0 ≤ v.zweierExp
  · rw [if_pos h]
    have e : (⟨v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int), 1⟩ : Bruch).nenner
        = 1 := rfl
    rw [e]; decide
  · rw [if_neg h]
    have e : (⟨v.zaehler, 2 ^ (-v.zweierExp).toNat⟩ : Bruch).nenner
        = 2 ^ (-v.zweierExp).toNat := rfl
    rw [e]; exact Nat.pow_pos (show 0 < 2 by decide)

/-- Addition of finite values with in-range exact sum stays finite
    (and is, by construction, the rounded exact sum). -/
theorem add_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hob : (exaktBruch (exaktAdd u v)).zaehler.natAbs
      < (exaktBruch (exaktAdd u v)).nenner * 2 ^ F.emax) :
    klasse F (add F a b) = .normal ∨ klasse F (add F a b) = .subnormal
      ∨ klasse F (add F a b) = .null := by
  have hmax : 0 < F.bexpMax := by
    have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
    omega
  have hfin : klasse F (rundeExakt F (exaktAdd u v)) = .normal
      ∨ klasse F (rundeExakt F (exaktAdd u v)) = .subnormal
      ∨ klasse F (rundeExakt F (exaktAdd u v)) = .null := by
    unfold rundeExakt
    exact rundeBruch_finite F _ hF (exaktBruch_nenner_pos _) hob
  generalize hka : klasse F a = ka
  generalize hkb : klasse F b = kb
  cases ka <;> cases kb <;>
    first
      | (unfold add; rw [hka, hkb, klasse_null_bits F _ hmax]
         exact Or.inr (Or.inr rfl))
      | (unfold add; rw [hka, hkb, ha, hb]; exact hfin)
      | (have hnone : wertExakt F a = none := by unfold wertExakt; rw [hka]
         rw [hnone] at ha; cases ha)
      | (have hnone : wertExakt F b = none := by unfold wertExakt; rw [hkb]
         rw [hnone] at hb; cases hb)

/-- Multiplication of finite values with in-range exact product stays finite
    (zero times finite is the signed zero, otherwise the rounded product). -/
theorem mul_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hob : (exaktBruch (exaktMul u v)).zaehler.natAbs
      < (exaktBruch (exaktMul u v)).nenner * 2 ^ F.emax) :
    klasse F (mul F a b) = .normal ∨ klasse F (mul F a b) = .subnormal
      ∨ klasse F (mul F a b) = .null := by
  have hmax : 0 < F.bexpMax := by
    have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
    omega
  have hfin : klasse F (rundeExakt F (exaktMul u v)) = .normal
      ∨ klasse F (rundeExakt F (exaktMul u v)) = .subnormal
      ∨ klasse F (rundeExakt F (exaktMul u v)) = .null := by
    unfold rundeExakt
    exact rundeBruch_finite F _ hF (exaktBruch_nenner_pos _) hob
  generalize hka : klasse F a = ka
  generalize hkb : klasse F b = kb
  cases ka <;> cases kb <;>
    first
      | (unfold mul; rw [hka, hkb, klasse_null_bits F _ hmax]
         exact Or.inr (Or.inr rfl))
      | (unfold mul; rw [hka, hkb, ha, hb]; exact hfin)
      | (have hnone : wertExakt F a = none := by unfold wertExakt; rw [hka]
         rw [hnone] at ha; cases ha)
      | (have hnone : wertExakt F b = none := by unfold wertExakt; rw [hkb]
         rw [hnone] at hb; cases hb)

/-- Negation keeps the classification (only the sign bit flips). -/
theorem klasse_neg (F : Format) (a : GBits F) :
    klasse F (neg F a) = klasse F a := by
  cases a with
  | mk s bx fr => unfold neg klasse; rfl

/-- Negation negates the exact value. -/
theorem wertExakt_neg_some (F : Format) (b : GBits F) (v : Exakt)
    (hb : wertExakt F b = some v) :
    wertExakt F (neg F b) = some ⟨-v.zaehler, v.zweierExp⟩ := by
  cases b with
  | mk s bx fr =>
    cases s
    · -- Sign false: negation turns it true.
      have eneg : neg F (⟨false, bx, fr⟩ : GBits F) = ⟨true, bx, fr⟩ := rfl
      rw [eneg]
      have hkn : klasse F (⟨true, bx, fr⟩ : GBits F)
          = klasse F (⟨false, bx, fr⟩ : GBits F) := by
        have h := klasse_neg F (⟨false, bx, fr⟩ : GBits F)
        rwa [eneg] at h
      unfold wertExakt at hb ⊢
      generalize hka : klasse F (⟨false, bx, fr⟩ : GBits F) = ka
      cases ka
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        cases v with
        | mk z e =>
          cases hb
          decide
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at hb
        rw [if_pos trivial] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (-1 : Int) * (fr : Int) = -((1 : Int) * fr) := by omega
          rw [h1]
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at hb
        rw [if_pos trivial] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (-1 : Int) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))
              = -(((1 : Int)) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))) := by omega
          rw [h1]
      · simp only [hka] at hb; cases hb
      · simp only [hka] at hb; cases hb
    · -- Sign true: mirror image.
      have eneg : neg F (⟨true, bx, fr⟩ : GBits F) = ⟨false, bx, fr⟩ := rfl
      rw [eneg]
      have hkn : klasse F (⟨false, bx, fr⟩ : GBits F)
          = klasse F (⟨true, bx, fr⟩ : GBits F) := by
        have h := klasse_neg F (⟨true, bx, fr⟩ : GBits F)
        rwa [eneg] at h
      unfold wertExakt at hb ⊢
      generalize hka : klasse F (⟨true, bx, fr⟩ : GBits F) = ka
      cases ka
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        cases v with
        | mk z e =>
          cases hb
          decide
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_pos trivial] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (1 : Int) * (fr : Int) = -(((-1 : Int)) * fr) := by omega
          rw [h1]
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_pos trivial] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (1 : Int) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))
              = -(((-1 : Int)) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))) := by omega
          rw [h1]
      · simp only [hka] at hb; cases hb
      · simp only [hka] at hb; cases hb

/-- Subtraction of finite values with in-range exact difference stays finite. -/
theorem sub_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hob : (exaktBruch (exaktAdd u ⟨-v.zaehler, v.zweierExp⟩)).zaehler.natAbs
      < (exaktBruch (exaktAdd u ⟨-v.zaehler, v.zweierExp⟩)).nenner * 2 ^ F.emax) :
    klasse F (sub F a b) = .normal ∨ klasse F (sub F a b) = .subnormal
      ∨ klasse F (sub F a b) = .null := by
  unfold sub
  exact add_finite F hF a (neg F b) u ⟨-v.zaehler, v.zweierExp⟩ ha
    (wertExakt_neg_some F b v hb) hob

/-! ## Theorems: the signed-zero rule (IEEE 754-2019 §6.3). -/

/-- The sum of two zeros is `-0` exactly when both are `-0`. -/
theorem add_null_null (F : Format) (a b : GBits F)
    (ha : klasse F a = .null) (hb : klasse F b = .null) :
    add F a b = ⟨a.sign && b.sign, 0, 0⟩ := by
  unfold add; rw [ha, hb]

/-- Exact cancellation of a dyadic value leaves numerator zero. -/
theorem exaktAdd_neg_zaehler (u : Exakt) :
    (exaktAdd u ⟨-u.zaehler, u.zweierExp⟩).zaehler = 0 := by
  unfold exaktAdd
  simp only [Int.le_refl, if_true, Int.sub_self]
  rw [Int.neg_mul]; exact Int.add_right_neg _

/-- An exact zero rounds to `+0` (its numerator is not negative). -/
theorem rundeExakt_null (F : Format) (v : Exakt) (hv : v.zaehler = 0) :
    rundeExakt F v = ⟨false, 0, 0⟩ := by
  have hd := exaktBruch_nenner_pos v
  have hz : (exaktBruch v).zaehler = 0 := by
    unfold exaktBruch
    by_cases h : 0 ≤ v.zweierExp
    · rw [if_pos h]; show v.zaehler * _ = 0; rw [hv, Int.zero_mul]
    · rw [if_neg h]; exact hv
  unfold rundeExakt rundeBruch rundeBruchBei
  rw [if_neg (by omega), hz]
  rfl

/-- `x - x = +0` for every finite `x` (zeros included: `(-0) - (-0) = +0`). -/
theorem sub_selbst (F : Format) (a : GBits F)
    (hk : klasse F a = .normal ∨ klasse F a = .subnormal ∨ klasse F a = .null) :
    sub F a a = ⟨false, 0, 0⟩ := by
  unfold sub
  have hkn := klasse_neg F a
  rcases hk with hk | hk | hk
  · have hw : wertExakt F a = some ⟨(if a.sign then (-1 : Int) else 1)
        * ((2 ^ (F.p - 1) : Nat) + (a.frac : Int)),
        (a.bexp : Int) - (F.bias : Int) - ((F.p : Int) - 1)⟩ := by
      unfold wertExakt; rw [hk]
    have hwn := wertExakt_neg_some F a _ hw
    unfold add; rw [hkn, hk, hw, hwn]
    exact rundeExakt_null F _ (exaktAdd_neg_zaehler _)
  · have hw : wertExakt F a = some ⟨(if a.sign then (-1 : Int) else 1) * (a.frac : Int),
        F.emin - ((F.p : Int) - 1)⟩ := by
      unfold wertExakt; rw [hk]
    have hwn := wertExakt_neg_some F a _ hw
    unfold add; rw [hkn, hk, hw, hwn]
    exact rundeExakt_null F _ (exaktAdd_neg_zaehler _)
  · rw [add_null_null F a (neg F a) hk (by rw [hkn]; exact hk)]
    cases a with
    | mk sg bx fr => cases sg <;> rfl

/-- The exact quotient denominator, exposed (definitionally the `let` body). -/
theorem divBruch_nenner (u v : Exakt) : (divBruch u v).nenner
    = v.zaehler.natAbs
      * 2 ^ (v.zweierExp
        - (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp)).toNat :=
  by rfl

end Gabbro.Grammatik.Gleitkomma
