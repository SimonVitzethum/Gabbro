/- Part 2 of 3 of `Gleitkomma` (split by instrumente/teile/lean-teilen.py; the umbrella `Gleitkomma.lean` imports all parts). -/
import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T1

namespace Gabbro.Grammatik.Gleitkomma

/-- Lower bound: the bit length is tight up to one bit (`2 ^ bitlen ≤ 2 * n`). -/
theorem bitlenAux_untere (fuel n : Nat) (hn : n ≠ 0) :
    2 ^ (bitlenAux n fuel) ≤ 2 * n := by
  induction fuel generalizing n with
  | zero =>
    rw [bitlenAux_null]
    have e0 : (2 : Nat) ^ 0 = 1 := rfl
    omega
  | succ fuel ih =>
    rw [bitlenAux_succ]
    by_cases hn0 : n = 0
    · subst hn0; exact (hn rfl).elim
    · simp only [hn0, if_false]
      by_cases hh : n / 2 = 0
      · have hn1 : n = 1 := by omega
        subst hn1
        have e0 : (1 : Nat) / 2 = 0 := by decide
        rw [e0, bitlenAux_null_all]
        decide
      · have ih' := ih (n / 2) hh
        have e2 := zweiHoch_succ (bitlenAux (n / 2) fuel)
        have hmod := Nat.div_add_mod n 2
        omega

theorem bitlen_obere (n : Nat) : n < 2 ^ (bitlen n) :=
  bitlenAux_obere n n Nat.lt_two_pow_self

theorem bitlen_untere (n : Nat) (hn : n ≠ 0) : 2 ^ (bitlen n) ≤ 2 * n :=
  bitlenAux_untere n n hn

/-- Lower bound at non-negative exponents: with `E0 = bn - bd` over
    bit-length bounds (`2^bn ≤ 2n`, `d < 2^bd`), the decided exponent
    satisfies `d * 2^E ≤ n`. The `E0 - 1` arm (branch miss) is covered by
    halving the bit-length upper bound. -/
theorem findeExpBei_unten_nonneg (n d : Nat) (E0 : Int) (bn bd : Nat)
    (hE0 : E0 = (bn : Int) - (bd : Int))
    (hnB : 2 ^ bn ≤ 2 * n) (hdB : d < 2 ^ bd)
    (hE : 0 ≤ findeExpBei n d E0) : d * 2 ^ (findeExpBei n d E0).toNat ≤ n := by
  unfold findeExpBei at hE ⊢
  by_cases h0 : (0 : Int) ≤ E0
  · rw [if_pos h0] at hE ⊢
    by_cases hc : d * 2 ^ E0.toNat ≤ n
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc] at hE ⊢
      have hE0n : E0.toNat = bn - bd := by omega
      have hE1n : (E0 - 1).toNat = E0.toNat - 1 := by omega
      have hE1' : E0.toNat = 1 + (E0.toNat - 1) := by omega
      have hsplit2 : 2 ^ E0.toNat = 2 * 2 ^ (E0.toNat - 1) := by
        have hcong := congrArg (2 ^ ·) hE1'
        rw [zweiHoch_succ] at hcong
        exact hcong
      have hbn : bn = E0.toNat + bd := by omega
      have hpow : 2 ^ bn = 2 ^ E0.toNat * 2 ^ bd := by
        rw [hbn, Nat.pow_add]
      have hcomm : 2 ^ bd * 2 ^ E0.toNat = 2 ^ E0.toNat * 2 ^ bd :=
        Nat.mul_comm _ _
      have hleY : d * 2 ^ E0.toNat ≤ 2 * n := by
        have h1 := Nat.mul_le_mul (Nat.le_of_lt hdB) (Nat.le_refl (2 ^ E0.toNat))
        omega
      have hdm : d * 2 ^ E0.toNat = 2 * (d * 2 ^ (E0.toNat - 1)) := by
        rw [hsplit2, Nat.mul_left_comm]
      rw [hE1n]
      omega
  · rw [if_neg h0] at hE ⊢
    by_cases hc : d ≤ n * 2 ^ (-E0).toNat
    · rw [if_pos hc] at hE; omega
    · rw [if_neg hc] at hE; omega

/-- The decided exponent lower-bounds the quotient at non-negative values. -/
theorem findeExp_unten (n d : Nat) (hn : 0 < n)
    (hE : 0 ≤ findeExp n d) : d * 2 ^ (findeExp n d).toNat ≤ n := by
  unfold findeExp at hE ⊢
  exact findeExpBei_unten_nonneg n d ((bitlen n : Int) - (bitlen d : Int))
    (bitlen n) (bitlen d) rfl
    (bitlen_untere n (by omega)) (bitlen_obere d) hE

/-! ## Theorems: conversions and ops on in-range exact values stay finite. -/

/-- Zero bits classify as zero (needs a non-degenerate exponent field). -/
theorem klasse_null_bits (F : Format) (s : Bool) (hmax : 0 < F.bexpMax) :
    klasse F ⟨s, 0, 0⟩ = .null := by
  have e : (⟨s, 0, 0⟩ : GBits F).bexp = 0 := rfl
  have f : (⟨s, 0, 0⟩ : GBits F).frac = 0 := rfl
  unfold klasse
  rw [e, f, if_neg (by omega : ¬ (0 : Nat) = F.bexpMax), if_pos rfl, if_pos rfl]

/-- Nonzero significand at biased exponent zero is subnormal. -/
theorem klasse_subnormal_bits (F : Format) (s : Bool) (q : Nat)
    (hmax : 0 < F.bexpMax) (hq : q ≠ 0) :
    klasse F ⟨s, 0, q⟩ = .subnormal := by
  have e : (⟨s, 0, q⟩ : GBits F).bexp = 0 := rfl
  have f : (⟨s, 0, q⟩ : GBits F).frac = q := rfl
  unfold klasse
  rw [e, f, if_neg (by omega : ¬ (0 : Nat) = F.bexpMax), if_pos rfl, if_neg hq]

/-- A biased exponent strictly between zero and all-ones is normal. -/
theorem klasse_normal_bits (F : Format) (s : Bool) (bx fr : Nat)
    (hb0 : bx ≠ 0) (hbmax : bx < F.bexpMax) :
    klasse F ⟨s, bx, fr⟩ = .normal := by
  have e : (⟨s, bx, fr⟩ : GBits F).bexp = bx := rfl
  unfold klasse
  rw [e, if_neg (by omega : ¬ bx = F.bexpMax), if_neg hb0]

/-- Rounding a strictly in-range exact value stays finite: with `0 < den`
    and `|num| < den * 2^emax` (and a non-degenerate format), the result is
    normal, subnormal or zero -- never infinity or NaN. -/
theorem rundeBruch_finite (F : Format) (b : Bruch) (hF : 1 ≤ F.emax)
    (hd : 0 < b.nenner)
    (hob : b.zaehler.natAbs < b.nenner * 2 ^ F.emax) :
    klasse F (rundeBruch F b) = .normal
      ∨ klasse F (rundeBruch F b) = .subnormal
      ∨ klasse F (rundeBruch F b) = .null := by
  have hemin : F.emin = 1 - (F.emax : Int) := rfl
  have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
  have hmax : 0 < F.bexpMax := by omega
  unfold rundeBruch rundeBruchBei
  rw [if_neg (by omega : ¬ b.nenner = 0)]
  by_cases hn0 : b.zaehler.natAbs = 0
  · rw [if_pos hn0, klasse_null_bits F _ hmax]
    exact Or.inr (Or.inr rfl)
  · rw [if_neg hn0]
    have hn : 0 < b.zaehler.natAbs := Nat.pos_of_ne_zero hn0
    have hEle : findeExp b.zaehler.natAbs b.nenner ≤ (F.emax : Int) - 1 := by
      by_cases hE0 : 0 ≤ findeExp b.zaehler.natAbs b.nenner
      · by_cases hmaxl : (F.emax : Int) ≤ findeExp b.zaehler.natAbs b.nenner
        · have hlow := findeExp_unten _ _ hn hE0
          have hto : F.emax ≤ (findeExp b.zaehler.natAbs b.nenner).toNat := by omega
          have hmono := Nat.pow_le_pow_right (show 0 < 2 by decide) hto
          have hmul := Nat.mul_le_mul (Nat.le_refl b.nenner) hmono
          omega
        · omega
      · omega
    unfold rundeBruchKern
    rw [if_neg (by omega : ¬ (F.emax : Int) < findeExp b.zaehler.natAbs b.nenner)]
    by_cases hdeep : findeExp b.zaehler.natAbs b.nenner < F.emin - (F.p : Int)
    · rw [if_pos hdeep, klasse_null_bits F _ hmax]
      exact Or.inr (Or.inr rfl)
    · rw [if_neg hdeep]
      by_cases hEmin : F.emin ≤ findeExp b.zaehler.natAbs b.nenner
      · rw [if_pos hEmin]
        by_cases hq : normQ F.p (findeExp b.zaehler.natAbs b.nenner)
            b.zaehler.natAbs b.nenner < 2 ^ F.p
        · rw [if_pos hq]
          have hb0 : (findeExp b.zaehler.natAbs b.nenner - F.emin + 1).toNat ≠ 0 := by omega
          have hbmax : (findeExp b.zaehler.natAbs b.nenner - F.emin + 1).toNat
              < F.bexpMax := by omega
          rw [klasse_normal_bits F _ _ _ hb0 hbmax]
          exact Or.inl rfl
        · rw [if_neg hq]
          by_cases hEmax : findeExp b.zaehler.natAbs b.nenner < (F.emax : Int)
          · rw [if_pos hEmax]
            have hb0 : (findeExp b.zaehler.natAbs b.nenner - F.emin + 2).toNat ≠ 0 := by omega
            have hbmax : (findeExp b.zaehler.natAbs b.nenner - F.emin + 2).toNat
                < F.bexpMax := by omega
            rw [klasse_normal_bits F _ _ _ hb0 hbmax]
            exact Or.inl rfl
          · have hlt : findeExp b.zaehler.natAbs b.nenner < (F.emax : Int) := by omega
            exact (hEmax hlt).elim
      · rw [if_neg hEmin]
        by_cases hsub : subQ F b.zaehler.natAbs b.nenner < 2 ^ (F.p - 1)
        · rw [if_pos hsub]
          by_cases hq0 : subQ F b.zaehler.natAbs b.nenner = 0
          · rw [hq0, klasse_null_bits F _ hmax]
            exact Or.inr (Or.inr rfl)
          · rw [klasse_subnormal_bits F _ _ hmax hq0]
            exact Or.inr (Or.inl rfl)
        · rw [if_neg hsub]
          have hbmax : (1 : Nat) < F.bexpMax := by omega
          rw [klasse_normal_bits F _ 1 0 (by omega) hbmax]
          exact Or.inl rfl

/-! ## Conversions through the finite rounding path. -/

/-- Integers convert through the dyadic path with denominator one. -/
theorem ofInt_bruch (F : Format) (z : Int) :
    ofInt F z = rundeBruch F ⟨z, 1⟩ := by
  have e1 : (⟨z, (0 : Int)⟩ : Exakt).zweierExp = 0 := rfl
  have e2 : (⟨z, (0 : Int)⟩ : Exakt).zaehler = z := rfl
  have t0 : (0 : Int).toNat = 0 := rfl
  have p0 : (2 : Nat) ^ (0 : Nat) = 1 := rfl
  unfold ofInt rundeExakt exaktBruch
  rw [e1, e2, t0, p0, if_pos (by omega : (0 : Int) ≤ 0)]
  have m1 : z * ((1 : Nat) : Int) = z := Int.mul_one z
  rw [m1]

/-- An integer strictly inside `2^emax` converts to a finite value. -/
theorem ofInt_finite (F : Format) (hF : 1 ≤ F.emax) (z : Int)
    (h : z.natAbs < 2 ^ F.emax) :
    klasse F (ofInt F z) = .normal ∨ klasse F (ofInt F z) = .subnormal
      ∨ klasse F (ofInt F z) = .null := by
  rw [ofInt_bruch]
  have ez : (⟨z, (1 : Nat)⟩ : Bruch).zaehler = z := rfl
  have en : (⟨z, (1 : Nat)⟩ : Bruch).nenner = 1 := rfl
  have hd1 : 0 < (⟨z, (1 : Nat)⟩ : Bruch).nenner := by omega
  have hob1 : (⟨z, (1 : Nat)⟩ : Bruch).zaehler.natAbs
      < (⟨z, (1 : Nat)⟩ : Bruch).nenner * 2 ^ F.emax := by
    rw [ez, en]; omega
  exact rundeBruch_finite F ⟨z, 1⟩ hF hd1 hob1

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
  rfl

/-- Division of finite values by a nonzero finite divisor with in-range
    exact quotient stays finite (and is the rounded exact quotient).
    `0 / 0` is NaN, so the divisor must be nonzero (`hkb`, `hv`). -/
theorem div_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hkb : klasse F b = .normal ∨ klasse F b = .subnormal)
    (hv : v.zaehler ≠ 0)
    (hob : (divBruch u v).zaehler.natAbs
      < (divBruch u v).nenner * 2 ^ F.emax) :
    klasse F (div F a b) = .normal ∨ klasse F (div F a b) = .subnormal
      ∨ klasse F (div F a b) = .null := by
  have hmax : 0 < F.bexpMax := by
    have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
    omega
  have hdD : 0 < (divBruch u v).nenner := by
    rw [divBruch_nenner]
    have h1 : 0 < v.zaehler.natAbs := by omega
    have h2 : 0 < 2 ^ (v.zweierExp
        - (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp)).toNat :=
      Nat.pow_pos (show 0 < 2 by decide)
    exact Nat.mul_pos h1 h2
  have hfin : klasse F (rundeBruch F (divBruch u v)) = .normal
      ∨ klasse F (rundeBruch F (divBruch u v)) = .subnormal
      ∨ klasse F (rundeBruch F (divBruch u v)) = .null :=
    rundeBruch_finite F _ hF hdD hob
  generalize hka : klasse F a = ka
  cases hkb with
  | inl hkb =>
    cases ka <;>
      first
        | (unfold div; rw [hka, hkb, klasse_null_bits F _ hmax]
           exact Or.inr (Or.inr rfl))
        | (unfold div; rw [hka, hkb, ha, hb]; exact hfin)
        | (have hnone : wertExakt F a = none := by
             unfold wertExakt; simp only [hka]
           rw [hnone] at ha; cases ha)
  | inr hkb =>
    cases ka <;>
      first
        | (unfold div; rw [hka, hkb, klasse_null_bits F _ hmax]
           exact Or.inr (Or.inr rfl))
        | (unfold div; rw [hka, hkb, ha, hb]; exact hfin)
        | (have hnone : wertExakt F a = none := by
             unfold wertExakt; simp only [hka]
           rw [hnone] at ha; cases ha)

/-! ## Witnesses: concrete vectors by `decide`.

  Every vector below is a kernel computation (`decide`/`rfl`-checkable,
  no `native_decide`): the model rounds exactly like IEEE-754 hardware on
  fractions, ties, subnormals and overflow. The subnormal/overflow vectors
  evaluate `2 ^ 1074`-scale naturals through ~1100 structural steps, past
  both default elaborator limits, hence the two options (elaboration-only,
  no soundness content). -/

set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
theorem zeuge_ebits32 : f32.ebits = 8 := by decide

theorem zeuge_ebits64 : f64.ebits = 11 := by decide

theorem zeuge_zehntel64 :
    zuBits f64 (ofRat f64 1 10) = 0x3FB999999999999A := by decide

theorem zeuge_zweiZehntel64 :
    zuBits f64 (ofRat f64 2 10) = 0x3FC999999999999A := by decide

/-- `0.1 + 0.2 = 0.30000000000000004`: the famous `0x3FD3333333333334`. -/
theorem zeuge_add01 :
    zuBits f64 (add f64 (ofRat f64 1 10) (ofRat f64 2 10))
      = 0x3FD3333333333334 := by decide


end Gabbro.Grammatik.Gleitkomma
