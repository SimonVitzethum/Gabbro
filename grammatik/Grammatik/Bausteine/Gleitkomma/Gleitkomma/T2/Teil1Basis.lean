module

public import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T1

@[expose] public section



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


end Gabbro.Grammatik.Gleitkomma
