/- Rounding replay for software binary64 addition (`Block.float`, `op = .add`).

    The finite path adds exactly, then rounds: `softRound_replay` proves the
    routine's (quotient, remainder, denominator) triple — formed from the
    ordered exact sum `softFinite_exact` pins down — decides exactly the
    kernel's normal-branch rounding (`rundeBruchKern` through `normQ`). The
    bridge is `softRound_congr`: `rundeInt` depends only on the rational
    value, so the routine's one-bit normalization and the kernel's `normQD`
    scaling agree whenever they name the same rational. `softNormK_bitlen`
    ties the routine's shift to the bit length; `findeExp_scaled` (in
    `BitLength.lean`) positions the kernel exponent. Subnormal inputs and
    the deep-underflow/overflow branches keep their own triples; they are
    replayed where the routine emits them, reusing `softRound_congr` and
    `findeExp_scaled` from here. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Gleit.Align
public import Stage0.Senke.Gleit.BitLength
public import Stage0.Senke.Gleit.Pack
public import Stage0.Senke.Gleit.Round
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma
variable [Runner.IR.Kern]

/-! ## The routine triple names the exact sum. -/

/-- The routine triple is exact: quotient times denominator plus remainder
    is the unshifted magnitude. Mirrors `softJam_exact`. -/
theorem softForm_rat (S : Nat) :
    softNormQ S * softNormDen S + softNormR S = S := by
  have h := Nat.mod_add_div S (2 ^ softNormK S)
  unfold softNormQ softNormR softNormDen
  rw [Nat.mul_comm (2 ^ softNormK S) (S / 2 ^ softNormK S)] at h
  omega

/-- `rundeInt` depends only on the rational value: two triples naming the
    same rational round identically. Quotients agree first (floor
    uniqueness), then remainders cross-multiply, then each comparison
    transports. -/
theorem softRound_congr (q₁ r₁ d₁ q₂ r₂ d₂ : Nat)
    (h₁ : r₁ < d₁) (h₂ : r₂ < d₂)
    (h : (q₁ * d₁ + r₁) * d₂ = (q₂ * d₂ + r₂) * d₁) :
    rundeInt q₁ r₁ d₁ = rundeInt q₂ r₂ d₂ := by
  have hd₁ : 0 < d₁ := by omega
  have hd₂ : 0 < d₂ := by omega
  have e : q₁ * (d₁ * d₂) + r₁ * d₂ = q₂ * (d₁ * d₂) + r₂ * d₁ := by
    have h1 : (q₁ * d₁ + r₁) * d₂ = q₁ * (d₁ * d₂) + r₁ * d₂ := by ring
    have h2 : (q₂ * d₂ + r₂) * d₁ = q₂ * (d₁ * d₂) + r₂ * d₁ := by ring
    rw [← h1, ← h2]; exact h
  have b₁ : r₁ * d₂ < d₁ * d₂ := Nat.mul_lt_mul_of_pos_right h₁ hd₂
  have h₂d : r₂ * d₁ < d₂ * d₁ := Nat.mul_lt_mul_of_pos_right h₂ hd₁
  have b₂ : r₂ * d₁ < d₁ * d₂ := by
    rw [Nat.mul_comm d₂ d₁] at h₂d
    exact h₂d
  have hq : q₁ = q₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (q₁ + 1) * (d₁ * d₂) ≤ q₂ * (d₁ * d₂) :=
        Nat.mul_le_mul (Nat.succ_le_of_lt hlt) (Nat.le_refl _)
      have had : (q₁ + 1) * (d₁ * d₂) = q₁ * (d₁ * d₂) + d₁ * d₂ := by ring
      rw [had] at hle
      omega
    · have hle : (q₂ + 1) * (d₁ * d₂) ≤ q₁ * (d₁ * d₂) :=
        Nat.mul_le_mul (Nat.succ_le_of_lt hgt) (Nat.le_refl _)
      have had : (q₂ + 1) * (d₁ * d₂) = q₂ * (d₁ * d₂) + d₁ * d₂ := by ring
      rw [had] at hle
      omega
  have hr : r₁ * d₂ = r₂ * d₁ := by
    rw [hq] at e
    exact Nat.add_left_cancel e
  have m1 : (2 * r₁) * d₂ = 2 * (r₁ * d₂) := by ring
  have m2 : (2 * r₂) * d₁ = 2 * (r₂ * d₁) := by ring
  have m3 : d₁ * d₂ = d₂ * d₁ := Nat.mul_comm _ _
  have lt₁ : 2 * r₁ < d₁ → 2 * r₂ < d₂ := by
    intro hlt
    by_contra hcon
    push_neg at hcon
    have small : (2 * r₁) * d₂ < d₁ * d₂ :=
      Nat.mul_lt_mul_of_pos_right hlt hd₂
    have big : d₂ * d₁ ≤ (2 * r₂) * d₁ :=
      Nat.mul_le_mul hcon (Nat.le_refl _)
    omega
  have lt₂ : 2 * r₂ < d₂ → 2 * r₁ < d₁ := by
    intro hlt
    by_contra hcon
    push_neg at hcon
    have small : (2 * r₂) * d₁ < d₂ * d₁ :=
      Nat.mul_lt_mul_of_pos_right hlt hd₁
    have big : d₁ * d₂ ≤ (2 * r₁) * d₂ :=
      Nat.mul_le_mul hcon (Nat.le_refl _)
    omega
  have gt₁ : d₁ < 2 * r₁ → d₂ < 2 * r₂ := by
    intro hgt
    by_contra hcon
    push_neg at hcon
    have small : d₁ * d₂ < (2 * r₁) * d₂ :=
      Nat.mul_lt_mul_of_pos_right hgt hd₂
    have big : (2 * r₂) * d₁ ≤ d₂ * d₁ :=
      Nat.mul_le_mul hcon (Nat.le_refl _)
    omega
  have gt₂ : d₂ < 2 * r₂ → d₁ < 2 * r₁ := by
    intro hgt
    by_contra hcon
    push_neg at hcon
    have small : d₂ * d₁ < (2 * r₂) * d₁ :=
      Nat.mul_lt_mul_of_pos_right hgt hd₁
    have big : (2 * r₁) * d₂ ≤ d₁ * d₂ :=
      Nat.mul_le_mul hcon (Nat.le_refl _)
    omega
  rcases lt_trichotomy (2 * r₁) d₁ with hlt | heq | hgt
  · rw [rundeInt_fall _ _ _ hlt, rundeInt_fall _ _ _ (lt₁ hlt)]
    exact hq
  · have heq₂ : 2 * r₂ = d₂ := by
      rcases lt_trichotomy (2 * r₂) d₂ with h | h | h
      · have := lt₂ h; omega
      · exact h
      · have := gt₂ h; omega
    unfold rundeInt
    rw [if_neg (by omega : ¬ d₁ < 2 * r₁), if_neg (by omega : ¬ 2 * r₁ < d₁),
      if_neg (by omega : ¬ d₂ < 2 * r₂), if_neg (by omega : ¬ 2 * r₂ < d₂), hq]
  · rw [rundeInt_steig _ _ _ hgt, rundeInt_steig _ _ _ (gt₁ hgt)]
    rw [hq]

/-- The routine shift is the bit length minus the significand width, on the
    one-bit-normalization path. -/
theorem softNormK_bitlen (S : Nat) (hlo : 2 ^ 52 ≤ S) (hhi : S < 2 ^ 54) :
    softNormK S = bitlen S - 53 := by
  have hob := bitlen_obere S
  have hun := bitlen_untere S (by omega)
  have hlow : 52 < bitlen S := by
    by_contra hcon
    push_neg at hcon
    have h1 := Nat.pow_le_pow_right (show 0 < 2 by decide) hcon
    omega
  have hhigh : bitlen S < 55 := by
    by_contra hcon
    push_neg at hcon
    have h1 := Nat.pow_le_pow_right (show 0 < 2 by decide) hcon
    have h2 : (2 : Nat) ^ 55 = 2 * 2 ^ 54 := by
      rw [show (55 : Nat) = 54 + 1 from rfl, Nat.pow_succ, Nat.mul_comm]
    omega
  have h53 : (2 : Nat) ^ 54 = 2 * 2 ^ 53 := by
    rw [show (54 : Nat) = 53 + 1 from rfl, Nat.pow_succ, Nat.mul_comm]
  unfold softNormK
  by_cases hlt : S < 2 ^ 53
  · rw [if_pos hlt]
    have : bitlen S = 53 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h1
      · have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show bitlen S ≤ 52 by omega)
        omega
      · have h2 : bitlen S = 54 := by omega
        have h3 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 54 ≤ bitlen S by omega)
        omega
    omega
  · rw [if_neg hlt]
    have : bitlen S = 54 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h1
      · have h2 : bitlen S = 53 := by omega
        rw [h2] at hob
        omega
      · omega
    omega

/-! ## The `normQD` branches as rewrite rules. -/

/-- The `normQD` scaling-up branch: the scaled pair. -/
theorem normQD_pos (E : Int) (n d : Nat) (M : Nat)
    (hM : M = (((53 : Nat) : Int) - 1 - E).toNat)
    (hMpos : 0 ≤ ((53 : Nat) : Int) - 1 - E) :
    normQD 53 E n d = (n * 2 ^ M, d) := by
  unfold normQD
  rw [if_pos hMpos, hM]

/-- The `normQD` scaling-down branch: the scaled pair. -/
theorem normQD_neg (E : Int) (n d : Nat) (M : Nat)
    (hM : M = (E - (((53 : Nat) : Int) - 1)).toNat)
    (hMneg : ¬ 0 ≤ ((53 : Nat) : Int) - 1 - E) :
    normQD 53 E n d = (n, d * 2 ^ M) := by
  unfold normQD
  rw [if_neg hMneg, hM]

/-! ## The normal-branch replay. -/

/-- The routine triple replays the kernel `normQ` decision: the kernel
    triple names the same rational as the routine triple. -/
theorem softRound_normQD (S N Dd : Nat)
    (hRd : N % Dd < Dd)
    (hagree : S * Dd = N * softNormDen S) :
    softRoundMag (softNormQ S) (softNormR S) (softNormDen S)
      = rundeInt (N / Dd) (N % Dd) Dd := by
  unfold softRoundMag
  have hR : softNormR S < softNormDen S := Nat.mod_lt _ (Nat.two_pow_pos _)
  apply softRound_congr _ _ _ _ _ _ hR hRd
  rw [softForm_rat S, Nat.div_add_mod']
  exact hagree

/-- The kernel `rundeBruchKern` normal branch, with the positioned exponent
    and the routine triple as the `normQ` decision. -/
theorem softRound_kern (S n d : Nat) (E : Int) (s : Bool)
    (hlo : (f64.emin : Int) ≤ E) (hhi : E < (f64.emax : Int))
    (hQr : normQ 53 E n d = softRoundMag (softNormQ S) (softNormR S) (softNormDen S))
    (hQr53 : softRoundMag (softNormQ S) (softNormR S) (softNormDen S) ≤ 2 ^ 53) :
    rundeBruchKern f64 s n d E =
      ⟨s, (E - f64.emin + 1).toNat +
        (if softRoundMag (softNormQ S) (softNormR S) (softNormDen S) = 2 ^ 53 then 1 else 0),
        (if softRoundMag (softNormQ S) (softNormR S) (softNormDen S) = 2 ^ 53 then 2 ^ 52
        else softRoundMag (softNormQ S) (softNormR S) (softNormDen S)) - 2 ^ (f64.p - 1)⟩ := by
  have hemax : f64.emax = 1023 := rfl
  have hemin : f64.emin = 1 - 1023 := rfl
  have hp53 : f64.p = 53 := rfl
  have hfp : (53 : Nat) - 1 = 52 := rfl
  unfold rundeBruchKern
  rw [hp53, hfp]
  have c1 : ¬ (f64.emax : Int) < E := by omega
  have c2 : ¬ E < (f64.emin : Int) - ((53 : Nat) : Int) := by omega
  rw [if_neg c1, if_neg c2, if_pos hlo, hQr]
  by_cases hcar : softRoundMag (softNormQ S) (softNormR S) (softNormDen S) = 2 ^ 53
  · have hlt : ¬ softRoundMag (softNormQ S) (softNormR S) (softNormDen S) < 2 ^ 53 := by omega
    rw [if_neg hlt, if_pos hhi, if_pos hcar]
    have exponent : (E - f64.emin + 2).toNat = (E - f64.emin + 1).toNat + 1 := by
      omega
    rw [exponent]
    simp only [hcar, ite_true, Nat.sub_self]
  · have hlt : softRoundMag (softNormQ S) (softNormR S) (softNormDen S) < 2 ^ 53 := by omega
    rw [if_pos hlt]
    simp only [hcar, ite_false, Nat.add_zero]

/-- The normal replay: on the ordered finite path with a set top bit, the
    kernel `rundeExakt` of the exact sum is the routine's rounded significand
    with carry, at the positioned exponent. Both `exaktBruch` shapes and both
    `normQD` scalings reduce to the exponent equation `hE`. -/
theorem softRound_replay (u v : Exakt) (hle : u.zweierExp ≤ v.zweierExp)
    (S : Nat) (hS : S = (exaktAdd u v).zaehler.natAbs) (hSpos : 0 < S)
    (hSbound : S < 2 ^ 54) (hSlow : 2 ^ 52 ≤ S)
    (E : Int) (hE : E = u.zweierExp + 52 + (softNormK S : Int))
    (hlo : (f64.emin : Int) ≤ E) (hhi : E < (f64.emax : Int)) :
    rundeExakt f64 (exaktAdd u v) =
      ⟨decide ((exaktAdd u v).zaehler < 0),
       (E - f64.emin + 1).toNat +
         (if softRoundMag (softNormQ S) (softNormR S) (softNormDen S) = 2 ^ 53 then 1 else 0),
       (if softRoundMag (softNormQ S) (softNormR S) (softNormDen S) = 2 ^ 53 then 2 ^ 52
        else softRoundMag (softNormQ S) (softNormR S) (softNormDen S)) - 2 ^ (f64.p - 1)⟩ := by
  have hex := softAlignAdd_exact u v hle
  rw [hex] at hS ⊢
  dsimp only at hS ⊢
  have hk := softNormK_bitlen S hSlow hSbound
  have hbits : 53 ≤ bitlen S := by
    have hob := bitlen_obere S
    by_contra hcon
    have hle : bitlen S ≤ 52 := by omega
    have hpow := Nat.pow_le_pow_right (show 0 < 2 by decide) hle
    omega
  have hEbits : E = u.zweierExp + (bitlen S : Int) - 1 := by
    omega
  have hQr53 : softRoundMag (softNormQ S) (softNormR S) (softNormDen S) ≤ 2 ^ 53 := by
    have hb : softNormQ S < 2 ^ 53 := by
      unfold softNormQ softNormK
      split
      · simpa only [Nat.pow_zero, Nat.div_one] using ‹S < 2 ^ 53›
      · change S / 2 < 2 ^ 53
        omega
    have hle1 : softRoundMag (softNormQ S) (softNormR S) (softNormDen S)
        ≤ softNormQ S + 1 := by
      unfold softRoundMag rundeInt
      split
      · omega
      · split
        · omega
        · split <;> omega
    exact hle1.trans (Nat.succ_le_of_lt hb)
  unfold rundeExakt rundeBruch exaktBruch
  dsimp only
  by_cases he0 : 0 ≤ u.zweierExp
  · rw [if_pos he0]
    dsimp only
    have hpos : (0 : Int) < ((2 ^ u.zweierExp.toNat : Nat) : Int) := by
      exact_mod_cast Nat.two_pow_pos _
    have hsign : (u.zaehler + v.zaehler * (2 ^ softGap u.zweierExp v.zweierExp : Nat))
          * ((2 ^ u.zweierExp.toNat : Nat) : Int) < 0
        ↔ u.zaehler + v.zaehler * (2 ^ softGap u.zweierExp v.zweierExp : Nat) < 0 := by
      constructor
      · intro h
        by_contra hcon
        push_neg at hcon
        have hnn := Int.mul_nonneg hcon (le_of_lt hpos)
        omega
      · intro h
        exact Int.mul_neg_of_neg_of_pos h hpos
    have hsb : decide ((u.zaehler + v.zaehler * (2 ^ softGap u.zweierExp v.zweierExp : Nat))
          * ((2 ^ u.zweierExp.toNat : Nat) : Int) < 0)
        = decide (u.zaehler + v.zaehler * (2 ^ softGap u.zweierExp v.zweierExp : Nat) < 0) := by
      simp only [hsign]
    have hn0 : S * 2 ^ u.zweierExp.toNat ≠ 0 :=
      ne_of_gt (Nat.mul_pos hSpos (Nat.two_pow_pos _))
    rw [hsb, Int.natAbs_mul, Int.natAbs_natCast, ← hS]
    simp only [rundeBruchBei, show (1 : Nat) ≠ 0 by decide, hn0, ite_false]
    have he_nat : ((u.zweierExp.toNat : Nat) : Int) = u.zweierExp := by omega
    have hEpos : findeExp (S * 2 ^ u.zweierExp.toNat) 1 = E := by
      have h1 := findeExp_scaled S u.zweierExp.toNat 0 hSpos
      simp only [Nat.pow_zero] at h1
      rw [h1, he_nat]
      omega
    rw [hEpos]
    have hQr : normQ 53 E (S * 2 ^ u.zweierExp.toNat) 1
        = softRoundMag (softNormQ S) (softNormR S) (softNormDen S) := by
      by_cases hm : 0 ≤ ((53 : Nat) : Int) - 1 - E
      · set M := (((53 : Nat) : Int) - 1 - E).toNat with hM
        have hQD : normQD 53 E (S * 2 ^ u.zweierExp.toNat) 1 = (S * 2 ^ u.zweierExp.toNat * 2 ^ M, 1) :=
          normQD_pos E _ _ M hM hm
        have hnorm : normQ 53 E (S * 2 ^ u.zweierExp.toNat) 1
            = rundeInt ((S * 2 ^ u.zweierExp.toNat * 2 ^ M) / 1) ((S * 2 ^ u.zweierExp.toNat * 2 ^ M) % 1) 1 := by
          unfold normQ; rw [hQD]; try dsimp only
        rw [hnorm]
        have hRd : (S * 2 ^ u.zweierExp.toNat * 2 ^ M) % 1 < 1 := Nat.mod_lt _ (by decide)
        have e2 : (S * 2 ^ u.zweierExp.toNat * 2 ^ M) * softNormDen S
            = S * 2 ^ (u.zweierExp.toNat + M + softNormK S) := by
          unfold softNormDen; rw [Nat.pow_add, Nat.pow_add]; ring
        have hexp : 0 = u.zweierExp.toNat + M + softNormK S := by omega
        have hagree : S * 1 = (S * 2 ^ u.zweierExp.toNat * 2 ^ M) * softNormDen S := by
          rw [Nat.mul_one, e2, ← hexp, Nat.pow_zero, Nat.mul_one]
        exact (softRound_normQD S _ _ hRd hagree).symm
      · set M := (E - (((53 : Nat) : Int) - 1)).toNat with hM
        have hQD : normQD 53 E (S * 2 ^ u.zweierExp.toNat) 1 = (S * 2 ^ u.zweierExp.toNat, 1 * 2 ^ M) :=
          normQD_neg E _ _ M hM hm
        have hnorm : normQ 53 E (S * 2 ^ u.zweierExp.toNat) 1
            = rundeInt ((S * 2 ^ u.zweierExp.toNat) / (1 * 2 ^ M))
              ((S * 2 ^ u.zweierExp.toNat) % (1 * 2 ^ M)) (1 * 2 ^ M) := by
          unfold normQ; rw [hQD]; try dsimp only
        rw [hnorm]
        have hRd : (S * 2 ^ u.zweierExp.toNat) % (1 * 2 ^ M) < 1 * 2 ^ M :=
          Nat.mod_lt _ (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
        have e2 : (S * 2 ^ u.zweierExp.toNat) * 1
            = S * 2 ^ (u.zweierExp.toNat + 0) := by
          rw [Nat.mul_one, Nat.add_zero]
        have hexp : M = u.zweierExp.toNat + softNormK S := by omega
        have hagree : S * (1 * 2 ^ M) = (S * 2 ^ u.zweierExp.toNat) * softNormDen S := by
          have e3 : (S * 2 ^ u.zweierExp.toNat) * softNormDen S
              = S * 2 ^ (u.zweierExp.toNat + softNormK S) := by
            unfold softNormDen; rw [Nat.pow_add]; ring
          rw [e3, ← hexp, Nat.one_mul]
        exact (softRound_normQD S _ _ hRd hagree).symm
    exact softRound_kern S _ _ E _ hlo hhi hQr hQr53
  · rw [if_neg he0]
    dsimp only
    have hd0 : 2 ^ (-u.zweierExp).toNat ≠ 0 :=
      ne_of_gt (Nat.two_pow_pos _)
    rw [← hS]
    simp only [rundeBruchBei, hd0, show S ≠ 0 by omega, ite_false]
    have he_nat : (((-u.zweierExp).toNat : Nat) : Int) = -u.zweierExp := by omega
    have hEpos : findeExp S (2 ^ (-u.zweierExp).toNat) = E := by
      have h1 := findeExp_scaled S 0 (-u.zweierExp).toNat hSpos
      simp only [Nat.pow_zero, Nat.mul_one] at h1
      rw [h1, he_nat]
      omega
    rw [hEpos]
    have hQr : normQ 53 E S (2 ^ (-u.zweierExp).toNat)
        = softRoundMag (softNormQ S) (softNormR S) (softNormDen S) := by
      by_cases hm : 0 ≤ ((53 : Nat) : Int) - 1 - E
      · set M := (((53 : Nat) : Int) - 1 - E).toNat with hM
        have hQD : normQD 53 E S (2 ^ (-u.zweierExp).toNat) = (S * 2 ^ M, 2 ^ (-u.zweierExp).toNat) :=
          normQD_pos E _ _ M hM hm
        have hnorm : normQ 53 E S (2 ^ (-u.zweierExp).toNat)
            = rundeInt ((S * 2 ^ M) / (2 ^ (-u.zweierExp).toNat))
              ((S * 2 ^ M) % (2 ^ (-u.zweierExp).toNat)) (2 ^ (-u.zweierExp).toNat) := by
          unfold normQ; rw [hQD]; try dsimp only
        rw [hnorm]
        have hRd : (S * 2 ^ M) % (2 ^ (-u.zweierExp).toNat) < 2 ^ (-u.zweierExp).toNat :=
          Nat.mod_lt _ (Nat.two_pow_pos _)
        have e2 : (S * 2 ^ M) * softNormDen S
            = S * 2 ^ (M + softNormK S) := by
          unfold softNormDen; rw [Nat.pow_add]; ring
        have hexp : (-u.zweierExp).toNat = M + softNormK S := by omega
        have hagree : S * (2 ^ (-u.zweierExp).toNat) = (S * 2 ^ M) * softNormDen S := by
          rw [e2, ← hexp]
        exact (softRound_normQD S _ _ hRd hagree).symm
      · set M := (E - (((53 : Nat) : Int) - 1)).toNat with hM
        have hQD : normQD 53 E S (2 ^ (-u.zweierExp).toNat)
            = (S, 2 ^ (-u.zweierExp).toNat * 2 ^ M) :=
          normQD_neg E _ _ M hM hm
        have hnorm : normQ 53 E S (2 ^ (-u.zweierExp).toNat)
            = rundeInt (S / (2 ^ (-u.zweierExp).toNat * 2 ^ M))
              (S % (2 ^ (-u.zweierExp).toNat * 2 ^ M)) (2 ^ (-u.zweierExp).toNat * 2 ^ M) := by
          unfold normQ; rw [hQD]; try dsimp only
        rw [hnorm]
        have hRd : S % (2 ^ (-u.zweierExp).toNat * 2 ^ M) < 2 ^ (-u.zweierExp).toNat * 2 ^ M :=
          Nat.mod_lt _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
        have e2 : S * 1 = S * 2 ^ (0 : Nat) := by rw [Nat.pow_zero, Nat.mul_one]
        have hexp : (-u.zweierExp).toNat + M = softNormK S := by omega
        have hagree : S * (2 ^ (-u.zweierExp).toNat * 2 ^ M) = S * softNormDen S := by
          have e3 : (2 ^ (-u.zweierExp).toNat * 2 ^ M) = 2 ^ ((-u.zweierExp).toNat + M) := by
            rw [← Nat.pow_add]
          rw [e3, hexp]
          unfold softNormDen
        exact (softRound_normQD S _ _ hRd hagree).symm
    exact softRound_kern S _ _ E _ hlo hhi hQr hQr53

#print axioms softForm_rat
#print axioms softRound_congr
#print axioms softNormK_bitlen
#print axioms normQD_pos
#print axioms normQD_neg
#print axioms softRound_normQD
#print axioms softRound_kern
#print axioms softRound_replay

end Gabbro.Stage0.Senke
