/- Replay kernel rational division through one normalized guard/sticky word. -/
module
public import Stage0.Senke.Gleit.Div.RoundRatio
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- The quotient has three guard places regardless of which operand has
    the larger significand. Both scale directions use the same Nat division. -/
def softDivGuardCount (a b : Nat) : Nat := if a < b then 56 else 55

/-- Every branch of rational rounding is reproduced by the existing exact
    dyadic replay, including carry into infinity and gradual underflow. -/
theorem softDiv_replay (s : Bool) (a b ca cb t j : Nat)
    (ap : 0 < a) (bp : 0 < b)
    (al : 2 ^ 52 ≤ a * 2 ^ ca) (ah : a * 2 ^ ca < 2 ^ 53)
    (bl : 2 ^ 52 ≤ b * 2 ^ cb) (bh : b * 2 ^ cb < 2 ^ 53) :
    let k := softDivGuardCount (a * 2 ^ ca) (b * 2 ^ cb)
    let m := softDivJam ((a * 2 ^ ca) * 2 ^ k) (b * 2 ^ cb)
    let e : Int := (t : Int) - j - ca + cb - k
    rundeBruchBei f64 s (a * 2 ^ t) (b * 2 ^ j) =
      rundeExakt f64 ⟨if s then -(m : Int) else m, e⟩ := by
  dsimp only
  let A := a * 2 ^ ca
  let B := b * 2 ^ cb
  let k := softDivGuardCount A B
  let n := A * 2 ^ k
  let m := softDivJam n B
  let e : Int := (t : Int) - j - ca + cb - k
  let E : Int := e + 55
  have Bp : 0 < B := Nat.mul_pos bp (Nat.two_pow_pos _)
  have bounds := softDivGuard_bounds A B al ah bl bh
  change 2 ^ 55 * B ≤ n ∧ n < 2 ^ 56 * B ∧ n < 2 ^ 128 at bounds
  have mb := softDivJam_bounds n B Bp bounds.2.2 bounds.1 bounds.2.1
  have bits : bitlen m = 56 := bitlen_unique m 56 mb.1 mb.2 (by omega)
  have abits : bitlen a + ca = 53 := by
    have norm := bitlen_unique A 53 al ah (by omega)
    rw [bitlen_mul_pow2 a ca ap] at norm
    exact norm
  have bbits : bitlen b + cb = 53 := by
    have norm := bitlen_unique B 53 bl bh (by omega)
    rw [bitlen_mul_pow2 b cb bp] at norm
    exact norm
  have exponent : findeExp (a * 2 ^ t) (b * 2 ^ j) = E := by
    rw [softDiv_exponent a b ca cb t j ap bp abits bbits]
    dsimp only [E, e, k, softDivGuardCount, A, B]
    split <;> omega
  have normal : normQ 53 E (a * 2 ^ t) (b * 2 ^ j) = softRoundDyadic m (-3) := by
    rw [softDiv_normQ a b t j bp E,
      softDiv_normalize_round a b ca cb bp,
      ← softRoundRatio_mul_pow A B k Bp]
    have scale : 52 - E + (t : Int) - j - ca + cb - k = -3 := by
      dsimp only [E, e]
      omega
    rw [scale]
    exact softDivJam_round n B 3 Bp bounds.2.2 (by decide)
  have subnormal (below : E < f64.emin) :
      subQ f64 (a * 2 ^ t) (b * 2 ^ j) = softRoundDyadic m (e + 1074) := by
    rw [softDiv_subQ a b t j bp, softDiv_normalize_round a b ca cb bp,
      ← softRoundRatio_mul_pow A B k Bp]
    have scale : (t : Int) - j + 1074 - ca + cb - k = e + 1074 := by
      dsimp only [e]
      omega
    rw [scale]
    let shift := (-e - 1074).toNat
    have down : e + 1074 = -(shift : Int) := by
      change E < (-1022 : Int) at below
      dsimp only [E] at below
      dsimp only [shift]
      omega
    have guard : 2 ≤ shift := by
      change E < (-1022 : Int) at below
      dsimp only [E] at below
      dsimp only [shift]
      omega
    rw [down]
    exact softDivJam_round n B shift Bp bounds.2.2 guard
  have nonzero : (if s then -(m : Int) else (m : Int)) ≠ 0 := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have magnitude : (if s then -(m : Int) else (m : Int)).natAbs = m := by cases s <;> simp
  have sign : decide ((if s then -(m : Int) else (m : Int)) < 0) = s := by
    cases s <;> simp [show (0 : Int) < m by omega]
  have replay := softRound_replay_all (if s then -(m : Int) else (m : Int)) e nonzero
  dsimp only at replay
  rw [magnitude, sign, bits] at replay
  have position : e + (56 : Nat) - 1 = E := by dsimp only [E]; omega
  rw [position] at replay
  have qscale : (53 : Int) - (56 : Nat) = -3 := by decide
  rw [qscale] at replay
  unfold rundeBruchBei
  rw [if_neg (ne_of_gt (Nat.mul_pos bp (Nat.two_pow_pos _))),
    if_neg (ne_of_gt (Nat.mul_pos ap (Nat.two_pow_pos _))), exponent]
  unfold rundeBruchKern
  rw [show f64.p = 53 from rfl, normal]
  by_cases below : E < f64.emin
  · rw [subnormal below]
    exact replay.symm
  · have above : f64.emin ≤ E := by omega
    simp only [if_pos above] at replay ⊢
    exact replay.symm

/-- The exact same quotient certificate covers ordinary rounding and a
    subnormal result. These are instances of the generic rational theorem. -/
theorem softDiv_replay_zeuge :
    rundeBruchBei f64 false (2 ^ 52) (3 * 2 ^ 51) =
      rundeExakt f64 ⟨48038396025285291, -56⟩ ∧
    rundeBruchBei f64 false (2 ^ 52) (2 ^ 1075) =
      rundeExakt f64 ⟨2 ^ 55, -1078⟩ := by
  decide +kernel

#print axioms softDiv_replay
#print axioms softDiv_replay_zeuge
end Gabbro.Stage0.Senke
