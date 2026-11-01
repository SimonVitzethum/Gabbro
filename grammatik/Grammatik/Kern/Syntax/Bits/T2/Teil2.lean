module

public import Grammatik.Kern.Syntax.Bits.T1
public import Grammatik.Kern.Syntax.Bits.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- `clz_log2`: `clz x + log2_floor x = w`, as values. -/
theorem clz_log2 (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    (Zahl.clz w x).n + (Zahl.log2_floor w x).n = (w : Int) := by
  have hb := zahlNat_bounds w x
  have h := clzn_log2n hb.1 hb.2
  show ((clzn w (zahlNat w x) : Nat) : Int)
    + ((Nat.log2 (zahlNat w x) : Nat) : Int) = (w : Int)
  have hle : ((clzn w (zahlNat w x) + Nat.log2 (zahlNat w x) : Nat) : Int)
      ≤ (w : Int) := Int.ofNat_le.mpr (Nat.le_of_eq h)
  have hge : (w : Int)
      ≤ ((clzn w (zahlNat w x) : Nat) : Int)
        + ((Nat.log2 (zahlNat w x) : Nat) : Int) := by
    have e : ((clzn w (zahlNat w x) + Nat.log2 (zahlNat w x) : Nat) : Int)
        = ((clzn w (zahlNat w x) : Nat) : Int)
          + ((Nat.log2 (zahlNat w x) : Nat) : Int) := by simp only [Int.natCast_add]
    omega
  omega

/-- `ctz_spez`: `2 ^ r ∣ x` and `¬ 2 ^ (r+1) ∣ x` for `r = ctz x`. -/
theorem ctz_spez (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    ((2 : Int) ^ ctzn w (zahlNat w x)) ∣ x.n
      ∧ ¬ ((2 : Int) ^ (ctzn w (zahlNat w x) + 1)) ∣ x.n := by
  have hb := zahlNat_bounds w x
  obtain ⟨hdvd, hnd⟩ := ctzn_spez hb.1 hb.2
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have hval : x.n.toNat = zahlNat w x := rfl
  constructor
  · have hcast : ((2 ^ ctzn w (zahlNat w x) : Nat) : Int)
        = (2 : Int) ^ ctzn w (zahlNat w x) := by simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    have h1 : ((2 ^ ctzn w (zahlNat w x) : Nat) : Int)
        ∣ ((zahlNat w x : Nat) : Int) := Int.natCast_dvd_natCast.mpr hdvd
    rw [hcast, ← hval, h2n] at h1
    exact h1
  · intro hdvdI
    apply hnd
    have hcast : ((2 ^ (ctzn w (zahlNat w x) + 1) : Nat) : Int)
        = (2 : Int) ^ (ctzn w (zahlNat w x) + 1) := by simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    have hnat : ((2 ^ (ctzn w (zahlNat w x) + 1) : Nat) : Int)
        ∣ ((x.n.toNat : Nat) : Int) := by
      rw [hcast, h2n]
      exact hdvdI
    have hnat2 : 2 ^ (ctzn w (zahlNat w x) + 1) ∣ x.n.toNat :=
      Int.natCast_dvd_natCast.mp hnat
    rw [hval] at hnat2
    exact hnat2

/-- `popcount_rotl`: popcount is invariant under rotation, as values. -/
theorem popcount_rotl (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) :
    (Zahl.popcount w (Zahl.rotl w x s)).n = (Zahl.popcount w x).n := by
  have hs : s.n.toNat ≤ w := zahlAmt_le w s
  have hx : x.n.toNat < 2 ^ (w + 1) := zahlFull_bounds w x
  have h := popcountn_rotln w s.n.toNat x.n.toNat hs hx
  show ((popcountn w (rotln w s.n.toNat x.n.toNat) : Nat) : Int)
    = ((popcountn w x.n.toNat : Nat) : Int)
  rw [h]

/-- `rotl_rotr`: `rotr ∘ rotl = id`, as values. -/
theorem rotl_rotr (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) :
    (Zahl.rotr w (Zahl.rotl w x s) s).n = x.n := by
  have hs : s.n.toNat ≤ w := zahlAmt_le w s
  have hx : x.n.toNat < 2 ^ (w + 1) := zahlFull_bounds w x
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have h := rotrn_rotln w s.n.toNat x.n.toNat hs hx
  show ((rotrn w s.n.toNat (rotln w s.n.toNat x.n.toNat) : Nat) : Int) = x.n
  rw [h, h2n]


end Gabbro.Grammatik
