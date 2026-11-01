/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Shift.lean
  Subject:   `<<` and `>>` by a runtime count on integers of any width.

  The operand is extended to the shift width `k`, which also bounds the largest count by `64 k`; the count
  keeps its own limbs behind it and the kernel reads its first word. Since the type bounds the count by the
  operand's declared width (`hw2`), the kernels have no stop path: `x << n` is exact modulo `2^(64 k)`, and the
  result type holds the true product.
-/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Divide
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Shl
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Shr
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

/-- The stage count of the shift kernels is in range for every frame the lowering admits. -/
theorem shiftStages_bounds {k : Nat} (hk : 1 ≤ k) (hsmall : k < 2 ^ 31) :
    k ≤ 2 ^ shiftStages k ∧ shiftStages k ≤ 63 := by
  have above : k < 2 ^ (k.log2 + 1) := Nat.lt_log2_self
  have below : k.log2 < 31 := (Nat.log2_lt (by omega)).mpr hsmall
  unfold shiftStages
  omega

section
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
variable {W : Runner.Mem → Prop} {fp : Runner.W} {K d : Nat} {c : List II} {top : Nat}
variable {m : Runner.Mem} {pc : Runner.W}

/-- The count word the kernels read: the first limb of the count's canonical encoding. -/
theorem shiftCount_read {l2 h2 : Int} (h0' : 0 ≤ l2) (y : Zahl l2 h2) {mm : Runner.Mem} {base : Nat}
    (hy : WordsAt mm fp base (integerEncoding (integerWords l2 h2) y.n)) :
    mm.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofNat 64 y.n.toNat) := by
  have first := wordsAt_first (integerWords_pos' l2 h2) hy
  have eq : BitVec.ofInt 64 y.n = BitVec.ofNat 64 y.n.toNat := by
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg (by have := y.lo_le; omega)]
  rw [first, eq]

theorem wideShl_ok {l1 h1 l2 h2 : Int} (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (x : Zahl l1 h1) (y : Zahl l2 h2) {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + shiftWords l1 h1 h2 0 (h1 * 2 ^ h2.toNat)) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + shiftWords l1 h1 h2 0 (h1 * 2 ^ h2.toNat)) cb ρ W reserved →
      ValueOk L m pc fp K (d + shiftWords l1 h1 h2 0 (h1 * 2 ^ h2.toNat)) cb (.int l2 h2) y)
    (h : wideShlL l1 h1 l2 h2 0 (h1 * 2 ^ h2.toNat) d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (h1 * 2 ^ h2.toNat)) (Zahl.shl w hw1 hw2 h0 h0' x y) := by
  unfold wideShlL at h
  have ex : ((x.n.toNat : Nat) : Int) = x.n := Int.toNat_of_nonneg (by have := x.lo_le; omega)
  have ey : ((y.n.toNat : Nat) : Int) = y.n := Int.toNat_of_nonneg (by have := y.lo_le; omega)
  have left : integerWords l1 h1 ≤ shiftWords l1 h1 h2 0 (h1 * 2 ^ h2.toNat) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have run := wideBinary_ok x y left (Nat.le_refl _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (shiftWords l1 h1 h2 0 (h1 * 2 ^ h2.toNat))
      ((x.n.toNat * 2 ^ y.n.toNat : Nat) : Int)))
    (fun m pc hP hd hx hy => by
      have positive := Nat.le_trans (integerWords_pos' l1 h1) left
      have bounds := shiftStages_bounds positive (by have := hP.small; omega)
      have count : y.n.toNat < 64 * shiftWords l1 h1 h2 0 (h1 * 2 ^ h2.toNat) := by
        have := y.lo_le
        have := y.le_hi
        unfold shiftWords
        omega
      have hN := shiftCount_read h0' y hy
      rw [← ex] at hx
      obtain ⟨m', st, ag, wz⟩ := wideShl_run hP.frame hP.small (by omega) count bounds.1 bounds.2
        hP.code hP.far x.n.toNat hx hN
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => by
    have value : (Zahl.shl w hw1 hw2 h0 h0' x y).n = ((x.n.toNat * 2 ^ y.n.toNat : Nat) : Int) := by
      change x.n * 2 ^ y.n.toNat = _
      push_cast
      rw [ex]
    exact valueAt_int_of_wide (Zahl.shl w hw1 hw2 h0 h0' x y) (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_max_left _ _)) (by rw [value]; exact words)

theorem wideShr_ok {l1 h1 l2 h2 : Int} (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (x : Zahl l1 h1) (y : Zahl l2 h2) {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + shiftWords l1 h1 h2 0 h1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + shiftWords l1 h1 h2 0 h1) cb ρ W reserved →
      ValueOk L m pc fp K (d + shiftWords l1 h1 h2 0 h1) cb (.int l2 h2) y)
    (h : wideShrL l1 h1 l2 h2 0 h1 d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 h1) (Zahl.shr w hw1 hw2 h0 h0' x y) := by
  unfold wideShrL at h
  have ex : ((x.n.toNat : Nat) : Int) = x.n := Int.toNat_of_nonneg (by have := x.lo_le; omega)
  have left : integerWords l1 h1 ≤ shiftWords l1 h1 h2 0 h1 :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have run := wideBinary_ok x y left (Nat.le_refl _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (shiftWords l1 h1 h2 0 h1)
      ((x.n.toNat / 2 ^ y.n.toNat : Nat) : Int)))
    (fun m pc hP hd hx hy => by
      have positive := Nat.le_trans (integerWords_pos' l1 h1) left
      have bounds := shiftStages_bounds positive (by have := hP.small; omega)
      have count : y.n.toNat < 64 * shiftWords l1 h1 h2 0 h1 := by
        have := y.lo_le
        have := y.le_hi
        unfold shiftWords
        omega
      have hN := shiftCount_read h0' y hy
      rw [← ex] at hx
      obtain ⟨m', st, ag, wz⟩ := wideShr_run hP.frame hP.small (by omega) count bounds.1 bounds.2
        hP.code hP.far x.n.toNat (unsignedFits_zahl h0 x left) hx hN
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => by
    have value : (Zahl.shr w hw1 hw2 h0 h0' x y).n = ((x.n.toNat / 2 ^ y.n.toNat : Nat) : Int) := by
      change x.n / 2 ^ y.n.toNat = _
      push_cast
      rw [ex]
    exact valueAt_int_of_wide (Zahl.shr w hw1 hw2 h0 h0' x y) (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_max_left _ _)) (by rw [value]; exact words)

end

end Gabbro.Stage0.Senke
