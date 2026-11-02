/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Ring.lean
  Subject:   Addition, subtraction, multiplication, negation and the bitwise operators on integers of any
             width: the generic operand placement connected to the kernels' execution theorems.

  Each theorem takes the operands as `ValueOk` induction hypotheses (their canonical limbs in memory) and the
  assembled code, and returns the result's complete canonical limbs. The kernel works modulo `2^(64 k)` at the
  common width `k`; the result type's own limbs are the first ones (`valueAt_int_of_wide`).
-/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Operands
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Run
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Multiply.MulRun
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Neg
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Bits
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
variable {W : Runner.Mem → Prop} {fp : Runner.W} {K d : Nat} {c : List II} {top : Nat}
variable {m : Runner.Mem} {pc : Runner.W}

theorem wideAdd_ok {l1 h1 l2 h2 : Int} (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 (l1 + l2) (h1 + h2)) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 (l1 + l2) (h1 + h2)) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 (l1 + l2) (h1 + h2)) cb (.int l2 h2) y)
    (h : wideAddL l1 h1 l2 h2 (l1 + l2) (h1 + h2) d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int (l1 + l2) (h1 + h2)) (Zahl.add x y) := by
  unfold wideAddL at h
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d
      (integerEncoding (arithWords l1 h1 l2 h2 (l1 + l2) (h1 + h2)) (x.n + y.n)))
    (fun m pc hP hd hx hy => by
      obtain ⟨m', st, ag, wz, _⟩ := wideAdd_run hP.frame hP.small (by omega) hP.code hP.far x.n y.n hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => valueAt_int_of_wide (Zahl.add x y) (arithWords_result _ _ _ _ _ _) words

theorem wideSub_ok {l1 h1 l2 h2 : Int} (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 (l1 - h2) (h1 - l2)) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 (l1 - h2) (h1 - l2)) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 (l1 - h2) (h1 - l2)) cb (.int l2 h2) y)
    (h : wideSubL l1 h1 l2 h2 (l1 - h2) (h1 - l2) d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int (l1 - h2) (h1 - l2)) (Zahl.sub x y) := by
  unfold wideSubL at h
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d
      (integerEncoding (arithWords l1 h1 l2 h2 (l1 - h2) (h1 - l2)) (x.n - y.n)))
    (fun m pc hP hd hx hy => by
      obtain ⟨m', st, ag, wz, _⟩ := wideSub_run hP.frame hP.small (by omega) hP.code hP.far x.n y.n hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => valueAt_int_of_wide (Zahl.sub x y) (arithWords_result _ _ _ _ _ _) words

theorem wideMul_ok {l1 h1 l2 h2 : Int} (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2))) (imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2))) (imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2))) (imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))) cb (.int l2 h2) y)
    (h : wideMulL l1 h1 l2 h2 (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2))) (imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2))) d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2))) (imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))) (Zahl.mul x y) := by
  unfold wideMulL at h
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (arithWords l1 h1 l2 h2 (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2))) (imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))) (x.n * y.n)))
    (fun m pc hP hd hx hy => by
      obtain ⟨m', st, ag, wz, _⟩ := wideMul_run hP.frame hP.small (by omega) hP.code hP.far x.n y.n hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => valueAt_int_of_wide (Zahl.mul x y) (arithWords_result _ _ _ _ _ _) words

theorem wideNeg_ok {lo hi : Int} (x : Zahl lo hi) {fa : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int lo hi) x)
    (h : wideNegL lo hi (-hi) (-lo) d fa = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int (-hi) (-lo)) (Zahl.neg x) := by
  unfold wideNegL at h
  have run := wideUnary_ok x (Nat.le_max_left (integerWords lo hi) (integerWords (-hi) (-lo))) iha h hK hp
    (R := fun m' => WordsAt m' fp d
      (integerEncoding (max (integerWords lo hi) (integerWords (-hi) (-lo))) (-x.n)))
    (fun m pc hP hd hx => by
      obtain ⟨m', st, ag, wz⟩ := wideNeg_run hP.frame hP.small (by omega) hP.code hP.far x.n hx
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words =>
    valueAt_int_of_wide (Zahl.neg x) (Nat.le_max_right (integerWords lo hi) (integerWords (-hi) (-lo))) words

theorem wideBand_ok {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 0 h1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 0 h1) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 0 h1) cb (.int l2 h2) y)
    (h : wideBitL 8 l1 h1 l2 h2 0 h1 d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 h1) (Zahl.band h0 h0' x y) := by
  unfold wideBitL at h
  have ex : ((x.n.toNat : Nat) : Int) = x.n := Int.toNat_of_nonneg (by have := x.lo_le; omega)
  have ey : ((y.n.toNat : Nat) : Int) = y.n := Int.toNat_of_nonneg (by have := y.lo_le; omega)
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (arithWords l1 h1 l2 h2 0 h1)
      ((x.n.toNat &&& y.n.toNat : Nat) : Int)))
    (fun m pc hP hd hx hy => by
      rw [← ex] at hx
      rw [← ey] at hy
      obtain ⟨m', st, ag, wz, _⟩ := wideAnd_run hP.frame hP.small (by omega) hP.code hP.far x.n.toNat y.n.toNat hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => valueAt_int_of_wide (Zahl.band h0 h0' x y) (arithWords_result _ _ _ _ _ _) words

theorem wideBor_ok {l1 h1 l2 h2 : Int} (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < 2 ^ w) (x : Zahl l1 h1) (y : Zahl l2 h2) {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 0 (2 ^ w - 1)) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 0 (2 ^ w - 1)) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 0 (2 ^ w - 1)) cb (.int l2 h2) y)
    (h : wideBitL 9 l1 h1 l2 h2 0 (2 ^ w - 1) d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (2 ^ w - 1)) (Zahl.bor w h0 h0' hw1 hw2 x y) := by
  unfold wideBitL at h
  have ex : ((x.n.toNat : Nat) : Int) = x.n := Int.toNat_of_nonneg (by have := x.lo_le; omega)
  have ey : ((y.n.toNat : Nat) : Int) = y.n := Int.toNat_of_nonneg (by have := y.lo_le; omega)
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (arithWords l1 h1 l2 h2 0 (2 ^ w - 1))
      ((x.n.toNat ||| y.n.toNat : Nat) : Int)))
    (fun m pc hP hd hx hy => by
      rw [← ex] at hx
      rw [← ey] at hy
      obtain ⟨m', st, ag, wz, _⟩ := wideOr_run hP.frame hP.small (by omega) hP.code hP.far x.n.toNat y.n.toNat hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words =>
    valueAt_int_of_wide (Zahl.bor w h0 h0' hw1 hw2 x y) (arithWords_result _ _ _ _ _ _) words

theorem wideBxor_ok {l1 h1 l2 h2 : Int} (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < 2 ^ w) (x : Zahl l1 h1) (y : Zahl l2 h2) {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 0 (2 ^ w - 1)) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 0 (2 ^ w - 1)) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 0 (2 ^ w - 1)) cb (.int l2 h2) y)
    (h : wideBitL 10 l1 h1 l2 h2 0 (2 ^ w - 1) d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (2 ^ w - 1)) (Zahl.bxor w h0 h0' hw1 hw2 x y) := by
  unfold wideBitL at h
  have ex : ((x.n.toNat : Nat) : Int) = x.n := Int.toNat_of_nonneg (by have := x.lo_le; omega)
  have ey : ((y.n.toNat : Nat) : Int) = y.n := Int.toNat_of_nonneg (by have := y.lo_le; omega)
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (arithWords l1 h1 l2 h2 0 (2 ^ w - 1))
      ((x.n.toNat ^^^ y.n.toNat : Nat) : Int)))
    (fun m pc hP hd hx hy => by
      rw [← ex] at hx
      rw [← ey] at hy
      obtain ⟨m', st, ag, wz, _⟩ := wideXor_run hP.frame hP.small (by omega) hP.code hP.far x.n.toNat y.n.toNat hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words =>
    valueAt_int_of_wide (Zahl.bxor w h0 h0' hw1 hw2 x y) (arithWords_result _ _ _ _ _ _) words

end Gabbro.Stage0.Senke
