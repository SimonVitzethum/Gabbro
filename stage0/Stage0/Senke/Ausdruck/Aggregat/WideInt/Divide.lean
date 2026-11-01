/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Divide.lean
  Subject:   Unsigned and signed division and remainder on integers of any width.

  The division kernels leave the quotient in the dividend's slots and the remainder in the divisor's slots
  (`d + k ..`). The quotient is the result as it stands; the remainder is copied down by `copyWords`
  (`withCopy_run`, exact footprint `d .. d + k`). A zero divisor is excluded by the types (`1 ≤ l2` for the
  unsigned operators, an interval without zero for the signed ones), so the kernels have no stop path. The
  signed quotient of the minimum by `-1` is the one value outside the signed range of the operand width: the
  model's result interval already holds it (`betragMax`), and the kernel's modular limbs are its canonical
  encoding at that width.
-/
module
public import Stage0.Senke.Welt.WeltAt
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Copy
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Operands
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Run
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.Final
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

theorem tdiv_toNat {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a.tdiv b = ((a.toNat / b.toNat : Nat) : Int) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [Int.tdiv_eq_ediv_nonneg ha]
  simp only [Int.toNat_natCast]
  rfl

theorem tmod_toNat {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a.tmod b = ((a.toNat % b.toNat : Nat) : Int) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [Int.tmod_eq_emod_of_nonneg ha]
  simp only [Int.toNat_natCast]
  rfl

/-- A nonnegative value below `2 ^ (64 j)` stays below it at any larger width. -/
theorem unsignedFits_zahl {lo hi : Int} (h0 : 0 ≤ lo) (z : Zahl lo hi) {k : Nat}
    (hk : integerWords lo hi ≤ k) : z.n.toNat < 2 ^ (64 * k) := by
  have range := integerWords_nonnegative h0 z.lo_le z.le_hi
  have capacity : (2 : Int) ^ (64 * integerWords lo hi) ≤ 2 ^ (64 * k) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (show 64 * integerWords lo hi ≤ 64 * k by omega)
  have natural : ((z.n.toNat : Nat) : Int) < ((2 ^ (64 * k) : Nat) : Int) := by
    rw [Int.toNat_of_nonneg range.1]
    push_cast
    omega
  exact_mod_cast natural

section
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
variable {W : Runner.Mem → Prop} {fp : Runner.W} {K d : Nat} {c : List II} {top : Nat}
variable {m : Runner.Mem} {pc : Runner.W}

/-- A kernel followed by a copy of the `k` limbs at `d + k` down to `d`. -/
theorem withCopy_run {kern : List II} {k : Nat} {ws : List Runner.W} (hws : ws.length = k)
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hd : d + 2 * k ≤ K) (hk : 1 ≤ k)
    (hc : CodeAt m pc (kern ++ copyWords k d (d + k)))
    (hfar : CodeFar pc (kern ++ copyWords k d (d + k)).length fp K)
    (first : ∃ m1, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * kern.length), fp⟩ m1 ∧ Agree fp d K m m1 ∧
      WordsAt m1 fp (d + k) ws) :
    ∃ m2, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (kern ++ copyWords k d (d + k)).length), fp⟩ m2 ∧
      Agree fp d K m m2 ∧ WordsAt m2 fp d ws := by
  obtain ⟨m1, run1, ch1, input⟩ := first
  have hfar' : CodeFar pc (kern.length + k) fp K := by simpa only [List.length_append, copyWords_length] using hfar
  have far2 := codeFar_right (n := kern.length) hfar'
  have code2 : CodeAt m1 (pc + BitVec.ofNat 64 (16 * kern.length)) (copyWords k d (d + k)) :=
    (codeAt_right hc).agree ch1 (by simpa only [copyWords_length] using far2)
  obtain ⟨m2, run2, ch2, output⟩ := copyWords_run (fp := fp) (K := K) ws (m := m1)
    (pc := pc + BitVec.ofNat 64 (16 * kern.length)) (dst := d) (src := d + k) (hF.agree ch1) hK
    (by omega) (by omega) (Or.inl (by omega)) (by rw [hws]; exact code2) (by rw [hws]; exact far2) input
  refine ⟨m2, ?_, ch1.trans (Agree.widen ch2 (by omega)), output⟩
  have : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * kern.length) + BitVec.ofNat 64 (16 * ws.length), fp⟩ m2 :=
    run1.trans run2
  simpa only [List.length_append, copyWords_length, pc_add, hws] using this

theorem wideDiv_ok {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 0 h1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 0 h1) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 0 h1) cb (.int l2 h2) y)
    (h : wideDivL l1 h1 l2 h2 0 h1 d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 h1) (Zahl.div h0 h1' x y) := by
  unfold wideDivL at h
  have positive := Nat.le_trans (integerWords_pos' l1 h1) (arithWords_left l1 h1 l2 h2 0 h1)
  have ex : ((x.n.toNat : Nat) : Int) = x.n := Int.toNat_of_nonneg (by have := x.lo_le; omega)
  have ey : ((y.n.toNat : Nat) : Int) = y.n := Int.toNat_of_nonneg (by have := y.lo_le; omega)
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (arithWords l1 h1 l2 h2 0 h1)
      ((x.n.toNat / y.n.toNat : Nat) : Int)))
    (fun m pc hP hd hx hy => by
      rw [← ex] at hx
      rw [← ey] at hy
      obtain ⟨m', st, ag, wz, _⟩ := wideDiv_run hP.frame hP.small (by omega) positive hP.code hP.far x.n.toNat y.n.toNat
        (by have := y.lo_le; omega) (unsignedFits_zahl (by omega) y (arithWords_right _ _ _ _ _ _))
        (unsignedFits_zahl h0 x (arithWords_left _ _ _ _ _ _)) hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => by
    have value : (Zahl.div h0 h1' x y).n = ((x.n.toNat / y.n.toNat : Nat) : Int) :=
      tdiv_toNat (by have := x.lo_le; omega) (by have := y.lo_le; omega)
    exact valueAt_int_of_wide (Zahl.div h0 h1' x y) (arithWords_result _ _ _ _ _ _) (by rw [value]; exact words)

theorem wideRem_ok {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + arithWords l1 h1 l2 h2 0 (h2 - 1)) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + arithWords l1 h1 l2 h2 0 (h2 - 1)) cb ρ W reserved →
      ValueOk L m pc fp K (d + arithWords l1 h1 l2 h2 0 (h2 - 1)) cb (.int l2 h2) y)
    (h : wideRemL l1 h1 l2 h2 0 (h2 - 1) d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (h2 - 1)) (Zahl.rem h0 h1' x y) := by
  unfold wideRemL at h
  have positive := Nat.le_trans (integerWords_pos' l1 h1) (arithWords_left l1 h1 l2 h2 0 (h2 - 1))
  have ex : ((x.n.toNat : Nat) : Int) = x.n := Int.toNat_of_nonneg (by have := x.lo_le; omega)
  have ey : ((y.n.toNat : Nat) : Int) = y.n := Int.toNat_of_nonneg (by have := y.lo_le; omega)
  have run := wideBinary_ok x y (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding (arithWords l1 h1 l2 h2 0 (h2 - 1))
      ((x.n.toNat % y.n.toNat : Nat) : Int)))
    (fun m pc hP hd hx hy => by
      rw [← ex] at hx
      rw [← ey] at hy
      refine withCopy_run (integerEncoding_length _ _) hP.frame hP.small (by omega) positive hP.code hP.far ?_
      obtain ⟨m', st, ag, _, wz⟩ := wideDiv_run hP.frame hP.small (by omega) positive
        (codeAt_left hP.code) (codeFar_left (by simpa only [List.length_append, copyWords_length] using hP.far))
        x.n.toNat y.n.toNat (by have := y.lo_le; omega)
        (unsignedFits_zahl (by omega) y (arithWords_right _ _ _ _ _ _))
        (unsignedFits_zahl h0 x (arithWords_left _ _ _ _ _ _)) hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => by
    have value : (Zahl.rem h0 h1' x y).n = ((x.n.toNat % y.n.toNat : Nat) : Int) :=
      tmod_toNat (by have := x.lo_le; omega) (by have := y.lo_le; omega)
    exact valueAt_int_of_wide (Zahl.rem h0 h1' x y) (arithWords_result _ _ _ _ _ _) (by rw [value]; exact words)

theorem wideSdiv_ok {l1 h1 l2 h2 : Int} (hb : 1 ≤ l2 ∨ h2 ≤ -1) (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + signedArithWords l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1)) = some (cb, tb) →
      tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + signedArithWords l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1)) cb ρ W reserved →
      ValueOk L m pc fp K (d + signedArithWords l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1)) cb
        (.int l2 h2) y)
    (h : wideSdivL l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1) d fa fb = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int (-(betragMax l1 h1)) (betragMax l1 h1)) (Zahl.sdiv hb x y) := by
  unfold wideSdivL at h
  have positive := Nat.le_trans (integerWords_pos' l1 h1)
    (Nat.le_trans (integerWords_le_signedWords l1 h1)
      (signedArithWords_left l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1)))
  have run := wideBinary_ok x y (Nat.le_trans (integerWords_le_signedWords _ _) (signedArithWords_left _ _ _ _ _ _))
    (Nat.le_trans (integerWords_le_signedWords _ _) (signedArithWords_right _ _ _ _ _ _)) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding
      (signedArithWords l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1)) (x.n.tdiv y.n)))
    (fun m pc hP hd hx hy => by
      have fx := signedFits_zahl x (signedArithWords_left l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1))
      have fy := signedFits_zahl y (signedArithWords_right l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1))
      obtain ⟨m', st, ag, wz, _⟩ := wideSdiv_run hP.frame hP.small (by omega) positive hP.code hP.far x.n y.n
        (by have := y.lo_le; have := y.le_hi; omega) fx.1 fx.2 fy.1 fy.2 hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => valueAt_int_of_wide (Zahl.sdiv hb x y) (signedArithWords_result _ _ _ _ _ _) words

theorem wideSrem_ok {l1 h1 l2 h2 : Int} (hb : 1 ≤ l2 ∨ h2 ≤ -1) (x : Zahl l1 h1) (y : Zahl l2 h2)
    {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + signedArithWords l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1)) =
      some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + signedArithWords l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1)) cb ρ W
        reserved →
      ValueOk L m pc fp K (d + signedArithWords l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1)) cb
        (.int l2 h2) y)
    (h : wideSremL l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1) d fa fb = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1)) (Zahl.srem hb x y) := by
  unfold wideSremL at h
  have positive := Nat.le_trans (integerWords_pos' l1 h1)
    (Nat.le_trans (integerWords_le_signedWords l1 h1)
      (signedArithWords_left l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1)))
  have run := wideBinary_ok x y (Nat.le_trans (integerWords_le_signedWords _ _) (signedArithWords_left _ _ _ _ _ _))
    (Nat.le_trans (integerWords_le_signedWords _ _) (signedArithWords_right _ _ _ _ _ _)) iha ihb h hK hp
    (R := fun m' => WordsAt m' fp d (integerEncoding
      (signedArithWords l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1)) (x.n.tmod y.n)))
    (fun m pc hP hd hx hy => by
      have fx := signedFits_zahl x (signedArithWords_left l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1))
      have fy := signedFits_zahl y (signedArithWords_right l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1))
      refine withCopy_run (integerEncoding_length _ _) hP.frame hP.small (by omega) positive hP.code hP.far ?_
      obtain ⟨m', st, ag, _, wz⟩ := wideSdiv_run hP.frame hP.small (by omega) positive
        (codeAt_left hP.code) (codeFar_left (by simpa only [List.length_append, copyWords_length] using hP.far))
        x.n y.n (by have := y.lo_le; have := y.le_hi; omega) fx.1 fx.2 fy.1 fy.2 hx hy
      exact ⟨m', st, ag, wz⟩)
  exact run.mono fun _ words => valueAt_int_of_wide (Zahl.srem hb x y) (signedArithWords_result _ _ _ _ _ _) words

end

end Gabbro.Stage0.Senke
