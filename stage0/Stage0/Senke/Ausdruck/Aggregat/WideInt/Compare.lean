/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Compare.lean
  Subject:   `<`, `<=` and `==` on integers of any width.

  Both operands are extended to `k = max (signedWords) + 1` limbs, so their difference fits the signed range of
  `k` limbs and the kernels read it exactly: `<` is the sign of `x - y`, `==` is the zero test of the
  difference. `<=` is `¬ (y < x)` with the operands lowered in the swapped order; the flag is flipped by an
  actual `xor 1` instruction.
-/
module
public import Stage0.Senke.Welt.WeltAt
public import Stage0.Senke.Ausdruck.Wort.Wort
public import Stage0.Senke.Ausdruck.Arithmetik.Interval
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Operands
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.CompareRun
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

/-- Two values of the signed range of `M` limbs differ by less than `2 ^ (64 M)`. -/
theorem diff_range {M : Nat} (hM : 1 ≤ M) {x y : Int}
    (hx : -(2 ^ 63 * 2 ^ (64 * (M - 1))) ≤ x ∧ x < 2 ^ 63 * 2 ^ (64 * (M - 1)))
    (hy : -(2 ^ 63 * 2 ^ (64 * (M - 1))) ≤ y ∧ y < 2 ^ 63 * 2 ^ (64 * (M - 1))) :
    (-(2 ^ 63 * 2 ^ (64 * M)) ≤ x - y ∧ x - y < 2 ^ 63 * 2 ^ (64 * M)) ∧
    (-(2 ^ (64 * (M + 1))) < x - y ∧ x - y < 2 ^ (64 * (M + 1))) := by
  have positive : (0 : Int) < 2 ^ (64 * (M - 1)) := Int.pow_pos (by decide)
  have e1 : (2 : Int) ^ (64 * M) = 2 ^ 64 * 2 ^ (64 * (M - 1)) := by
    rw [← Int.pow_add]
    congr 1
    omega
  have e2 : (2 : Int) ^ (64 * (M + 1)) = 2 ^ 64 * 2 ^ (64 * M) := by
    rw [← Int.pow_add]
    congr 1
    omega
  have c63 : (2 : Int) ^ 63 = 9223372036854775808 := by norm_num
  have c64 : (2 : Int) ^ 64 = 18446744073709551616 := by norm_num
  rw [c63] at hx hy ⊢
  rw [c64] at e1 e2
  constructor <;> constructor <;> omega

theorem valueAt_bool {D : Deklaration} {L : Lay D} {m : Runner.Mem} {fp : Runner.W} {base : Nat} {v : Bool}
    (read : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (Runner.IR.bool v)) :
    ValueAt L m fp base .bool v :=
  ValueAt.of_enc rfl read (bool_word v)

section
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
variable {W : Runner.Mem → Prop} {fp : Runner.W} {K d : Nat} {c : List II} {top : Nat}
variable {m : Runner.Mem} {pc : Runner.W}

theorem wideLt_ok {l1 h1 l2 h2 : Int} (x : Zahl l1 h1) (y : Zahl l2 h2) {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + compareWords l1 h1 l2 h2) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + compareWords l1 h1 l2 h2) cb ρ W reserved →
      ValueOk L m pc fp K (d + compareWords l1 h1 l2 h2) cb (.int l2 h2) y)
    (h : wideLtL l1 h1 l2 h2 d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (decide (x.n < y.n)) := by
  unfold wideLtL at h
  have left : integerWords l1 h1 ≤ compareWords l1 h1 l2 h2 :=
    Nat.le_trans (integerWords_le_signedWords _ _) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _))
  have right : integerWords l2 h2 ≤ compareWords l1 h1 l2 h2 :=
    Nat.le_trans (integerWords_le_signedWords _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))
  have run := wideBinary_ok x y left right iha ihb h hK hp
    (R := fun m' => m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some (Runner.IR.bool (decide (x.n < y.n))))
    (fun m pc hP hd hx hy => by
      have fx := signedFits_zahl x (Nat.le_max_left (signedWords l1 h1) (signedWords l2 h2))
      have fy := signedFits_zahl y (Nat.le_max_right (signedWords l1 h1) (signedWords l2 h2))
      have range := diff_range (Nat.le_trans (integerWords_pos' l1 h1)
        (Nat.le_trans (integerWords_le_signedWords l1 h1) (Nat.le_max_left _ _))) fx fy
      obtain ⟨m', st, ag, rd⟩ := wideLt_run (n := max (signedWords l1 h1) (signedWords l2 h2)) hP.frame hP.small
        (by unfold compareWords at hd; omega) hP.code hP.far x.n y.n hx hy range.1.1 range.1.2
      exact ⟨m', st, ag, rd⟩)
  exact run.mono fun _ read => valueAt_bool read

theorem wideEq_ok {l1 h1 l2 h2 : Int} (x : Zahl l1 h1) (y : Zahl l2 h2) {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb (d + compareWords l1 h1 l2 h2) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + compareWords l1 h1 l2 h2) cb ρ W reserved →
      ValueOk L m pc fp K (d + compareWords l1 h1 l2 h2) cb (.int l2 h2) y)
    (h : wideEqL l1 h1 l2 h2 d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (decide (x.n = y.n)) := by
  unfold wideEqL at h
  have left : integerWords l1 h1 ≤ compareWords l1 h1 l2 h2 :=
    Nat.le_trans (integerWords_le_signedWords _ _) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _))
  have right : integerWords l2 h2 ≤ compareWords l1 h1 l2 h2 :=
    Nat.le_trans (integerWords_le_signedWords _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))
  have run := wideBinary_ok x y left right iha ihb h hK hp
    (R := fun m' => m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some (Runner.IR.bool (decide (x.n = y.n))))
    (fun m pc hP hd hx hy => by
      have fx := signedFits_zahl x (Nat.le_max_left (signedWords l1 h1) (signedWords l2 h2))
      have fy := signedFits_zahl y (Nat.le_max_right (signedWords l1 h1) (signedWords l2 h2))
      have range := diff_range (Nat.le_trans (integerWords_pos' l1 h1)
        (Nat.le_trans (integerWords_le_signedWords l1 h1) (Nat.le_max_left _ _))) fx fy
      obtain ⟨m', st, ag, rd⟩ := wideEq_run (n := max (signedWords l1 h1) (signedWords l2 h2)) hP.frame hP.small
        (by unfold compareWords at hd; omega) hP.code hP.far x.n y.n hx hy range.2.1 range.2.2
      exact ⟨m', st, ag, rd⟩)
  exact run.mono fun _ read => valueAt_bool read

/-- The flag word, flipped by a constant and an `xor`. -/
theorem flipFlag_ok {b : Runner.W} (fits : d + 2 ≤ K)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some b)
    (pre : Pre L m pc fp K d [ci 1 (d + 1 : Nat) 1 0, ci 10 (d : Nat) (d : Nat) (d + 1 : Nat)] ρ W reserved) :
    Ok m pc fp K d [ci 1 (d + 1 : Nat) 1 0, ci 10 (d : Nat) (d : Nat) (d + 1 : Nat)]
      (· = b ^^^ BitVec.ofInt 64 1) := by
  have start : Pre L m pc fp K d
      ([ci 1 (d + 1 : Nat) 1 0] ++ [ci 10 (d : Nat) (d : Nat) (d + 1 : Nat)]) ρ W reserved := pre
  obtain ⟨m1, run1, changed1, one, readOne, equal⟩ := const_ok (d := d + 1)
    { start.left with ctx := by have := pre.ctx; omega } (by decide) (by omega)
  subst one
  have next := start.next (changed1.mono (Nat.le_succ d)) (Nat.le_refl _) (by omega)
  have preserved : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some b := by
    rw [agree_rd_low changed1 pre.frame.room (by omega) (by omega)]
    exact read
  obtain ⟨m2, run2, changed2, flag, readFlag, encoded⟩ := eng_bin_ok next
    (d := d) (a := d) (b := d + 1) (by omega) (by omega) (by omega)
    preserved readOne (g := fun a b => some (a ^^^ b)) rfl (by decide) rfl
  refine ⟨m2, ?_, (changed1.mono (Nat.le_succ d)).trans changed2, flag, readFlag, encoded⟩
  simpa only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, pc_add]
    using run1.trans run2

theorem wideLe_ok {l1 h1 l2 h2 : Int} (x : Zahl l1 h1) (y : Zahl l2 h2) {fa fb : Nat → Option (List II × Nat)}
    (iha : ∀ ca ta, fa (d + compareWords l2 h2 l1 h1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + compareWords l2 h2 l1 h1) ca ρ W reserved →
      ValueOk L m pc fp K (d + compareWords l2 h2 l1 h1) ca (.int l1 h1) x)
    (ihb : ∀ cb tb, fb d = some (cb, tb) → tb ≤ K → ∀ m pc, Pre L m pc fp K d cb ρ W reserved →
      ValueOk L m pc fp K d cb (.int l2 h2) y)
    (h : wideLeL l1 h1 l2 h2 d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (decide (x.n ≤ y.n)) := by
  unfold wideLeL at h
  have left : integerWords l2 h2 ≤ compareWords l2 h2 l1 h1 :=
    Nat.le_trans (integerWords_le_signedWords _ _) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _))
  have right : integerWords l1 h1 ≤ compareWords l2 h2 l1 h1 :=
    Nat.le_trans (integerWords_le_signedWords _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))
  have run := wideBinary_ok y x left right ihb iha h hK hp
    (R := fun m' => m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some (Runner.IR.bool (decide (x.n ≤ y.n))))
    (fun m pc hP hd hx hy => by
      have fy := signedFits_zahl y (Nat.le_max_left (signedWords l2 h2) (signedWords l1 h1))
      have fx := signedFits_zahl x (Nat.le_max_right (signedWords l2 h2) (signedWords l1 h1))
      have range := diff_range (Nat.le_trans (integerWords_pos' l2 h2)
        (Nat.le_trans (integerWords_le_signedWords l2 h2) (Nat.le_max_left _ _))) fy fx
      have codeAll := hP.code
      have farAll : CodeFar pc (wideLtC (compareWords l2 h2 l1 h1 - 1) d).length fp K := by
        have := hP.far
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        exact codeFar_left (n := (wideLtC (compareWords l2 h2 l1 h1 - 1) d).length) (k := 2) this
      obtain ⟨m1, st1, ag1, rd1⟩ := wideLt_run (n := max (signedWords l2 h2) (signedWords l1 h1))
        hP.frame hP.small (by unfold compareWords at hd; omega) (codeAt_left codeAll) farAll y.n x.n hx hy
        range.1.1 range.1.2
      have next := hP.next ag1 (Nat.le_refl d) (by omega)
      obtain ⟨m2, st2, ag2, w, read2, hw⟩ := flipFlag_ok (by unfold compareWords at hd; omega) rd1 next
      refine ⟨m2, ?_, ag1.trans ag2, ?_⟩
      · have := st1.trans st2
        simpa only [List.length_append, List.length_cons, List.length_nil, pc_add] using this
      · rw [read2, hw, bool_word, not_word]
        by_cases hlt : y.n < x.n
        · have hn : ¬ x.n ≤ y.n := by omega
          simp [hlt, hn, Runner.IR.bool]
        · have hn : x.n ≤ y.n := by omega
          simp [hlt, hn, Runner.IR.bool])
  exact run.mono fun _ read => valueAt_bool read

end

end Gabbro.Stage0.Senke
