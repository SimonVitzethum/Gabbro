/- Actual waiter-counter CAS loop: sequential successful iteration, with explicit
   bounds for interpreting the modular word arithmetic as a natural counter. -/
module
public import Stage0.Senke.Sperre.Nimm
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
set_option linter.unusedSectionVars false

/-- The thread-independent lock-word invariant at stable boundaries. Foreign
    ownership and nonzero waiters are allowed. Counter overflow is excluded
    explicitly; no bound on waiting time or number of retries follows. -/
def LockInv (o c w : W) : Prop :=
  ((o = 0 ∧ c = 0) ∨ (o ≠ 0 ∧ 1 ≤ c.toNat ∧ c.toNat < 2 ^ 62)) ∧ w.toNat < 2 ^ 62

section
variable [Kern]
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

/-- A write to the waiter word preserves the other two words and the frame. -/
theorem LS.waiters (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) (w' : W) :
    LS m0 (write m (BitVec.ofNat 64 (a + 16)) 8 w'.toNat) fp s a f o c w' := by
  have hfar := E.far
  have htop := E.top
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, h.ag.trans (agreeK_lk (by omega) (by omega) htop _)⟩
  · rw [rd64_write_far (far_lk_slot (y := a + 16) hfar htop hj (by omega) (by omega))]; exact h.sl j hj
  · rw [rd64_write_far (far_lk_lk (y := a + 16) (z := a) (by omega) (by omega) (by omega))]; exact h.o
  · rw [rd64_write_far (far_lk_lk (y := a + 16) (z := a + 8) (by omega) (by omega) (by omega))]; exact h.c
  · exact rd64_wr64 (wr64_some (by rw [h.ag.wr]; exact E.wr2)) (rd64_some_all h.w)

/-- The successful CAS in `addC`, returning the previous waiter count. -/
theorem ls_cas_waiters (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    {i : Nat} (hi : code[i]? = some (ci 22 ((s + 9 : Nat) : Int) ((s + 5 : Nat) : Int) ((s + 6 : Nat) : Int)))
    (hae : f 5 = BitVec.ofNat 64 (a + 16)) (heq : f 6 = w) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m' ∧
      LS m0 m' fp s a (upd f 9 w) o c (f 7) := by
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hcas := cas_spec (e := f 6) (n := f 7) h.w (by rw [h.ag.wr]; exact E.wr2)
  rw [heq, ite_eq_left rfl] at hcas
  have hL := h.waiters E (f 7)
  have hF := E.frameK hL.ag
  refine ⟨_, ls_star hI (by decide) ?_, hL.slot E (by omega) w⟩
  rw [← pc_next]
  simp only [op]
  refine f2_run hI ?_
  rw [sx_nat (d := s + 5) (by omega)]
  simp only [ld]
  refine run_rd64 (h.sl 5 (by omega)) (f3_run hI ?_)
  rw [sx_nat (d := s + 6) (by omega)]
  refine run_rd64 (h.sl 6 (by omega)) ?_
  rw [slot_plus8]
  refine run_rd64 (h.sl 7 (by omega)) ?_
  rw [hae]
  refine .ask (a := some (w, 0)) (m' := write m (BitVec.ofNat 64 (a + 16)) 8 (f 7).toNat)
    (by simp only [memAns, heq, hcas]) ?_
  simp only [opt_some, ret1]
  have hI1 := E.ins hL.ag hi
  simp only [ci] at hI1
  refine f1_run hI1 ?_
  rw [sx_nat (d := s + 9) (by omega)]
  exact run_wr64 (wr64_some (hF.wr _ (by omega)))

/-- One complete iteration of the emitted waiter increment/decrement loop.
    No other thread interferes during these seven instructions. -/
theorem add_waiters (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    {p : Nat} {delta : Int} (hc : At code p (addC (a + 16) (s + 5) delta))
    (hd : lit32 delta = true) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' o c (w + BitVec.ofInt 64 delta) ∧
      (∀ j, j < 5 → f' j = f j) := by
  have ht := E.top
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := 5) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_ld E h1 (hc.get (j := 1) rfl) (d := 6) (e := 5) (by omega) rfl (by omega) (by omega)
    (by simp only [upd_self, BitVec.ofInt_natCast]; exact h1.w)
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := 8) (by omega) (by omega) hd
  obtain ⟨m4, s4, h4⟩ := ls_bin E h3 (hc.get (j := 3) rfl) (d := 7) (e := 6) (g' := 8) rfl (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (r := w + BitVec.ofInt 64 delta) (by simp [upd])
  have hc4 : code[p + 4]? = some (ci 22 ((s + 9 : Nat) : Int) ((s + 5 : Nat) : Int) ((s + 6 : Nat) : Int)) := by
    simpa only [show s + 5 + 4 = s + 9 by omega, show s + 5 + 1 = s + 6 by omega]
      using hc.get (j := 4) rfl
  obtain ⟨m5, s5, h5⟩ := ls_cas_waiters E h4 hc4 (by simp only [upd, ite_eq_left, show (5 : Nat) ≠ 7 by decide,
      show (5 : Nat) ≠ 8 by decide, show (5 : Nat) ≠ 6 by decide]; exact BitVec.ofInt_natCast _ _) (by simp [upd])
  obtain ⟨m6, s6, h6⟩ := ls_bin E h5 (hc.get (j := 5) rfl) (d := 9) (e := 9) (g' := 6) rfl (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (r := 1)
    (by simp [upd, Runner.IR.bool])
  have s7 := ls_brz_ne E h6 (hc.get (j := 6) rfl) (e := 9) (by omega) (by omega) (by simp [upd])
  refine ⟨m6, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7))))),
    h6.congr rfl rfl (by simp [upd]), ?_⟩
  intro j hj
  simp [upd, show j ≠ 5 by omega, show j ≠ 6 by omega, show j ≠ 7 by omega,
    show j ≠ 8 by omega, show j ≠ 9 by omega]

end

/-- Natural-counter interpretation requires room before an increment. -/
theorem LockInv.increment {o c w : W} (h : LockInv o c w) (room : w.toNat + 1 < 2 ^ 62) :
    LockInv o c (w + 1) := by
  refine ⟨h.1, ?_⟩
  simp only [BitVec.toNat_add]
  change (w.toNat + 1) % 2 ^ 64 < 2 ^ 62
  omega

/-- A registered waiter can decrement without underflow. -/
theorem LockInv.decrement {o c w : W} (h : LockInv o c w) (positive : 0 < w.toNat) :
    LockInv o c (w + BitVec.ofInt 64 (-1)) := by
  refine ⟨h.1, ?_⟩
  have hw := h.2
  have eq : w + BitVec.ofInt 64 (-1) = w - 1 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rw [eq, BitVec.toNat_sub_of_le (show (1 : W) ≤ w from by
    rw [BitVec.le_def]; change 1 ≤ w.toNat; omega)]
  change w.toNat - 1 < 2 ^ 62
  omega

end Gabbro.Stage0.Senke
