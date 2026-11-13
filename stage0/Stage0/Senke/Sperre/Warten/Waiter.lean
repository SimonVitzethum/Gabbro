/- The actual waiter-counter CAS loop, with its scratch base explicit. -/
module
public import Stage0.Senke.Sperre.Nimm
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern]
section
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
    {i b : Nat} (hb : b + 4 < 18)
    (hi : code[i]? = some (ci 22 ((s + (b + 4) : Nat) : Int)
      ((s + b : Nat) : Int) ((s + (b + 1) : Nat) : Int)))
    (hae : f b = BitVec.ofNat 64 (a + 16)) (heq : f (b + 1) = w) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m' ∧
      LS m0 m' fp s a (upd f (b + 4) w) o c (f (b + 2)) := by
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hcas := cas_spec (e := f (b + 1)) (n := f (b + 2)) h.w (by rw [h.ag.wr]; exact E.wr2)
  rw [heq, ite_eq_left rfl] at hcas
  have hL := h.waiters E (f (b + 2))
  have hF := E.frameK hL.ag
  refine ⟨_, ls_star hI (by decide) ?_, hL.slot E hb w⟩
  rw [← pc_next]
  simp only [op]
  refine f2_run hI ?_
  rw [sx_nat (d := s + b) (by omega)]
  simp only [ld]
  refine run_rd64 (h.sl b (by omega)) (f3_run hI ?_)
  rw [sx_nat (d := s + (b + 1)) (by omega)]
  refine run_rd64 (h.sl (b + 1) (by omega)) ?_
  rw [slot_plus8, show s + (b + 1) + 1 = s + (b + 2) by omega]
  refine run_rd64 (h.sl (b + 2) (by omega)) ?_
  rw [hae]
  refine .ask (a := some (w, 0)) (m' := write m (BitVec.ofNat 64 (a + 16)) 8 (f (b + 2)).toNat)
    (by simp only [memAns, heq, hcas]) ?_
  simp only [opt_some, ret1]
  have hI1 := E.ins hL.ag hi
  simp only [ci] at hI1
  refine f1_run hI1 ?_
  rw [sx_nat (d := s + (b + 4)) (by omega)]
  exact run_wr64 (wr64_some (hF.wr _ (by omega)))

/-- One successful iteration of the seven emitted instructions. The explicit
    scratch base covers both the old base five and the ticket lock's base seven.
    No other thread interferes during these seven instructions. -/
theorem add_waiters (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    {p b : Nat} {delta : Int} (hc : At code p (addC (a + 16) (s + b) delta))
    (hb : b + 4 < 18) (hd : lit32 delta = true) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' o c (w + BitVec.ofInt 64 delta) ∧
      (∀ j, j < b → f' j = f j) := by
  have ht := E.top
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := b) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_ld E h1 (hc.get (j := 1) rfl) (d := b + 1) (e := b)
    (by omega) rfl (by omega) (by omega)
    (by simp only [upd_self, BitVec.ofInt_natCast]; exact h1.w)
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := b + 3) (by omega) (by omega) hd
  obtain ⟨m4, s4, h4⟩ := ls_bin E h3 (hc.get (j := 3) rfl) (d := b + 2) (e := b + 1) (g' := b + 3)
    rfl (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (r := w + BitVec.ofInt 64 delta) (by simp [upd])
  have hc4 : code[p + 4]? = some (ci 22 ((s + (b + 4) : Nat) : Int)
      ((s + b : Nat) : Int) ((s + (b + 1) : Nat) : Int)) := by
    simpa only [Nat.add_assoc] using hc.get (j := 4) rfl
  obtain ⟨m5, s5, h5⟩ := ls_cas_waiters E h4 hb hc4
    (by simp [upd]; exact_mod_cast (BitVec.ofInt_natCast 64 (a + 16))) (by simp [upd])
  obtain ⟨m6, s6, h6⟩ := ls_bin E h5 (hc.get (j := 5) rfl) (d := b + 4) (e := b + 4) (g' := b + 1)
    rfl (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (r := 1)
    (by simp [upd, Runner.IR.bool])
  have s7 := ls_brz_ne E h6 (hc.get (j := 6) rfl) (e := b + 4) (by omega) (by omega) (by simp [upd])
  refine ⟨m6, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7))))),
    h6.congr rfl rfl (by simp [upd]), ?_⟩
  intro j hj
  simp [upd, show j ≠ b by omega, show j ≠ b + 1 by omega, show j ≠ b + 2 by omega,
    show j ≠ b + 3 by omega, show j ≠ b + 4 by omega]

end
end Gabbro.Stage0.Senke
