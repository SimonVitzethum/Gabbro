/- Sequential-thread simulation of the actual contended WAIT path. The explicit
   response and resume invariant describe the environment at a blocking boundary;
   they imply neither fairness nor the missing concurrent `ir_parallel` theorem. -/
import Stage0.Senke.Sperre.Contended
import Stage0.Senke.Sperre.Futex

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}
set_option maxRecDepth 100000

section
variable {m0 m : Mem} {pc fp : W} {s a p : Nat} {code : List II}
  {f : Nat → W} {o c w : W} {L : Lay D}

/-- Register as a waiter, build WAIT, and reach its actual syscall. The lock
    invariant includes foreign ownership and a bounded nonzero waiter count. -/
theorem nimm_wait_entry (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmC L a s)) (hinv : LockInv o c w)
    (room : w.toNat + 1 < 2 ^ 62) :
    ∃ mw fw, Star ⟨pc + BitVec.ofNat 64 (16 * (p + 22)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 36)), fp⟩ mw ∧
      LS m0 mw fp s a fw o c (w + 1) ∧ LockInv o c (w + 1) ∧
      FutexArgs fw (BitVec.ofNat 64 a) 128 (f 4) ∧ fw 0 = f 0 ∧ fw 4 = f 4 ∧
      StopAt ⟨pc + BitVec.ofNat 64 (16 * (p + 36)), fp⟩ mw (futexReq (BitVec.ofNat 64 a) 128 (f 4)) := by
  have inc : At code (p + 22) (addC (a + 16) (s + 5) 1) := by
    intro j hj
    have := hc (22 + j) (by change j < 7 at hj; rw [nimmC_len]; omega)
    rw [show p + 22 + j = p + (22 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  obtain ⟨m1, f1, steps1, state1, keep1⟩ := add_waiters E h inc (by decide)
  have prep : At code (p + 29) (futexC a 128 (s + 4) (s + 10) none) := by
    intro j hj
    have := hc (29 + j) (by change j < 8 at hj; rw [nimmC_len]; omega)
    rw [show p + 29 + j = p + (29 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  obtain ⟨mw, fw, steps2, state2, args, keep2⟩ := futex_prepare E state1 prep (by decide) (by simp)
  have args' : FutexArgs fw (BitVec.ofNat 64 a) 128 (f 4) := by simpa [keep1 4 (by decide)] using args
  have entry := futex_entry E state2 (hc.get (j := 36) rfl) args'
  refine ⟨mw, fw, steps1.trans steps2, state2, hinv.increment room, args', ?_, ?_, entry⟩
  · exact (keep2 0 (by decide)).trans (keep1 0 (by decide))
  · exact (keep2 4 (by decide)).trans (keep1 4 (by decide))

/-- A returned WAIT unregisters this waiter and jumps to instruction 17, the
    actual acquisition retry, retaining this thread's id. Other threads' changes
    are supplied by `resume` and `invariant`, separately from the OS contract. -/
theorem nimm_wait_retry {spurious : W → W → Mem → Mem → Prop} [FutexOK spurious]
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmC L a s)) {seen r x o' c' w' : W} {mr : Mem}
    (args : FutexArgs f (BitVec.ofNat 64 a) 128 seen)
    (answer : Kern.ans (futexReq (BitVec.ofNat 64 a) 128 seen) m (some (r, x)) mr)
    (resume : LS m0 mr fp s a f o' c' w') (invariant : LockInv o' c' w')
    (registered : 0 < w'.toNat) :
    ((∃ observed, mr.rd32 (BitVec.ofNat 64 a) = some observed ∧ observed ≠ seen.setWidth 32) ∨
      spurious (BitVec.ofNat 64 a) seen m mr) ∧
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 36)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 17)), fp⟩ m' ∧
      LS m0 m' fp s a f' o' c' (w' + BitVec.ofInt 64 (-1)) ∧
      LockInv o' c' (w' + BitVec.ofInt 64 (-1)) ∧ f' 0 = f 0 := by
  refine ⟨FutexOK.wait_return _ _ _ _ _ _ answer, ?_⟩
  obtain ⟨m1, steps1, state1⟩ := futex_return E h (hc.get (j := 36) rfl) args answer resume
  have dec : At code (p + 37) (addC (a + 16) (s + 5) (-1)) := by
    intro j hj
    have := hc (37 + j) (by change j < 7 at hj; rw [nimmC_len]; omega)
    rw [show p + 37 + j = p + (37 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  obtain ⟨m2, f2, steps2, state2, keep2⟩ := add_waiters E state1 dec (by decide)
  have ins := E.ins state2.ag (hc.get (j := 44) rfl)
  simp only [ci] at ins
  have jump : Star ⟨pc + BitVec.ofNat 64 (16 * (p + 44)), fp⟩ m2
      ⟨pc + BitVec.ofNat 64 (16 * (p + 17)), fp⟩ m2 := by
    refine ls_star ins (by decide) ?_
    have run := run_jmp (t := ⟨pc + BitVec.ofNat 64 (16 * (p + 44)), fp⟩) ins
    rw [sx_lit (show lit32 (-(16 * 27)) = true by decide)] at run
    have eq : pc + BitVec.ofNat 64 (16 * (p + 44)) + BitVec.ofInt 64 (-(16 * 27)) =
        pc + BitVec.ofNat 64 (16 * (p + 17)) := by
      rw [show 16 * (p + 44) = 16 * (p + 17) + 432 by omega, BitVec.ofNat_add,
        BitVec.ofInt_neg]
      change pc + (BitVec.ofNat 64 (16 * (p + 17)) + (432 : W)) + -(432 : W) = _
      rw [← BitVec.add_assoc, ← BitVec.sub_eq_add_neg, BitVec.add_sub_cancel]
    rwa [eq] at run
  exact ⟨m2, f2, steps1.trans (steps2.trans jump), state2, invariant.decrement registered,
    by simpa [upd] using keep2 0 (by decide)⟩

end
end Gabbro.Stage0.Senke
