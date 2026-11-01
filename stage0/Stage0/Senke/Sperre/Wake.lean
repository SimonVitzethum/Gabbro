/- Last release with waiters: actual branch, WAKE entry and conditional return.
   These are sequential-thread facts, not a concurrent source refinement. -/
import Stage0.Senke.Sperre.Gib

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}

section
variable {m0 m : Mem} {pc fp : W} {s a p : Nat} {code : List II}
  {f : Nat → W} {c w : W} {L : Lay D}

/-- Last release with nonzero waiters reaches the emitted WAKE-one syscall.
    The waiter count is unchanged; the owner and recursion count are zero. -/
theorem gib_waiters_entry (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f (meW L fp) c w)
    (hc : At code p (gibC L a s)) (hme : MeOK L fp) (last : c - 1 = 0)
    (waiters : w ≠ 0) (bounded : w.toNat < 2 ^ 62) :
    ∃ mw fw, Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 28)), fp⟩ mw ∧
      LS m0 mw fp s a fw 0 0 w ∧ LockInv 0 0 w ∧ FutexArgs fw (BitVec.ofNat 64 a) 129 1 ∧
      StopAt ⟨pc + BitVec.ofNat 64 (16 * (p + 28)), fp⟩ mw (futexReq (BitVec.ofNat 64 a) 129 1) := by
  obtain ⟨m1, f1, steps1, state1, test⟩ := gib_release E h hc hme last
  have branch := ls_brz_ne E state1 (hc.get (j := 20) rfl) (e := 2) rfl (by omega)
    (by rw [test]; exact waiters)
  have prep : At code (p + 21) (futexC a 129 0 (s + 10) (some 1)) := by
    intro j hj
    have := hc (21 + j) (by change j < 8 at hj; rw [gibC_len]; omega)
    rw [show p + 21 + j = p + (21 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  have prep' : At code (p + 21) (futexC a 129 (s + 4) (s + 10) (some 1)) := prep
  obtain ⟨mw, fw, steps2, state2, args, _⟩ := futex_prepare E state1 prep' (by decide)
    (by intro k hk; cases hk; decide)
  exact ⟨mw, fw, steps1.trans (branch.trans steps2), state2,
    ⟨Or.inl ⟨rfl, rfl⟩, bounded⟩, args, futex_entry E state2 (hc.get (j := 28) rfl) args⟩

/-- WAKE returns at most one woken waiter, and the release leaves the invariant
    under the explicitly supplied resume/frame condition. No waiter is removed
    from the memory counter by WAKE: each returning WAIT removes its own entry. -/
theorem gib_waiters_return {spurious : W → W → Mem → Mem → Prop} [FutexOK spurious]
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f 0 0 w)
    (hc : At code p (gibC L a s)) (args : FutexArgs f (BitVec.ofNat 64 a) 129 1)
    {r x : W} {mr : Mem}
    (answer : Kern.ans (futexReq (BitVec.ofNat 64 a) 129 1) m (some (r, x)) mr)
    (resume : LS m0 mr fp s a f 0 0 w) (bounded : w.toNat < 2 ^ 62) :
    (r.toInt < 0 ∨ r.toNat ≤ 1) ∧ ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 28)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 29)), fp⟩ m' ∧
      LS m0 m' fp s a f' 0 0 w ∧ LockInv 0 0 w := by
  obtain ⟨m', steps, state⟩ := futex_return E h (hc.get (j := 28) rfl) args answer resume
  have result : r.toInt < 0 ∨ r.toNat ≤ 1 := by
    by_cases error : r.toInt < 0
    · exact Or.inl error
    · exact Or.inr (FutexOK.wake_return spurious _ _ _ _ _ _ answer (by omega))
  exact ⟨result, m', _, steps, state, ⟨Or.inl ⟨rfl, rfl⟩, bounded⟩⟩

end
end Gabbro.Stage0.Senke
