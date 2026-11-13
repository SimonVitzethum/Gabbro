/- Give with waiters: the locked serving update and the actual WAKE-all call. -/
module
public import Stage0.Senke.Sperre.Warten.Futex
public import Stage0.Senke.Sperre.Ticket.Schritt
public import Stage0.Senke.Sperre.Ticket.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}
section
variable {m0 m : Mem} {pc fp : W} {s a p : Nat} {code : List II}
  {f : Nat → W} {next n w : W} {L : Lay D}

/-- Serving advances while next and the waiter count stay unchanged. The next
    word is arbitrary: in a valid contended state more than one ticket can be
    outstanding. This includes the `(n+1,n,w)` sequential code case. -/
theorem gibT_waiters_read (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f next n w)
    (hc : At code p (gibT L a s)) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' next (n + 1) w ∧ f' 2 = w := by
  have htop := E.top
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_ld E h1 (hc.get (j := 1) rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := n) (by
      show m1.rd64 (BitVec.ofInt 64 ((a + 8 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]; exact h1.c)
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := 4) rfl (by omega) (by decide)
  obtain ⟨m4, s4, h4⟩ := ls_bin E h3 (hc.get (j := 3) rfl) (d := 3) (e := 2) (g' := 4) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := n + 1) (by simp [upd])
  obtain ⟨m5, s5, h5⟩ := ls_cas_serve E h4 (hc.get (j := 4) rfl) (d := 5) (e := 1) (x := 2) rfl rfl rfl
    (by omega) (by omega) (by omega)
    (by
      have key : BitVec.ofInt 64 ((a : Int) + 8) = BitVec.ofNat 64 (a + 8) := by
        rw [← BitVec.ofInt_natCast]; simp
      simpa [upd] using key)
  have h5' := h5.congr rfl (c' := n + 1) (by simp [upd]) rfl
  obtain ⟨m6, s6, h6⟩ := ls_const E h5' (hc.get (j := 5) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m7, s7, h7⟩ := ls_ld E h6 (hc.get (j := 6) rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := w) (by simp only [upd_self, BitVec.ofInt_natCast]; exact h6.w)
  exact ⟨m7, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7))))), h7, by simp [upd]⟩

/-- Nonzero waiters fall through to a private futex WAKE-all, with the signed
    32-bit maximum as the wake count. No waiter is removed by the syscall. -/
theorem gibT_waiters_entry (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f next n w)
    (hc : At code p (gibT L a s)) (waiters : w ≠ 0) :
    ∃ mw fw, Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 15)), fp⟩ mw ∧
      LS m0 mw fp s a fw next (n + 1) w ∧
      FutexArgs fw (BitVec.ofNat 64 (a + 8)) 129 2147483647 ∧
      StopAt ⟨pc + BitVec.ofNat 64 (16 * (p + 15)), fp⟩ mw
        (futexReq (BitVec.ofNat 64 (a + 8)) 129 2147483647) := by
  obtain ⟨m1, f1, steps1, state1, test⟩ := gibT_waiters_read E h hc
  have branch := ls_brz_ne E state1 (hc.get (j := 7) rfl) (e := 2) rfl (by omega)
    (by rw [test]; exact waiters)
  have prep : At code (p + 8) (futexC (a + 8) 129 (s + 5) (s + 10) (some 2147483647)) := by
    intro j hj
    have := hc (8 + j) (by change j < 8 at hj; rw [gibT_len]; omega)
    rw [show p + 8 + j = p + (8 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  have ht := E.top
  obtain ⟨mw, fw, steps2, state2, args, _⟩ := futex_prepare E state1 prep
    (by omega) (by decide) (by decide) (by intro k hk; cases hk; decide)
  exact ⟨mw, fw, steps1.trans (branch.trans steps2), state2, args,
    futex_entry E state2 (hc.get (j := 15) rfl) args⟩

/-- A returned WAKE reports an error or at most the requested number of woken
    threads. Other threads' effects are exactly the supplied resumed `LS`. -/
theorem gibT_waiters_return {spurious : W → W → Mem → Mem → Prop} [FutexOK spurious]
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f next n w)
    (hc : At code p (gibT L a s))
    (args : FutexArgs f (BitVec.ofNat 64 (a + 8)) 129 2147483647)
    {r x next' n' w' : W} {mr : Mem}
    (answer : Kern.ans (futexReq (BitVec.ofNat 64 (a + 8)) 129 2147483647) m (some (r, x)) mr)
    (resume : LS m0 mr fp s a f next' n' w') :
    (r.toInt < 0 ∨ r.toNat ≤ 2147483647) ∧
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 15)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 16)), fp⟩ m' ∧
      LS m0 m' fp s a (upd f 17 r) next' n' w' := by
  obtain ⟨m', steps, state⟩ := futex_return E h (hc.get (j := 15) rfl) args answer resume
  have result : r.toInt < 0 ∨ r.toNat ≤ 2147483647 := by
    by_cases error : r.toInt < 0
    · exact Or.inl error
    · exact Or.inr (FutexOK.wake_return spurious _ _ _ _ _ _ answer (by omega))
  exact ⟨result, m', steps, state⟩

end
end Gabbro.Stage0.Senke
