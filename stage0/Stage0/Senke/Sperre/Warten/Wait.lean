/- Sequential entry to WAIT and conditional return to the serving check. -/
module
public import Stage0.Senke.Sperre.Warten.Futex
public import Stage0.Senke.Sperre.Warten.Invariant
public import Stage0.Senke.Sperre.Warten.Retry
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}
set_option maxRecDepth 100000
section
variable {m0 m : Mem} {pc fp : W} {s a p : Nat} {code : List II}
  {f : Nat → W} {n u w : W} {L : Lay D} {T : Nat}

/-- The branch uses the comparison already performed at index nine. The futex
    compare operand is the serving value READ into slot five, including when
    it differs from a subsequently observed serving word. My ticket survives. -/
theorem nimmT_wait_entry (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n u w)
    (hc : At code p (nimmT L a s)) {t : W} (ticket : f 2 = t)
    (compared : f 6 = bool (f 5 == f 2)) (waiting : t ≠ f 5)
    (hinv : TicketInvW T n u w) (room : w.toNat + 1 ≤ (n - u).toNat) :
    ∃ mw fw, Star ⟨pc + BitVec.ofNat 64 (16 * (p + 10)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 26)), fp⟩ mw ∧
      LS m0 mw fp s a fw n u (w + 1) ∧ TicketInvW T n u (w + 1) ∧
      FutexArgs fw (BitVec.ofNat 64 (a + 8)) 128 (f 5) ∧ fw 2 = t ∧ fw 5 = f 5 ∧
      StopAt ⟨pc + BitVec.ofNat 64 (16 * (p + 26)), fp⟩ mw
        (futexReq (BitVec.ofNat 64 (a + 8)) 128 (f 5)) := by
  have branch := ls_brz_zero E h (hc.get (j := 10) rfl) (e := 6) (k := 2)
    rfl rfl (by omega) (by omega)
    (by rw [compared, ticket]; exact bool_ne (Ne.symm waiting))
  have inc : At code (p + 12) (addC (a + 16) (s + 7) 1) := by
    intro j hj
    have := hc (12 + j) (by change j < 7 at hj; rw [nimmT_len]; omega)
    rw [show p + 12 + j = p + (12 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  obtain ⟨m1, f1, steps1, state1, keep1⟩ := add_waiters E h inc (by decide) (by decide)
  have prep : At code (p + 19) (futexC (a + 8) 128 (s + 5) (s + 10) none) := by
    intro j hj
    have := hc (19 + j) (by change j < 8 at hj; rw [nimmT_len]; omega)
    rw [show p + 19 + j = p + (19 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  have ht := E.top
  obtain ⟨mw, fw, steps2, state2, args, keep2⟩ :=
    futex_prepare E state1 prep (by omega) (by decide) (by decide) (by simp)
  have args' : FutexArgs fw (BitVec.ofNat 64 (a + 8)) 128 (f 5) := by
    simpa [keep1 5 (by decide)] using args
  have entry := futex_entry E state2 (hc.get (j := 26) rfl) args'
  refine ⟨mw, fw, branch.trans (steps1.trans steps2), state2, hinv.increment room, args', ?_, ?_, entry⟩
  · exact (keep2 2 (by decide)).trans ((keep1 2 (by decide)).trans ticket)
  · exact (keep2 5 (by decide)).trans (keep1 5 (by decide))

/-- A kernel response is required. Its WAIT classification and the environment's
    frame/word invariant are separate premises. After unregistering, index 34
    returns to index seven without changing my ticket in slot two. -/
theorem nimmT_wait_retry {spurious : W → W → Mem → Mem → Prop} [FutexOK spurious]
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n u w)
    (hc : At code p (nimmT L a s)) {seen r x n' u' w' : W} {mr : Mem}
    (args : FutexArgs f (BitVec.ofNat 64 (a + 8)) 128 seen)
    (answer : Kern.ans (futexReq (BitVec.ofNat 64 (a + 8)) 128 seen) m (some (r, x)) mr)
    (resume : LS m0 mr fp s a f n' u' w') (invariant : TicketInvW T n' u' w')
    (registered : 0 < w'.toNat) :
    ((∃ observed, mr.rd32 (BitVec.ofNat 64 (a + 8)) = some observed ∧ observed ≠ seen.setWidth 32) ∨
      spurious (BitVec.ofNat 64 (a + 8)) seen m mr) ∧
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 26)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' n' u' (w' - 1) ∧ TicketInvW T n' u' (w' - 1) ∧
      f' 2 = f 2 ∧ f' 5 = f 5 := by
  refine ⟨FutexOK.wait_return _ _ _ _ _ _ answer, ?_⟩
  obtain ⟨m1, steps1, state1⟩ := futex_return E h (hc.get (j := 26) rfl) args answer resume
  have dec : At code (p + 27) (addC (a + 16) (s + 7) (-1)) := by
    intro j hj
    have := hc (27 + j) (by change j < 7 at hj; rw [nimmT_len]; omega)
    rw [show p + 27 + j = p + (27 + j) by omega, this]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
    | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  obtain ⟨m2, f2, steps2, state2, keep2⟩ := add_waiters E state1 dec (by decide) (by decide)
  have jump : Star ⟨pc + BitVec.ofNat 64 (16 * (p + 34)), fp⟩ m2
      ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m2 := by
    simpa only [Nat.add_assoc] using
      ls_jmp_back E state2.ag (i := p + 7) (k := 27)
        (by have h34 := hc.get (j := 34) rfl; simpa using h34) rfl (by decide)
  have eq : w' + BitVec.ofInt 64 (-1) = w' - 1 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  refine ⟨m2, f2, steps1.trans (steps2.trans jump), state2.congr rfl rfl eq,
    invariant.decrement registered, ?_, ?_⟩
  · simpa [upd] using keep2 2 (by decide)
  · simpa [upd] using keep2 5 (by decide)

end
end Gabbro.Stage0.Senke
