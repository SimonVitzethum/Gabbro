/- The freestanding contention edge executes two instructions and preserves all
   memory, including the ticket in slot two. No kernel premise is needed. -/
module
public import Stage0.Senke.Sperre.Warten.Retry
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}

/-- Failed serving comparison: branch to the binding, then retry the serving
    read. Both steps keep the complete state, not only the abstract lock. -/
theorem nimmT_spin_retry {L : Lay D} {m0 m : Mem} {pc fp : W}
    {s a p : Nat} {code : List II} {f : Nat → W} {n u w : W}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n u w)
    (hc : At code p (nimmT L a s)) (binding : L.lockWait = .spin)
    (compared : f 6 = bool (f 5 == f 2)) (waiting : f 2 ≠ f 5) :
    Star ⟨pc + BitVec.ofNat 64 (16 * (p + 10)), fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m := by
  have branch := ls_brz_zero E h (hc.get (j := 10) rfl) (e := 6) (k := 2)
    rfl rfl (by omega) (by omega)
    (by rw [compared]; exact bool_ne (Ne.symm waiting))
  have entry : code[p + 12]? = some (ci 18 (-80) 0 0) := by
    exact hc.get (j := 12) (x := ci 18 (-80) 0 0) (by simp [nimmT, binding, waitEntry])
  have retry := ls_jmp_back E h.ag (i := p + 7) (k := 5) (Lb := -80)
    (by simpa only [show p + 7 + 5 = p + 12 by omega] using entry) (by decide) (by decide)
  have branch' := branch
  simp only [show p + 10 + 2 = p + 12 by omega] at branch'
  simp only [show p + 7 + 5 = p + 12 by omega] at retry
  exact branch'.trans retry

/-- One complete failed spin attempt: the serving read, comparison and retry.
    The ticket and all three shared words survive; only scratch slots change.
    Each attempt follows a fixed path of five IR instructions. -/
theorem nimmT_spin_round {L : Lay D} {m0 m : Mem} {pc fp : W}
    {s a p : Nat} {code : List II} {f : Nat → W} {n u w : W}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n u w)
    (hc : At code p (nimmT L a s)) (binding : L.lockWait = .spin)
    (waiting : f 2 ≠ u) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' n u w ∧ f' 2 = f 2 ∧ f' 5 = u := by
  have top := E.top
  obtain ⟨m1, step1, state1⟩ := ls_const E h (hc.get (j := 7) rfl) (d := 1)
    rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, step2, state2⟩ := ls_ld E state1 (hc.get (j := 8) rfl)
    (d := 5) (e := 1) rfl rfl (by omega) (by omega) (v := u) (by
      show m1.rd64 (BitVec.ofInt 64 ((a + 8 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]
      exact state1.c)
  obtain ⟨m3, step3, state3⟩ := ls_bin E state2 (hc.get (j := 9) rfl)
    (d := 6) (e := 5) (g' := 2) rfl (by decide) rfl rfl rfl
    (by omega) (by omega) (by omega) (r := bool (u == f 2)) (by simp [upd])
  have retry := nimmT_spin_retry E state3 hc binding (by simp [upd]) (by simpa [upd] using waiting)
  refine ⟨m3, _, step1.trans (step2.trans (step3.trans retry)), state3, ?_, ?_⟩
  · simp [upd]
  · simp [upd]

end Gabbro.Stage0.Senke
