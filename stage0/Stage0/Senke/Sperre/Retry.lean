/- The acquisition retry at instruction 17, after contended WAIT. These facts
   cover finite sequential-thread executions; eventual release is a premise. -/
module
public import Stage0.Senke.Sperre.Waiting.Wait
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}

section
variable {m0 m : Mem} {pc fp : W} {s a p : Nat} {code : List II}
  {f : Nat → W} {o c w : W} {L : Lay D}

/-- The actual retry CAS either acquires a free lock, or returns to the WAIT
    branch with the foreign owner in slot four and all lock words unchanged.
    Instruction 17 reuses the id in slot zero rather than recomputing it. -/
theorem nimm_retry (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmC L a s)) (id : f 0 = meW L fp) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 17)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + if o = 0 then 48 else 22)), fp⟩ m' ∧
      (if o = 0 then LS m0 m' fp s a f' (meW L fp) 1 w
       else LS m0 m' fp s a f' o c w ∧ f' 4 = o) ∧ f' 0 = meW L fp := by
  have ht := E.top
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 17) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_const E h1 (hc.get (j := 18) rfl) (d := 2) rfl (by omega) (by decide)
  obtain ⟨m3, s3, h3⟩ := ls_mov E h2 (hc.get (j := 19) rfl) (d := 3) (e := 0) rfl (by omega) (by omega) (by omega)
  obtain ⟨m4, s4, h4⟩ := ls_cas E h3 (hc.get (j := 20) rfl) (d := 4) (e := 1) (x := 2)
    rfl rfl rfl (by omega) (by omega) (by omega) (by simp [upd, BitVec.ofInt_natCast])
  let scratch4 := upd (upd (upd (upd f 1 (BitVec.ofInt 64 (a : Int))) 2 0) 3 (f 0)) 4 o
  by_cases free : o = 0
  · subst o
    have state4 := h4.congr (o' := meW L fp) (by simp [upd, id]) rfl rfl
    have branch := ls_brz_zero E state4 (hc.get (j := 21) rfl) (e := 4) (k := 24)
      rfl (by omega) (by omega) (by omega) (by simp [upd])
    obtain ⟨m5, s5, h5⟩ := ls_const E state4 (hc.get (j := 45) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
    obtain ⟨m6, s6, h6⟩ := ls_const E h5 (hc.get (j := 46) rfl) (d := 2) rfl (by omega) (by decide)
    obtain ⟨m7, s7, h7⟩ := ls_st_count E h6 (hc.get (j := 47) rfl) (e := 1) (g' := 2)
      rfl rfl (by omega) (by omega)
      (show BitVec.ofInt 64 ((a + 8 : Nat) : Int) = _ from BitVec.ofInt_natCast _ _)
    refine ⟨m7, upd (upd scratch4 1 (BitVec.ofInt 64 ((a + 8 : Nat) : Int))) 2 1, ?_, ?_, ?_⟩
    · simpa only [ite_true] using s1.trans (s2.trans (s3.trans (s4.trans (branch.trans (s5.trans (s6.trans s7))))))
    · simp only [ite_true]
      exact h7.congr rfl (by simp [upd]) rfl
    · simpa [scratch4, upd] using id
  · have state4 := h4.congr (o' := o) (by
      change (if o = 0 then _ else o) = o
      rw [ite_eq_right free]) rfl rfl
    have branch := ls_brz_ne E state4 (hc.get (j := 21) rfl) (e := 4) rfl (by omega)
      (by simpa [upd] using free)
    refine ⟨m4, scratch4, ?_, ?_, ?_⟩
    · simpa only [free, ite_false] using s1.trans (s2.trans (s3.trans (s4.trans branch)))
    · simp only [free, ite_false]; exact ⟨state4, by simp [scratch4]⟩
    · simpa [scratch4, upd] using id

/-- Any finite sequence of actual retry/WAIT instructions that returns here
    after the environment released the lock can be finished by acquisition.
    `history` is an actual runner `Star`, not an assumed source simulation.
    There is deliberately no claim that a foreign holder eventually releases. -/
theorem nimm_retry_acquired {start : T} {initial : Mem}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f 0 0 w)
    (hc : At code p (nimmC L a s)) (id : f 0 = meW L fp)
    (history : Star start initial ⟨pc + BitVec.ofNat 64 (16 * (p + 17)), fp⟩ m)
    (bounded : w.toNat < 2 ^ 62) (hme : MeOK L fp) :
    ∃ m' f', Star start initial ⟨pc + BitVec.ofNat 64 (16 * (p + 48)), fp⟩ m' ∧
      LS m0 m' fp s a f' (meW L fp) 1 w ∧ LockInv (meW L fp) 1 w := by
  obtain ⟨m', f', steps, state, _⟩ := nimm_retry E h hc id
  exact ⟨m', f', history.trans steps, state,
    ⟨Or.inr ⟨meW_ne hme, by decide, by decide⟩, bounded⟩⟩

end
end Gabbro.Stage0.Senke
