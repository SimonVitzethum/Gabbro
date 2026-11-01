/- The failed-acquisition prefix of the actual lock emitter, before waiter
   bookkeeping or a syscall. No futex behavior is assumed by this theorem. -/
module
public import Stage0.Senke.Sperre.Nimm
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

variable [Kern] {D : Deklaration}

/-- A foreign nonzero owner sends `nimmC` to its wait branch. The failed CAS
    returns that owner without changing any lock word. This is a prefix result,
    not acquisition, futex progress or a concurrent source simulation. -/
theorem nimm_contended {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II}
    {f : Nat → W} {o c w : W} {L : Lay D} {p : Nat}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmC L a s)) (hme : MeOK L fp)
    (ho : o ≠ 0) (hother : o ≠ meW L fp) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 22)), fp⟩ m' ∧
      LS m0 m' fp s a f' o c w ∧ f' 0 = meW L fp ∧ f' 4 = o ∧
      (∀ j, 5 ≤ j → f' j = f j) := by
  have htop := E.top
  obtain ⟨m7, f7, s7, h7, e7, keep7⟩ :=
    ls_me E h hc.left.left.left.left.left.left.left.left hme
  obtain ⟨m8, s8, h8⟩ := ls_const E h7 (hc.get (j := 7) rfl)
    (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m9, s9, h9⟩ := ls_ld E h8 (hc.get (j := 8) rfl)
    (d := 1) (e := 1) rfl rfl (by omega) (by omega)
    (v := o) (by simp only [upd_self, BitVec.ofInt_natCast]; exact h8.o)
  obtain ⟨m10, s10, h10⟩ := ls_bin E h9 (hc.get (j := 9) rfl)
    (d := 1) (e := 1) (g' := 0) rfl (by decide)
    rfl rfl (by omega) (by omega) (by omega) (by omega) (r := 0)
    (by
      show some (bool (o == f7 0)) = some 0
      rw [e7, bool_ne hother])
  have s11 := ls_brz_zero E h10 (hc.get (j := 10) rfl)
    (e := 1) (k := 7) rfl (by omega) (by omega) (by omega) (by simp [upd])
  obtain ⟨m12, s12, h12⟩ := ls_const E h10 (hc.get (j := 17) rfl)
    (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m13, s13, h13⟩ := ls_const E h12 (hc.get (j := 18) rfl)
    (d := 2) rfl (by omega) (by decide)
  obtain ⟨m14, s14, h14⟩ := ls_mov E h13 (hc.get (j := 19) rfl)
    (d := 3) (e := 0) rfl (by omega) (by omega) (by omega)
  obtain ⟨m15, s15, h15⟩ := ls_cas E h14 (hc.get (j := 20) rfl)
    (d := 4) (e := 1) (x := 2) rfl rfl rfl (by omega) (by omega) (by omega)
    (by simp [upd, BitVec.ofInt_natCast])
  have h15' := h15.congr (o' := o) (by
    change (if o = 0 then _ else o) = o
    rw [ite_eq_right ho]) rfl rfl
  have s16 := ls_brz_ne E h15' (hc.get (j := 21) rfl)
    (e := 4) rfl (by omega) (by simpa [upd] using ho)
  refine ⟨m15, _, s7.trans (s8.trans (s9.trans (s10.trans (s11.trans
    (s12.trans (s13.trans (s14.trans (s15.trans s16)))))))), h15', ?_, ?_, ?_⟩
  · simpa [upd] using e7
  · simp [upd]
  · intro j hj
    simpa [upd, show j ≠ 1 by omega, show j ≠ 2 by omega,
      show j ≠ 3 by omega, show j ≠ 4 by omega] using keep7 j (by omega)

end Gabbro.Stage0.Senke
