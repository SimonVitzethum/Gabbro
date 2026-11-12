/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Gib.lean
  Subject:   The give of the ticket lock without waiters (`Ticket/Code.lean`): from next = serving + 1 and no waiters
             the code at `p` runs straight to its end, leaving serving one higher and the waiters at 0. The `cas`
             on the serving word is the LOCKED store the wake-up needs.
-/
module
public import Stage0.Senke.Sperre.Ticket.Schritt
public import Stage0.Senke.Sperre.Ticket.Code
public import Stage0.Senke.Sperre.Nimm
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {n : W}

/-- The give without waiters: serving `n` becomes `n + 1`, the waiters stay 0. -/
theorem gibT_ohne {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f (n + 1) n 0) {p : Nat}
    (hc : At code p (gibT L a s)) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 16)), fp⟩ m' ∧
      LS m0 m' fp s a f' (n + 1) (n + 1) 0 := by
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
    (v := 0) (by simp only [upd_self, BitVec.ofInt_natCast]; exact h6.w)
  have s8 := ls_brz_zero E h7 (hc.get (j := 7) rfl) (e := 2) (k := 9) rfl rfl (by omega) (by omega)
    (by simp [upd])
  exact ⟨m7, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8)))))), h7⟩

end

end Gabbro.Stage0.Senke
