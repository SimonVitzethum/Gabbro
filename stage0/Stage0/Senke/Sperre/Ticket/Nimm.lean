/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Nimm.lean
  Subject:   The uncontended take of the ticket lock (`Ticket/Code.lean`): from next = serving the code at `p` runs
             straight to its end, leaving the ticket taken (next + 1) with serving as it was. No thread number is
             needed; the `AgreeK` inside `LS` carries the untouched rest of the memory.
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
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {n w : W}

/-- The uncontended take: next = serving `n`; the ticket taken, serving still `n`. -/
theorem nimmT_frei {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n n w) {p : Nat}
    (hc : At code p (nimmT L a s)) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 35)), fp⟩ m' ∧
      LS m0 m' fp s a f' (n + 1) n w := by
  have htop := E.top
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_ld E h1 (hc.get (j := 1) rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := n) (by simp only [upd_self, BitVec.ofInt_natCast]; exact h1.o)
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := 4) rfl (by omega) (by decide)
  obtain ⟨m4, s4, h4⟩ := ls_bin E h3 (hc.get (j := 3) rfl) (d := 3) (e := 2) (g' := 4) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := n + 1) (by simp [upd])
  obtain ⟨m5, s5, h5⟩ := ls_cas E h4 (hc.get (j := 4) rfl) (d := 5) (e := 1) (x := 2) rfl rfl rfl
    (by omega) (by omega) (by omega) (by simp [upd, BitVec.ofInt_natCast])
  have h5' := h5.congr (o' := n + 1) (by simp [upd]) rfl rfl
  obtain ⟨m6, s6, h6⟩ := ls_bin E h5' (hc.get (j := 5) rfl) (d := 5) (e := 5) (g' := 2) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := 1) (by
      show some (bool ((n : W) == n)) = some (1 : W)
      rw [bool_eq_self])
  have s7 := ls_brz_ne E h6 (hc.get (j := 6) rfl) (e := 5) rfl (by omega) (by simp [upd])
  obtain ⟨m8, s8, h8⟩ := ls_const E h6 (hc.get (j := 7) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m9, s9, h9⟩ := ls_ld E h8 (hc.get (j := 8) rfl) (d := 5) (e := 1) rfl rfl (by omega) (by omega)
    (v := n) (by
      show m8.rd64 (BitVec.ofInt 64 ((a + 8 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]; exact h8.c)
  obtain ⟨m10, s10, h10⟩ := ls_bin E h9 (hc.get (j := 9) rfl) (d := 6) (e := 5) (g' := 2) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := 1) (by
      show some (bool ((n : W) == n)) = some (1 : W)
      rw [bool_eq_self])
  have s11 := ls_brz_ne E h10 (hc.get (j := 10) rfl) (e := 6) rfl (by omega) (by simp [upd])
  have s12 := ls_jmp E h10.ag (hc.get (j := 11) rfl) (k := 24) rfl (by omega)
  exact ⟨m10, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans (s9.trans
    (s10.trans (s11.trans s12)))))))))), h10⟩

end

end Gabbro.Stage0.Senke
