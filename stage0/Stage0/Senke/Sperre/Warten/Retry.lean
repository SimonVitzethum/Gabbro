/- The ticket draw's CAS split, and the acquisition branch after waiting. -/
module
public import Stage0.Senke.Sperre.Warten.Schritt
public import Stage0.Senke.Sperre.Ticket.Nimm
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}
section
variable {m0 m : Mem} {pc fp : W} {s a p : Nat} {code : List II}
  {f : Nat → W} {o c w : W} {L : Lay D}

/-- Start at the draw CAS, with the address, expected ticket and successor that
    instructions 0--3 prepared. Success preserves my ticket in slot two.
    Slot five is the comparison result at index seven, not the CAS result. -/
theorem nimmT_cas_hit (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmT L a s)) (addr : f 1 = BitVec.ofNat 64 a)
    (expected : f 2 = o) (successor : f 3 = o + 1) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 4)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' (o + 1) c w ∧ f' 2 = o ∧ f' 5 = 1 ∧
      (∀ j, j ≠ 5 → f' j = f j) := by
  obtain ⟨m1, s1, h1⟩ := ls_cas E h (hc.get (j := 4) rfl) (d := 5) (e := 1) (x := 2)
    rfl rfl rfl (by omega) (by omega) (by omega) addr
  have h1' := h1.congr (o' := o + 1) (by simp [expected, successor]) rfl rfl
  obtain ⟨m2, s2, h2⟩ := ls_bin E h1' (hc.get (j := 5) rfl) (d := 5) (e := 5) (g' := 2)
    rfl (by decide) rfl rfl rfl (by omega) (by omega) (by omega) (r := 1)
    (by simp [upd, expected, Runner.IR.bool])
  have branch := ls_brz_ne E h2 (hc.get (j := 6) rfl) (e := 5) rfl (by omega) (by simp [upd])
  refine ⟨m2, _, s1.trans (s2.trans branch), h2, ?_, ?_, ?_⟩
  · simpa [upd] using expected
  · simp [upd]
  · intro j hj; simp [upd, hj]

/-- A missed CAS leaves the next/serving/waiter words as the CAS saw them.
    Index five overwrites its returned next word with zero; the branch at six
    returns to zero with slot five = 0 and the old expected ticket still in two. -/
theorem nimmT_cas_miss (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmT L a s)) (addr : f 1 = BitVec.ofNat 64 a)
    (miss : o ≠ f 2) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * (p + 4)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m' ∧
      LS m0 m' fp s a f' o c w ∧ f' 5 = 0 ∧ f' 2 = f 2 ∧
      (∀ j, j ≠ 5 → f' j = f j) := by
  obtain ⟨m1, s1, h1⟩ := ls_cas E h (hc.get (j := 4) rfl) (d := 5) (e := 1) (x := 2)
    rfl rfl rfl (by omega) (by omega) (by omega) addr
  have h1' := h1.congr (o' := o) (by simp [miss]) rfl rfl
  obtain ⟨m2, s2, h2⟩ := ls_bin E h1' (hc.get (j := 5) rfl) (d := 5) (e := 5) (g' := 2)
    rfl (by decide) rfl rfl rfl (by omega) (by omega) (by omega) (r := 0)
    (by simpa [upd] using congrArg some (bool_ne miss))
  have branch := ls_brz_back E h2 (hc.get (j := 6) rfl) (i := p) (k := 6)
    (e := 5) rfl rfl (by omega) (by decide) (by simp [upd])
  refine ⟨m2, _, s1.trans (s2.trans branch), h2, ?_, ?_, ?_⟩
  · simp [upd]
  · simp [upd]
  · intro j hj; simp [upd, hj]

/-- At index ten the comparison in slot six must actually be the comparison
    of the serving value read into five with my ticket in two. The read also
    agrees with the current serving word. Equality takes
    the fallthrough and the jump to the end, preserving all words and slots. -/
theorem nimmT_acquired (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmT L a s)) (compared : f 6 = bool (f 5 == f 2))
    (read : f 5 = c) (equal : f 5 = f 2) :
    Star ⟨pc + BitVec.ofNat 64 (16 * (p + 10)), fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (p + 35)), fp⟩ m ∧ LS m0 m fp s a f o c w ∧ f 2 = c := by
  have branch := ls_brz_ne E h (hc.get (j := 10) rfl) (e := 6) rfl (by omega)
    (by rw [compared, equal, bool_eq_self]; decide)
  have jump := ls_jmp E h.ag (hc.get (j := 11) rfl) (k := 24) rfl (by omega)
  exact ⟨branch.trans jump, h, equal.symm.trans read⟩

/-- The actual prefix from a fresh draw through the serving comparison. -/
theorem nimmT_check (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    (hc : At code p (nimmT L a s)) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 10)), fp⟩ m' ∧
      LS m0 m' fp s a f' (o + 1) c w ∧ f' 2 = o ∧ f' 5 = c ∧
      f' 6 = bool (f' 5 == f' 2) := by
  have ht := E.top
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_ld E h1 (hc.get (j := 1) rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := o) (by simp only [upd_self, BitVec.ofInt_natCast]; exact h1.o)
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := 4) rfl (by omega) (by decide)
  obtain ⟨m4, s4, h4⟩ := ls_bin E h3 (hc.get (j := 3) rfl) (d := 3) (e := 2) (g' := 4) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := o + 1) (by simp [upd])
  obtain ⟨m7, f7, s7, h7, ticket, _, _⟩ := nimmT_cas_hit E h4 hc
    (by simp [upd, BitVec.ofInt_natCast]) (by simp [upd]) (by simp [upd])
  obtain ⟨m8, s8, h8⟩ := ls_const E h7 (hc.get (j := 7) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m9, s9, h9⟩ := ls_ld E h8 (hc.get (j := 8) rfl) (d := 5) (e := 1) rfl rfl (by omega) (by omega)
    (v := c) (by
      show m8.rd64 (BitVec.ofInt 64 ((a + 8 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]; exact h8.c)
  obtain ⟨m10, s10, h10⟩ := ls_bin E h9 (hc.get (j := 9) rfl) (d := 6) (e := 5) (g' := 2)
    rfl (by decide) rfl rfl rfl (by omega) (by omega) (by omega) (r := bool (c == o))
    (by simp [upd, ticket])
  refine ⟨m10, _, s1.trans (s2.trans (s3.trans (s4.trans (s7.trans (s8.trans (s9.trans s10)))))), h10, ?_, ?_, ?_⟩
  · simpa [upd] using ticket
  · simp [upd]
  · simp [upd, ticket]

end
end Gabbro.Stage0.Senke
