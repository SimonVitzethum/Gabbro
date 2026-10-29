/-
  File:      stage0/Stage0/Senke/Sperre/Gib.lean
  Subject:   The two paths of giving a lock (`gibC`) when no thread waits: the count - 1 is not 0 -- done; it is 0 --
             `cas` gives the owner word back (me -> 0), the waiters read 0, no `futex_wake`.
-/
import Stage0.Senke.Sperre.Nimm

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

/-- The count - 1 is not 0: the lock stays mine. -/
theorem gib_mehr {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {p : Nat}
    (hc : At code p (gibC L a s)) (hc1 : c - 1 ≠ 0) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 29)), fp⟩ m' ∧
      LS m0 m' fp s a f' o (c - 1) w := by
  have htop := E.top
  have hs := E.small
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_ld E h1 (hc.get (j := 1) rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := c) (by
      show m1.rd64 (BitVec.ofInt 64 ((a + 8 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]; exact h1.c)
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := 3) rfl (by omega) (by decide)
  obtain ⟨m4, s4, h4⟩ := ls_bin E h3 (hc.get (j := 3) rfl) (d := 2) (e := 2) (g' := 3) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := c - 1) (by simp [upd])
  obtain ⟨m5, s5, h5⟩ := ls_st_count E h4 (hc.get (j := 4) rfl) (e := 1) (g' := 2) rfl rfl (by omega)
    (by omega) (show BitVec.ofInt 64 ((a + 8 : Nat) : Int) = _ from BitVec.ofInt_natCast (w := 64) (a + 8))
  have s6 := ls_brz_ne E h5 (hc.get (j := 5) rfl) (e := 2) rfl (by omega) (by simpa [upd] using hc1)
  have s7 := ls_jmp E h5.ag (hc.get (j := 6) rfl) (k := 23) rfl (by omega)
  exact ⟨m5, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7))))),
    h5.congr rfl (by simp [upd]) rfl⟩

/-- The count - 1 is 0 and no thread waits: the owner word goes back to 0. -/
theorem gib_letzt {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f (meW L fp) c 0) {p : Nat}
    (hc : At code p (gibC L a s)) (hme : MeOK L fp) (hc1 : c - 1 = 0) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 29)), fp⟩ m' ∧
      LS m0 m' fp s a f' 0 0 0 := by
  have htop := E.top
  have hs := E.small
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m2, s2, h2⟩ := ls_ld E h1 (hc.get (j := 1) rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := c) (by
      show m1.rd64 (BitVec.ofInt 64 ((a + 8 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]; exact h1.c)
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := 3) rfl (by omega) (by decide)
  obtain ⟨m4, s4, h4⟩ := ls_bin E h3 (hc.get (j := 3) rfl) (d := 2) (e := 2) (g' := 3) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := c - 1) (by simp [upd])
  obtain ⟨m5, s5, h5⟩ := ls_st_count E h4 (hc.get (j := 4) rfl) (e := 1) (g' := 2) rfl rfl (by omega)
    (by omega) (show BitVec.ofInt 64 ((a + 8 : Nat) : Int) = _ from BitVec.ofInt_natCast (w := 64) (a + 8))
  have s6 := ls_brz_zero E h5 (hc.get (j := 5) rfl) (e := 2) (k := 2) rfl rfl (by omega) (by omega)
    (by simpa [upd] using hc1)
  have hm : At code (p + 7) (meC L s) := fun j hj => by
    rw [meC_len] at hj
    have h7 := hc (7 + j) (by rw [gibC_len]; omega)
    rw [show p + 7 + j = p + (7 + j) by omega, h7]
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  obtain ⟨m7, f7, s7, h7, e7, -⟩ := ls_me E h5 (p := p + 7) hm hme
  have g := fun j (x : II) (hx : (gibC L a s)[j]? = some x) => hc.get hx
  obtain ⟨m8, s8, h8⟩ := ls_const E h7 (g 14 _ rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m9, s9, h9⟩ := ls_mov E h8 (g 15 _ rfl) (d := 3) (e := 0) rfl (by omega) (by omega) (by omega)
  obtain ⟨m10, s10, h10⟩ := ls_const E h9 (g 16 _ rfl) (d := 4) rfl (by omega) (by decide)
  obtain ⟨m11, s11, h11⟩ := ls_cas E h10 (g 17 _ rfl) (d := 5) (e := 1) (x := 3) rfl rfl rfl
    (by omega) (by omega) (by omega) (by simp [upd, BitVec.ofInt_natCast])
  have h11' := h11.congr (o' := 0) (by simp [upd, e7]) rfl rfl
  obtain ⟨m12, s12, h12⟩ := ls_const E h11' (g 18 _ rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m13, s13, h13⟩ := ls_ld E h12 (g 19 _ rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := 0) (by
      show m12.rd64 (BitVec.ofInt 64 ((a + 16 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]; exact h12.w)
  have s14 := ls_brz_zero E h13 (g 20 _ rfl) (e := 2) (k := 9) rfl rfl (by omega) (by omega) (by simp [upd])
  exact ⟨m13, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans (s9.trans
    (s10.trans (s11.trans (s12.trans (s13.trans s14)))))))))))), h13.congr rfl (by simpa using hc1) rfl⟩

end

end Gabbro.Stage0.Senke
