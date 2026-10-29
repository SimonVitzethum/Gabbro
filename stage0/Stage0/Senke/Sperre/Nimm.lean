/-
  File:      stage0/Stage0/Senke/Sperre/Nimm.lean
  Subject:   The thread's number (`meC`) and the two fast paths of taking a lock (`nimmC`): the owner word is 0 --
             `cas` makes it mine, the count 1; the owner is me -- the count + 1. Neither path reads the waiters.
-/
import Stage0.Senke.Sperre.Schritt

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The code `xs` lies in `code` from instruction `p` on. -/
def At (code : List II) (p : Nat) (xs : List II) : Prop := ∀ j, j < xs.length → code[p + j]? = xs[j]?

theorem At.get {code xs : List II} {p : Nat} (h : At code p xs) {j : Nat} {x : II} (hx : xs[j]? = some x) :
    code[p + j]? = some x := by
  obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hx
  rw [h j hj, hx]

theorem At.left {code xs ys : List II} {p : Nat} (h : At code p (xs ++ ys)) : At code p xs := fun j hj => by
  rw [h j (by simp; omega), List.getElem?_append_left hj]

theorem At.right {code xs ys : List II} {p : Nat} (h : At code p (xs ++ ys)) : At code (p + xs.length) ys :=
  fun j hj => by
    rw [Nat.add_assoc, h (xs.length + j) (by simp; omega), List.getElem?_append_right (by omega)]
    simp

theorem At.whole (code : List II) : At code 0 code := fun j _ => by rw [Nat.zero_add]

/-- The thread's number + 1, as `meC` computes it from the frame. -/
def meW (L : Lay D) (fp : W) : W := BitVec.ofNat 64 ((fp.toNat - L.sb) / L.st + 1)

/-- What `meC` needs: the frame above the first stack, the stacks' size not 0, everything small. -/
structure MeOK (L : Lay D) (fp : W) : Prop where
  sb : L.sb ≤ fp.toNat
  sb31 : L.sb < 2 ^ 31
  st : 0 < L.st
  st31 : L.st < 2 ^ 31
  fp62 : fp.toNat < 2 ^ 62

theorem meW_ne {L : Lay D} {fp : W} (h : MeOK L fp) : meW L fp ≠ 0 := by
  intro h0
  have hq : (fp.toNat - L.sb) / L.st ≤ fp.toNat - L.sb := Nat.div_le_self _ _
  have h2 := h.fp62
  have h3 : (meW L fp).toNat ≠ 0 := by
    simp only [meW, BitVec.toNat_ofNat]
    generalize (fp.toNat - L.sb) / L.st = q at hq ⊢
    omega
  exact h3 (by rw [h0]; rfl)

theorem bool_eq_self (x : W) : bool (x == x) = 1 := by simp [Runner.IR.bool]

theorem bool_ne {x y : W} (h : x ≠ y) : bool (x == y) = 0 := by simp [Runner.IR.bool, h]

theorem lit32_nat {n : Nat} (h : n < 2 ^ 31) : lit32 (n : Int) = true := by
  simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

/-- `meC`: slot `s` gets the thread's number + 1; the slots from `s + 2` on stay. -/
theorem ls_me {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {p : Nat}
    (hc : At code p (meC L s)) (hme : MeOK L fp) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' o c w ∧ f' 0 = meW L fp ∧ ∀ j, 2 ≤ j → f' j = f j := by
  have hsb := hme.sb31
  have hst := hme.st31
  obtain ⟨m1, s1, h1⟩ := ls_lea E h (hc.get (j := 0) rfl) (d := 0) (by omega) (by omega)
  obtain ⟨m2, s2, h2⟩ := ls_const E h1 (hc.get (j := 1) rfl) (d := 1) (by omega) (by omega) (lit32_nat hsb)
  obtain ⟨m3, s3, h3⟩ := ls_bin E h2 (hc.get (j := 2) rfl) (d := 0) (e := 0) (g' := 1) rfl (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (r := fp - BitVec.ofInt 64 L.sb)
    (by simp [upd])
  obtain ⟨m4, s4, h4⟩ := ls_const E h3 (hc.get (j := 3) rfl) (d := 1) (by omega) (by omega) (lit32_nat hst)
  have hsub : fp - BitVec.ofInt 64 (L.sb : Int) = BitVec.ofNat 64 (fp.toNat - L.sb) := by
    rw [BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    have := hme.sb
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hdiv := sdiv_nat (x := fp.toNat - L.sb) (y := L.st) (by have := hme.fp62; omega) hme.st (by omega)
  obtain ⟨m5, s5, h5⟩ := ls_bin E h4 (hc.get (j := 4) rfl) (d := 0) (e := 0) (g' := 1) rfl (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (r := BitVec.ofNat 64 ((fp.toNat - L.sb) / L.st))
    (by
      show sdiv (fp - BitVec.ofInt 64 (L.sb : Int)) (BitVec.ofInt 64 (L.st : Int)) = _
      rw [hsub, BitVec.ofInt_natCast, hdiv])
  obtain ⟨m6, s6, h6⟩ := ls_const E h5 (hc.get (j := 5) rfl) (d := 1) (by omega) (by omega) (by decide)
  obtain ⟨m7, s7, h7⟩ := ls_bin E h6 (hc.get (j := 6) rfl) (d := 0) (e := 0) (g' := 1) rfl (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (r := meW L fp)
    (by
      show some (BitVec.ofNat 64 ((fp.toNat - L.sb) / L.st) + BitVec.ofInt 64 1) = some (meW L fp)
      simp only [Option.some.injEq, meW]
      apply BitVec.eq_of_toNat_eq
      have hq : (fp.toNat - L.sb) / L.st ≤ fp.toNat - L.sb := Nat.div_le_self _ _
      have h62 := hme.fp62
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
      generalize (fp.toNat - L.sb) / L.st = q at hq ⊢
      omega)
  refine ⟨m7, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7))))), h7, by simp [upd],
    fun j hj => ?_⟩
  simp [upd, show j ≠ 0 by omega, show j ≠ 1 by omega]

/-- The owner word is 0: `cas` makes the lock mine, the count 1. -/
theorem nimm_frei {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f 0 c w) {p : Nat}
    (hc : At code p (nimmC L a s)) (hme : MeOK L fp) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 48)), fp⟩ m' ∧
      LS m0 m' fp s a f' (meW L fp) 1 w := by
  have htop := E.top
  have hm := hc.left.left.left.left.left.left.left.left
  obtain ⟨m7, f7, s7, h7, e7, -⟩ := ls_me E h (p := p) hm hme
  obtain ⟨m8, s8, h8⟩ := ls_const E h7 (hc.get (j := 7) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m9, s9, h9⟩ := ls_ld E h8 (hc.get (j := 8) rfl) (d := 1) (e := 1) rfl rfl (by omega) (by omega)
    (v := 0) (by simp only [upd_self, BitVec.ofInt_natCast]; exact h8.o)
  obtain ⟨m10, s10, h10⟩ := ls_bin E h9 (hc.get (j := 9) rfl) (d := 1) (e := 1) (g' := 0) rfl (by decide)
    rfl rfl (by omega) (by omega) (by omega) (by omega) (r := 0)
    (by
      show some (bool ((0 : W) == f7 0)) = some 0
      rw [e7, bool_ne (Ne.symm (meW_ne hme))])
  have s11 := ls_brz_zero E h10 (hc.get (j := 10) rfl) (e := 1) (k := 7) rfl (by omega) (by omega) (by omega)
    (by simp [upd])
  obtain ⟨m12, s12, h12⟩ := ls_const E h10 (hc.get (j := 17) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m13, s13, h13⟩ := ls_const E h12 (hc.get (j := 18) rfl) (d := 2) rfl (by omega) (by decide)
  obtain ⟨m14, s14, h14⟩ := ls_mov E h13 (hc.get (j := 19) rfl) (d := 3) (e := 0) rfl (by omega) (by omega)
    (by omega)
  obtain ⟨m15, s15, h15⟩ := ls_cas E h14 (hc.get (j := 20) rfl) (d := 4) (e := 1) (x := 2) rfl rfl rfl
    (by omega) (by omega) (by omega) (by simp [upd, BitVec.ofInt_natCast])
  have h15' := h15.congr (o' := meW L fp) (by simp [upd, e7]) rfl rfl
  have s16 := ls_brz_zero E h15' (hc.get (j := 21) rfl) (e := 4) (k := 24) rfl (by omega) (by omega) (by omega)
    (by simp [upd])
  obtain ⟨m17, s17, h17⟩ := ls_const E h15' (hc.get (j := 45) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m18, s18, h18⟩ := ls_const E h17 (hc.get (j := 46) rfl) (d := 2) rfl (by omega) (by decide)
  obtain ⟨m19, s19, h19⟩ := ls_st_count E h18 (hc.get (j := 47) rfl) (e := 1) (g' := 2) rfl rfl (by omega)
    (by omega) (show BitVec.ofInt 64 ((a + 8 : Nat) : Int) = _ from BitVec.ofInt_natCast (w := 64) (a + 8))
  exact ⟨m19, _, s7.trans (s8.trans (s9.trans (s10.trans (s11.trans (s12.trans (s13.trans (s14.trans
    (s15.trans (s16.trans (s17.trans (s18.trans s19))))))))))), h19.congr rfl (by simp [upd]) rfl⟩


/-- The owner is me: the count + 1. -/
theorem nimm_mein {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f (meW L fp) c w) {p : Nat}
    (hc : At code p (nimmC L a s)) (hme : MeOK L fp) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 48)), fp⟩ m' ∧
      LS m0 m' fp s a f' (meW L fp) (c + 1) w := by
  have htop := E.top
  obtain ⟨m7, f7, s7, h7, e7, -⟩ := ls_me E h (p := p) hc.left.left.left.left.left.left.left.left hme
  obtain ⟨m8, s8, h8⟩ := ls_const E h7 (hc.get (j := 7) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m9, s9, h9⟩ := ls_ld E h8 (hc.get (j := 8) rfl) (d := 1) (e := 1) rfl rfl (by omega) (by omega)
    (v := meW L fp) (by simp only [upd_self, BitVec.ofInt_natCast]; exact h8.o)
  obtain ⟨m10, s10, h10⟩ := ls_bin E h9 (hc.get (j := 9) rfl) (d := 1) (e := 1) (g' := 0) rfl (by decide)
    rfl rfl (by omega) (by omega) (by omega) (by omega) (r := 1)
    (by
      show some (bool (meW L fp == f7 0)) = some 1
      rw [e7, bool_eq_self])
  have s11 := ls_brz_ne E h10 (hc.get (j := 10) rfl) (e := 1) rfl (by omega) (by simp [upd])
  obtain ⟨m12, s12, h12⟩ := ls_const E h10 (hc.get (j := 11) rfl) (d := 1) rfl (by omega) (lit32_nat (by omega))
  obtain ⟨m13, s13, h13⟩ := ls_ld E h12 (hc.get (j := 12) rfl) (d := 2) (e := 1) rfl rfl (by omega) (by omega)
    (v := c) (by
      show m12.rd64 (BitVec.ofInt 64 ((a + 8 : Nat) : Int)) = _
      rw [BitVec.ofInt_natCast]; exact h12.c)
  obtain ⟨m14, s14, h14⟩ := ls_const E h13 (hc.get (j := 13) rfl) (d := 3) rfl (by omega) (by decide)
  obtain ⟨m15, s15, h15⟩ := ls_bin E h14 (hc.get (j := 14) rfl) (d := 2) (e := 2) (g' := 3) rfl (by decide)
    rfl rfl rfl (by omega) (by omega) (by omega) (r := c + 1) (by simp [upd])
  obtain ⟨m16, s16, h16⟩ := ls_st_count E h15 (hc.get (j := 15) rfl) (e := 1) (g' := 2) rfl rfl (by omega)
    (by omega) (show BitVec.ofInt 64 ((a + 8 : Nat) : Int) = _ from BitVec.ofInt_natCast (w := 64) (a + 8))
  have s17 := ls_jmp E h16.ag (hc.get (j := 16) rfl) (k := 32) rfl (by omega)
  exact ⟨m16, _, s7.trans (s8.trans (s9.trans (s10.trans (s11.trans (s12.trans (s13.trans (s14.trans
    (s15.trans (s16.trans s17))))))))), h16.congr rfl (by simp [upd]) rfl⟩

end

end Gabbro.Stage0.Senke
