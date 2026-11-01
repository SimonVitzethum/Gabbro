/- Subject: Generic correctness of equality between a packed string and a long string. -/
import Stage0.Senke.Ausdruck.Aggregat.Frame.StringEqMixedCode
import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeOk

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

/-- The packed first byte as a word. -/
theorem pack_word (b : Zahl 0 255) :
    BitVec.ofInt 64 256 + BitVec.ofInt 64 b.n = BitVec.ofNat 64 (256 + b.n.toNat) := by
  have := b.lo_le
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  omega

theorem mixedEq_word {p q : Nat} (hp1 : p ≤ 1) (hq2 : 2 ≤ q) (hq31 : q < 2 ^ 31)
    (vP : Wert D (.str p)) (vL : Wert D (.str q)) :
    Runner.IR.bool ((Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 vL.1.length)) *
        (BitVec.ofInt 64 256 + BitVec.ofInt 64 (strGetW (n := q) vL (0 : Nat)).n)) ==
        BitVec.ofNat 64 (strN vP.1)) &&&
      Runner.IR.bool ((BitVec.ofNat 64 vL.1.length).ult (BitVec.ofInt 64 2)) =
      Runner.IR.bool (strEqW (n := p) (m := q) vP vL) := by
  have hP : vP.1.length ≤ 1 := by have := vP.2; omega
  have hL : vL.1.length ≤ q := vL.2
  rcases hbP : vP.1 with _ | ⟨b, restP⟩ <;> rcases hbL : vL.1 with _ | ⟨c, restL⟩
  · simp [strEqW, hbP, hbL, strN, Runner.IR.bool]
  · have hb0 : (strGetW (n := q) vL (0 : Nat)).n = c.n := by
      simp only [strGetW, Int.natCast_nonneg, ↓reduceIte, hbL]; rfl
    have hl : restL.length + 1 ≤ q := by have := hL; rw [hbL] at this; simpa using this
    have fl : (BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (c :: restL).length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofInt, BitVec.toNat_ofNat, decide_eq_true_eq, List.length_cons]
      omega
    have big : BitVec.ofNat 64 (256 + c.n.toNat) ≠ BitVec.ofNat 64 0 := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      have := c.lo_le; have := c.le_hi
      omega
    have one : ∀ a : Runner.W, 1 * a = a := by intro a; bv_omega
    have ne : (BitVec.ofNat 64 (256 + c.n.toNat) == 0#64) = false := by
      simpa using big
    simp only [strEqW, hbP, hbL, strN, hb0, fl, List.map_nil, List.map_cons, Runner.IR.bool, ite_true,
      one, pack_word, ne]
    simp
  · have rp : restP = [] := by
      have := hP; rw [hbP] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst rp
    have fl : (BitVec.ofInt 64 0).ult (BitVec.ofNat 64 ([] : List (Zahl 0 255)).length) = false := by decide
    have two : (BitVec.ofNat 64 ([] : List (Zahl 0 255)).length).ult (BitVec.ofInt 64 2) = true := by decide
    have big : BitVec.ofNat 64 (256 + b.n.toNat) ≠ BitVec.ofNat 64 0 := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      have := b.lo_le; have := b.le_hi
      omega
    have ne : (0#64 == BitVec.ofNat 64 (256 + b.n.toNat)) = false := by
      have : (0#64 == BitVec.ofNat 64 (256 + b.n.toNat)) = false := by
        rw [Bool.eq_false_iff]
        intro h
        exact big (by simpa using (beq_iff_eq.mp h).symm)
      exact this
    simp only [strEqW, hbP, hbL, strN, fl, two, List.map_nil, List.map_cons, Runner.IR.bool]
    simp [ne]
  · have rp : restP = [] := by
      have := hP; rw [hbP] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst rp
    have hb0 : (strGetW (n := q) vL (0 : Nat)).n = c.n := by
      simp only [strGetW, Int.natCast_nonneg, ↓reduceIte, hbL]; rfl
    have hl : restL.length + 1 ≤ q := by have := hL; rw [hbL] at this; simpa using this
    have fl : (BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (c :: restL).length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofInt, BitVec.toNat_ofNat, decide_eq_true_eq, List.length_cons]
      omega
    have one : ∀ a : Runner.W, 1 * a = a := by intro a; bv_omega
    rcases restL with _ | ⟨c2, rest2⟩
    · have two : (BitVec.ofNat 64 [c].length).ult (BitVec.ofInt 64 2) = true := by
        simp only [List.length_singleton]; decide
      have hc := c.lo_le; have hc' := c.le_hi
      have hb := b.lo_le; have hb' := b.le_hi
      by_cases e : b.n = c.n
      · have ee : BitVec.ofNat 64 (256 + c.n.toNat) = BitVec.ofNat 64 (256 + b.n.toNat) := by
          rw [e]
        simp only [strEqW, hbP, hbL, strN, hb0, fl, two, List.map_nil, List.map_cons, Runner.IR.bool,
          ite_true, one, pack_word, ee, e]
        simp
      · have ne : (BitVec.ofNat 64 (256 + c.n.toNat) == BitVec.ofNat 64 (256 + b.n.toNat)) = false := by
          rw [Bool.eq_false_iff]
          intro h
          have := congrArg BitVec.toNat (beq_iff_eq.mp h)
          simp only [BitVec.toNat_ofNat] at this
          omega
        simp only [strEqW, hbP, hbL, strN, hb0, fl, two, List.map_nil, List.map_cons, Runner.IR.bool,
          ite_true, one, pack_word, ne]
        simp [e]
    · simp only [List.length_cons] at hl
      have two : (BitVec.ofNat 64 (c :: c2 :: rest2).length).ult (BitVec.ofInt 64 2) = false := by
        simp only [BitVec.ult, BitVec.toNat_ofInt, BitVec.toNat_ofNat, decide_eq_false_iff_not, List.length_cons]
        omega
      simp only [strEqW, hbP, hbL, strN, two, List.map_nil, List.map_cons, Runner.IR.bool]
      simp

/-- The nine comparison instructions leave the equality Boolean in `d`; they read the packed word, the length
    word and the first byte word, and write only scratch words above `t` and the word `d`. -/
theorem strEqMixedC_ok {p q p0 l0 t : Nat} (hp1 : p ≤ 1) (hq2 : 2 ≤ q) (hq31 : q < 2 ^ 31)
    (vP : Wert D (.str p)) (vL : Wert D (.str q))
    (hp : Pre L m pc fp K d (strEqMixedC p0 l0 d t) ρ W reserved) (hdt : d ≤ t)
    (h0 : p0 < t) (h1 : l0 + 1 < t) (hK : t + 4 ≤ K)
    (readP : m.rd64 (slot fp (BitVec.ofNat 64 p0)) = some (BitVec.ofNat 64 (strN vP.1)))
    (readLen : m.rd64 (slot fp (BitVec.ofNat 64 l0)) = some (BitVec.ofNat 64 vL.1.length))
    (readByte : m.rd64 (slot fp (BitVec.ofNat 64 (l0 + 1))) =
      some (BitVec.ofInt 64 (strGetW (n := q) vL (0 : Nat)).n)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 9), fp⟩ m' ∧ Agree fp d K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some (Runner.IR.bool (strEqW (n := p) (m := q) vP vL)) := by
  have small := hp.small
  have room := hp.frame.room
  have hpt : Pre L m pc fp K t
      ([ci 1 t 0 0] ++ ([ci 27 ((t + 1 : Nat) : Int) t l0] ++ ([ci 1 ((t + 2 : Nat) : Int) 256 0] ++
      ([ci 3 ((t + 2 : Nat) : Int) ((t + 2 : Nat) : Int) ((l0 + 1 : Nat) : Int)] ++
      ([ci 5 ((t + 2 : Nat) : Int) ((t + 1 : Nat) : Int) ((t + 2 : Nat) : Int)] ++
      ([ci 14 ((t + 2 : Nat) : Int) ((t + 2 : Nat) : Int) p0] ++
      ([ci 1 ((t + 3 : Nat) : Int) 2 0] ++ ([ci 27 ((t + 3 : Nat) : Int) l0 ((t + 3 : Nat) : Int)] ++
      [ci 8 d ((t + 2 : Nat) : Int) ((t + 3 : Nat) : Int)])))))))) ρ W reserved :=
    { (show Pre L m pc fp K d _ ρ W reserved from hp) with ctx := by have := hp.ctx; omega }
  obtain ⟨m1, s1, a1, w1, r1, e1⟩ := const_ok (k := 0) hpt.left (by decide) (by omega)
  subst e1
  have p1 := hpt.next a1 (by omega : t ≤ t + 1) (by omega)
  have len1 : m1.rd64 (slot fp (BitVec.ofNat 64 l0)) = some (BitVec.ofNat 64 vL.1.length) := by
    rw [agree_rd_low a1 room (by omega) (by omega)]; exact readLen
  obtain ⟨m2, s2, a2, w2, r2, e2⟩ := eng_bin_ok (d := t + 1) (a := t) (b := l0) (o := 27) p1.left
    (by omega) (by omega) (by omega) r1 len1
    (g := fun a b => some (Runner.IR.bool (a.ult b))) rfl (by decide) rfl
  subst e2
  have p2 := p1.next a2 (by omega : t + 1 ≤ t + 2) (by omega)
  obtain ⟨m3, s3, a3, w3, r3, e3⟩ := const_ok (k := 256) p2.left (by decide) (by omega)
  subst e3
  have p3 := p2.next a3 (Nat.le_refl _) (by omega)
  have byte3 : m3.rd64 (slot fp (BitVec.ofNat 64 (l0 + 1))) =
      some (BitVec.ofInt 64 (strGetW (n := q) vL (0 : Nat)).n) := by
    rw [agree_rd_low a3 room (by omega) (by omega), agree_rd_low a2 room (by omega) (by omega),
      agree_rd_low a1 room (by omega) (by omega)]
    exact readByte
  obtain ⟨m4, s4, a4, w4, r4, e4⟩ := eng_bin_ok (d := t + 2) (a := t + 2) (b := l0 + 1) (o := 3) p3.left
    (by omega) (by omega) (by omega) r3 byte3
    (g := fun a b => some (a + b)) rfl (by decide) rfl
  subst e4
  have p4 := p3.next a4 (Nat.le_refl _) (by omega)
  have flag4 : m4.rd64 (slot fp (BitVec.ofNat 64 (t + 1))) =
      some (Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 vL.1.length))) := by
    rw [agree_rd_low a4 room (by omega) (by omega), agree_rd_low a3 room (by omega) (by omega)]; exact r2
  obtain ⟨m5, s5, a5, w5, r5, e5⟩ := eng_bin_ok (d := t + 2) (a := t + 1) (b := t + 2) (o := 5) p4.left
    (by omega) (by omega) (by omega) flag4 r4
    (g := fun a b => some (a * b)) rfl (by decide) rfl
  subst e5
  have p5 := p4.next a5 (Nat.le_refl _) (by omega)
  have packed5 : m5.rd64 (slot fp (BitVec.ofNat 64 p0)) = some (BitVec.ofNat 64 (strN vP.1)) := by
    rw [agree_rd_low a5 room (by omega) (by omega), agree_rd_low a4 room (by omega) (by omega),
      agree_rd_low a3 room (by omega) (by omega), agree_rd_low a2 room (by omega) (by omega),
      agree_rd_low a1 room (by omega) (by omega)]
    exact readP
  obtain ⟨m6, s6, a6, w6, r6, e6⟩ := eng_bin_ok (d := t + 2) (a := t + 2) (b := p0) (o := 14) p5.left
    (by omega) (by omega) (by omega) r5 packed5
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl (by decide) rfl
  subst e6
  have p6 := p5.next a6 (by omega : t + 2 ≤ t + 3) (by omega)
  obtain ⟨m7, s7, a7, w7, r7, e7⟩ := const_ok (k := 2) p6.left (by decide) (by omega)
  subst e7
  have p7 := p6.next a7 (Nat.le_refl _) (by omega)
  have len7 : m7.rd64 (slot fp (BitVec.ofNat 64 l0)) = some (BitVec.ofNat 64 vL.1.length) := by
    rw [agree_rd_low a7 room (by omega) (by omega), agree_rd_low a6 room (by omega) (by omega),
      agree_rd_low a5 room (by omega) (by omega), agree_rd_low a4 room (by omega) (by omega),
      agree_rd_low a3 room (by omega) (by omega), agree_rd_low a2 room (by omega) (by omega),
      agree_rd_low a1 room (by omega) (by omega)]
    exact readLen
  obtain ⟨m8, s8, a8, w8, r8, e8⟩ := eng_bin_ok (d := t + 3) (a := l0) (b := t + 3) (o := 27) p7.left
    (by omega) (by omega) (by omega) len7 r7
    (g := fun a b => some (Runner.IR.bool (a.ult b))) rfl (by decide) rfl
  subst e8
  have p8 := p7.next a8 (Nat.le_refl _) (by omega)
  have eq8 : m8.rd64 (slot fp (BitVec.ofNat 64 (t + 2))) =
      some (Runner.IR.bool ((Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 vL.1.length)) *
        (BitVec.ofInt 64 256 + BitVec.ofInt 64 (strGetW (n := q) vL (0 : Nat)).n)) ==
        BitVec.ofNat 64 (strN vP.1))) := by
    rw [agree_rd_low a8 room (by omega) (by omega), agree_rd_low a7 room (by omega) (by omega)]; exact r6
  have p8' : Pre L m8 _ fp K d [ci 8 d ((t + 2 : Nat) : Int) ((t + 3 : Nat) : Int)] ρ W reserved :=
    { p8 with ctx := by have := hp.ctx; omega }
  obtain ⟨m9, s9, a9, w9, r9, e9⟩ := eng_bin_ok (d := d) (a := t + 2) (b := t + 3) (o := 8) p8'
    (by omega) (by omega) (by omega) eq8 r8 (g := fun a b => some (a &&& b)) rfl (by decide) rfl
  subst e9
  refine ⟨m9, ?_, ?_, ?_⟩
  · have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m9 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m9 :=
      fun p q h s => h ▸ s
    refine key _ _ ?_ (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans s9))))))))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_cons, List.length_nil]
    omega
  · exact (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans
      ((a4.mono (by omega)).trans ((a5.mono (by omega)).trans ((a6.mono (by omega)).trans
      ((a7.mono (by omega)).trans ((a8.mono (by omega)).trans a9)))))))
  · rw [r9, mixedEq_word hp1 hq2 hq31 vP vL]

theorem strEqW_comm {n m : Nat} (a : Wert D (.str n)) (b : Wert D (.str m)) :
    strEqW (n := n) (m := m) a b = strEqW (n := m) (m := n) b a := by
  unfold strEqW
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact ⟨Eq.symm, Eq.symm⟩

theorem bool_enc (v : Bool) : Enc L .bool v (Runner.IR.bool v) := by
  simp only [Enc, wahr?]
  exact bool_word v

/-- Equality of a packed string and a long string, in either operand order. -/
theorem strEqMixed_ok {n q : Nat} (vs : Wert D (.str n)) (vt : Wert D (.str q)) (s t : Option (List II × Nat))
    (ihs : ∀ ca ta, s = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) vs)
    (iht : ∀ ca ta, t = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords (.str n)) ca ρ W reserved →
        ValueOk L m pc fp K (d + valueWords (.str n)) ca (.str q) vt)
    (h : strEqMixedL n q d s t = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (strEqW (n := n) (m := q) vs vt) := by
  have small := hp.small
  simp only [strEqMixedL] at h
  split at h
  · next g =>
    obtain ⟨hn1, hq2, hq31⟩ := g
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs, ⟨ct, tt⟩, ht, rfl, rfl⟩ := h
    have wn : valueWords (.str n) = 1 := by simp only [valueWords, if_pos hn1]
    have hp' : Pre L m pc fp K d (cs ++ (ct ++ strEqMixedC d (d + 1) d (d + 1 + (q + 1)))) ρ W reserved := by
      simpa only [List.append_assoc] using hp
    obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp'.left
    have n1 := hp'.next ch1 (by omega : d ≤ d + valueWords (.str n)) (by omega)
    obtain ⟨m2, run2, ch2, vt2⟩ := iht ct tt ht (by omega) m1 _ n1.left
    have vs2 := vs1.agree ch2 (hp.frame.agree ch1) (by omega) (by omega)
    have n2 := n1.next ch2 (Nat.le_refl _) (by omega)
    have n2' : Pre L m2 _ fp K d (strEqMixedC d (d + 1) d (d + 1 + (q + 1))) ρ W reserved :=
      { n2 with ctx := by have := hp.ctx; omega }
    obtain ⟨wP, rdP, encP⟩ := ValueAt.word (.str n) vs (show WordCompatible (.str n) from hn1) vs2
    have readP : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 (strN vs.1)) := by
      rw [rdP]; exact congrArg some encP.2
    have readLen := span_len_read (b := d + valueWords (.str n)) hq2 vt vt2
    have readByte := span_byte_read (b := d + valueWords (.str n)) hq2 vt vt2
    rw [wn] at readLen readByte
    obtain ⟨m3, run3, ch3, r3⟩ := strEqMixedC_ok (p0 := d) (l0 := d + 1) (t := d + 1 + (q + 1)) hn1 hq2 hq31
      vs vt n2' (by omega) (by omega) (by omega) (by omega) readP readLen readByte
    refine ⟨m3, ?_, ?_, ValueAt.of_enc (by decide) r3 (bool_enc _)⟩
    · have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m3 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m3 :=
        fun p q h s => h ▸ s
      refine key _ _ ?_ (run1.trans (run2.trans run3))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append, strEqMixedC_length]
      omega
    · exact ch1.trans ((ch2.mono (by omega)).trans ch3)
  · split at h
    · next g =>
      obtain ⟨hn2, hq1, hn31⟩ := g
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨cs, ts⟩, hs, ⟨ct, tt⟩, ht, rfl, rfl⟩ := h
      have wn : valueWords (.str n) = n + 1 := by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]
      have hp' : Pre L m pc fp K d (cs ++ (ct ++ strEqMixedC (d + (n + 1)) d d (d + (n + 1) + 1))) ρ W reserved := by
        simpa only [List.append_assoc] using hp
      obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp'.left
      have n1 := hp'.next ch1 (by omega : d ≤ d + valueWords (.str n)) (by omega)
      obtain ⟨m2, run2, ch2, vt2⟩ := iht ct tt ht (by omega) m1 _ n1.left
      have vs2 := vs1.agree ch2 (hp.frame.agree ch1) (by omega) (by omega)
      have n2 := n1.next ch2 (Nat.le_refl _) (by omega)
      have n2' : Pre L m2 _ fp K d (strEqMixedC (d + (n + 1)) d d (d + (n + 1) + 1)) ρ W reserved :=
        { n2 with ctx := by have := hp.ctx; omega }
      obtain ⟨wP, rdP, encP⟩ := ValueAt.word (.str q) vt (show WordCompatible (.str q) from hq1) vt2
      have readP : m2.rd64 (slot fp (BitVec.ofNat 64 (d + (n + 1)))) =
          some (BitVec.ofNat 64 (strN vt.1)) := by
        rw [wn] at rdP
        rw [rdP]; exact congrArg some encP.2
      have readLen := span_len_read (b := d) hn2 vs vs2
      have readByte := span_byte_read (b := d) hn2 vs vs2
      obtain ⟨m3, run3, ch3, r3⟩ := strEqMixedC_ok (p0 := d + (n + 1)) (l0 := d) (t := d + (n + 1) + 1) hq1 hn2 hn31
        vt vs n2' (by omega) (by omega) (by omega) (by omega) readP readLen readByte
      rw [strEqW_comm vs vt]
      refine ⟨m3, ?_, ?_, ValueAt.of_enc (by decide) r3 (bool_enc _)⟩
      · have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m3 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m3 :=
          fun p q h s => h ▸ s
        refine key _ _ ?_ (run1.trans (run2.trans run3))
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append, strEqMixedC_length]
        omega
      · exact ch1.trans ((ch2.mono (by omega)).trans ch3)
    · cases h

end Gabbro.Stage0.Senke
