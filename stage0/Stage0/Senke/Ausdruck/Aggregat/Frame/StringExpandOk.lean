/- Subject: Generic correctness of widening a packed string to a long string span. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringExpandCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringEqMixedOk
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Copy
public import Stage0.Senke.Welt.Spans.Cell
@[expose] public section

variable {currentOld : Bool}


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

/-- The widened encoding: the length word, the first byte word, then zero words. -/
theorem expand_words (L : Lay D) {n q : Nat} (hn1 : n ≤ 1) (hq2 : 2 ≤ q) (vs : Wert D (.str n)) :
    encodeWords L (.str q) (strWeitW (n := n) q vs) =
      [Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (strN vs.1))),
       (BitVec.ofNat 64 (strN vs.1) - BitVec.ofInt 64 256) *
         Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (strN vs.1)))] ++ List.replicate (q - 1) 0 := by
  have hlen : vs.1.length ≤ 1 := by have := vs.2; omega
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  subst hr
  rcases hbs : vs.1 with _ | ⟨b, rest⟩
  · simp only [encodeWords, strWeitW, hbs, if_neg (show ¬ r + 1 ≤ 1 by omega), List.take_nil, List.length_nil,
      List.map_nil, List.nil_append, strN, Nat.sub_zero, Nat.add_sub_cancel]
    have fl : (BitVec.ofInt 64 0).ult (BitVec.ofNat 64 0) = false := by decide
    simp only [fl, Runner.IR.bool, Bool.false_eq_true, ite_false, List.replicate_succ, List.cons_append,
      List.nil_append]
    simp
  · have hrest : rest = [] := by
      have := hlen; rw [hbs] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst hrest
    have hb := b.lo_le
    have fl : (BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (256 + b.n.toNat)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofInt, BitVec.toNat_ofNat, decide_eq_true_eq]
      have := b.le_hi
      omega
    have byte : BitVec.ofNat 64 (256 + b.n.toNat) - BitVec.ofInt 64 256 = BitVec.ofInt 64 b.n := by
      rw [← pack_word]; bv_omega
    have one : ∀ a : Runner.W, a * 1 = a := by intro a; bv_omega
    simp only [encodeWords, strWeitW, hbs, if_neg (show ¬ r + 1 ≤ 1 by omega), strN, fl, byte,
      Runner.IR.bool, ite_true, one, List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    simp [List.replicate_succ]

/-- Widening a packed string to a long span: head, two-word copy, zero tail. -/
theorem strExpand_ok {n q : Nat} (hn1 : n ≤ 1) (hq2 : 2 ≤ q)
    (vs : Wert D (.str n)) (s : Option (List II × Nat)) (z : List II × Nat)
    (hz : z = constWords (List.replicate (q - 1) 0) (d + 2))
    (ihs : ∀ ca ta, s = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) vs)
    (h : strExpandL n q d s z = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str q) (strWeitW (n := n) q vs) := by
  have small := hp.small
  have room := hp.frame.room
  subst hz
  simp only [strExpandL] at h
  split at h
  · next g =>
    obtain ⟨_, _, hq31⟩ := g
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs, rfl, rfl⟩ := h
    have wn : valueWords (.str n) = 1 := by simp only [valueWords, if_pos hn1]
    have hp' : Pre L m pc fp K d (cs ++ (strExpandHead d (d + q + 1) ++
        (copyWords 2 d (d + q + 1) ++ (constWords (List.replicate (q - 1) 0) (d + 2)).1))) ρ W reserved := hp
    obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp'.left
    have n1 := hp'.next ch1 (Nat.le_refl d) (by omega)
    obtain ⟨w, rdW, encW⟩ := ValueAt.word (.str n) vs (show WordCompatible (.str n) from hn1) vs1
    have hh : Pre L m1 _ fp K d
        ([ci 1 ((d + q + 1 + 2 : Nat) : Int) 0 0] ++
        ([ci 27 ((d + q + 1 : Nat) : Int) ((d + q + 1 + 2 : Nat) : Int) d] ++
        ([ci 1 ((d + q + 1 + 1 : Nat) : Int) 256 0] ++
        ([ci 4 ((d + q + 1 + 1 : Nat) : Int) d ((d + q + 1 + 1 : Nat) : Int)] ++
        ([ci 5 ((d + q + 1 + 1 : Nat) : Int) ((d + q + 1 + 1 : Nat) : Int) ((d + q + 1 : Nat) : Int)] ++
        (copyWords 2 d (d + q + 1) ++ (constWords (List.replicate (q - 1) 0) (d + 2)).1)))))) ρ W reserved := n1
    obtain ⟨_, hw⟩ := encW
    subst hw
    have frame1 := hp.frame.agree ch1
    have hhT : Pre L m1 _ fp K (d + q + 1 + 2) _ ρ W reserved :=
      { hh with ctx := by have := hp.ctx; omega }
    obtain ⟨m2, s2, a2, w2, r2, e2⟩ := const_ok (k := 0) hhT.left (by decide) (by omega)
    subst e2
    have p2 := hhT.next a2 (Nat.le_refl _) (by omega)
    have p2' : Pre L m2 _ fp K (d + q + 1) _ ρ W reserved := { p2 with ctx := by have := hp.ctx; omega }
    have w1 : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 (strN vs.1)) := by
      rw [agree_rd_low a2 room (by omega) (by omega)]; exact rdW
    obtain ⟨m3, s3, a3, w3, r3, e3⟩ := eng_bin_ok (d := d + q + 1) (a := d + q + 1 + 2) (b := d) (o := 27) p2'.left
      (by omega) (by omega) (by omega) r2 w1
      (g := fun a b => some (Runner.IR.bool (a.ult b))) rfl (by decide) rfl
    subst e3
    have p3 := p2'.next a3 (by omega : d + q + 1 ≤ d + q + 1 + 1) (by omega)
    obtain ⟨m4, s4, a4, w4, r4, e4⟩ := const_ok (k := 256) p3.left (by decide) (by omega)
    subst e4
    have p4 := p3.next a4 (Nat.le_refl _) (by omega)
    have w4' : m4.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 (strN vs.1)) := by
      rw [agree_rd_low a4 room (by omega) (by omega), agree_rd_low a3 room (by omega) (by omega)]; exact w1
    obtain ⟨m5, s5, a5, w5, r5, e5⟩ := eng_bin_ok (d := d + q + 1 + 1) (a := d) (b := d + q + 1 + 1) (o := 4) p4.left
      (by omega) (by omega) (by omega) w4' r4
      (g := fun a b => some (a - b)) rfl (by decide) rfl
    subst e5
    have p5 := p4.next a5 (Nat.le_refl _) (by omega)
    have flag5 : m5.rd64 (slot fp (BitVec.ofNat 64 (d + q + 1))) =
        some (Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (strN vs.1)))) := by
      rw [agree_rd_low a5 room (by omega) (by omega), agree_rd_low a4 room (by omega) (by omega)]; exact r3
    obtain ⟨m6, s6, a6, w6, r6, e6⟩ := eng_bin_ok (d := d + q + 1 + 1) (a := d + q + 1 + 1) (b := d + q + 1) (o := 5)
      p5.left (by omega) (by omega) (by omega) r5 flag5
      (g := fun a b => some (a * b)) rfl (by decide) rfl
    subst e6
    have p6 := p5.next a6 (Nat.le_refl _) (by omega)
    have flag6 : m6.rd64 (slot fp (BitVec.ofNat 64 (d + q + 1))) =
        some (Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (strN vs.1)))) := by
      rw [agree_rd_low a6 room (by omega) (by omega)]; exact flag5
    have frame6 : FrameOK m6 fp K := ((((frame1.agree a2).agree a3).agree a4).agree a5).agree a6
    have p6D : Pre L m6 _ fp K d (copyWords 2 d (d + q + 1) ++ (constWords (List.replicate (q - 1) 0) (d + 2)).1) ρ W reserved :=
      { p6 with ctx := by have := hp.ctx; omega }
    obtain ⟨m7, s7, a7, wa7⟩ := copyWords_run (fp := fp) (K := K) (dst := d) (src := d + q + 1)
      [Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (strN vs.1))),
       (BitVec.ofNat 64 (strN vs.1) - BitVec.ofInt 64 256) *
         Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (strN vs.1)))]
      frame6 small (show d + 2 ≤ K by omega) (show d + q + 1 + 2 ≤ K by omega) (Or.inl (by omega))
      p6D.left.code
      (by have := p6D.left.far; simp only [copyWords_length] at this; exact this)
      (by
        intro i hi
        have hi2 : i < 2 := hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact flag6
        · exact r6)
    have n7 := p6D.next (Agree.widen a7 (show d + 2 ≤ K by omega)) (by omega : d ≤ d + 2) (by omega)
    obtain ⟨m8, s8, a8, wz⟩ := constWords_ok (L := L) (d := d + 2) (List.replicate (q - 1) 0) (by omega) n7
    refine ⟨m8, ?_, ?_, ⟨trivial, ?_⟩⟩
    · have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m8 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m8 :=
        fun p q h s => h ▸ s
      refine key _ _ ?_ (run1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8)))))))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append, strExpandHead_length,
        copyWords_length, List.length_cons, List.length_nil]
      omega
    · exact ch1.trans (((a2.mono (by omega)).trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans
        ((a5.mono (by omega)).trans (a6.mono (by omega)))))).trans
        ((Agree.widen a7 (show d + 2 ≤ K by omega)).trans (a8.mono (by omega))))
    · rw [expand_words L hn1 hq2 vs, wordsAt_append]
      refine ⟨WordsAt.agree_low wa7 a8 room (show d + 2 ≤ d + 2 from Nat.le_refl _) (by omega), ?_⟩
      simpa using wz
  · cases h


variable {Λ : List (Res D)} {σ₀ σ : World D}

theorem strWeit_ok {n : Nat} (q : Nat) (s : Expr D Γ Λ (.str n))
    (ih : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.strWeit q s) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str q) (eval σ₀ (.strWeit q s) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    refine Ok.value ?_ (by simp only [valueWords, if_pos hn.2])
    split at h
    · next hz =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact (const_ok hp (by decide) (by omega)).mono fun w hw => by
        exact ⟨hn.2, by simpa [eval, strWeitW, hz, strN] using hw⟩
    · next hz =>
      have hlen : (eval σ₀ s σ ρ).1.length ≤ q := by have := (eval σ₀ s σ ρ).2; omega
      exact ((ih c top h hK m pc hp).word hn.1).mono fun w hw =>
        ⟨hn.2, by simpa [eval, strWeitW, List.take_of_length_le hlen] using hw.2⟩
  · split at h
    · next hl =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨cs, ts⟩, hs, out⟩ := h
      simp only [Prod.mk.injEq] at out
      obtain ⟨rfl, rfl⟩ := out
      obtain ⟨m1, run1, changed1, value1⟩ := ih cs ts hs (by omega) m pc hp.left
      have next := hp.next changed1 (by omega : d ≤ d + n + 1) (by omega : d ≤ K)
      obtain ⟨m2, run2, changed2, tail⟩ := constWords_ok (L := L) (List.replicate (q - n) 0) (by omega) next
      have hlen : (eval σ₀ s σ ρ).1.length ≤ n := (eval σ₀ s σ ρ).2
      have encoded : encodeWords L (.str q) (eval σ₀ (.strWeit q s) σ ρ) =
          encodeWords L (.str n) (eval σ₀ s σ ρ) ++ List.replicate (q - n) 0 := by
        simp only [encodeWords, eval, strWeitW, if_neg (show ¬ q ≤ 1 by omega),
          if_neg (show ¬ n ≤ 1 by omega), List.take_of_length_le (show (eval σ₀ s σ ρ).1.length ≤ q by omega)]
        simp only [List.append_assoc, List.replicate_append_replicate, List.cons.injEq, true_and, List.append_cancel_left_eq]
        congr 2
        omega
      refine ⟨m2, ?_, changed1.trans (changed2.mono (by omega)), trivial, ?_⟩
      · simpa only [List.length_append, pc_add] using run1.trans run2
      · have kept := value1.agree changed2 (hp.frame.agree changed1) (by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]; omega) (by omega)
        rw [encoded, wordsAt_append]
        refine ⟨kept.2, ?_⟩
        simpa only [encodeWords_length, valueWords, if_neg (show ¬ n ≤ 1 by omega), Nat.add_assoc] using tail
    · split at h
      · exact strExpand_ok (by omega) (by omega) (eval σ₀ s σ ρ) _ _ rfl
          (fun ca ta ha hta m pc hp => ih ca ta ha hta m pc hp) h hK hp
      · exact strTake_ok (eval σ₀ s σ ρ) _ (fun ca ta ha hta m pc hp => ih ca ta ha hta m pc hp) h hK hp


end Gabbro.Stage0.Senke
