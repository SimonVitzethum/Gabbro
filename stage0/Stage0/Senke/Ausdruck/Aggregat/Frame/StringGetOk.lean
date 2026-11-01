/- Subject: Generic correctness of byte access to a string of capacity at least two with any scalar index. -/
import Stage0.Senke.Ausdruck.Aggregat.Frame.StringGetCode
import Stage0.Senke.Ausdruck.Aggregat.StringOps
import Stage0.Senke.Ausdruck.Eng

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

/-- The unsigned test of a scalar index against the capacity is the range test `0 <= x < n`. -/
theorem ult_clamp {x : Int} {n : Nat} (hx0 : -2 ^ 63 ≤ x) (hx1 : x < 2 ^ 64) (hn : n < 2 ^ 31) :
    (BitVec.ofInt 64 x).ult (BitVec.ofInt 64 (n : Int)) = decide (0 ≤ x ∧ x < n) := by
  rw [Bool.eq_iff_iff]
  simp only [BitVec.ult, BitVec.toNat_ofInt, decide_eq_true_eq]
  omega

/-- `n + (x < n) * (x - n)` is the index itself when it is in range and the sentinel position `n` otherwise. -/
theorem clamp_word {x : Int} {n : Nat} (hx0 : -2 ^ 63 ≤ x) (hx1 : x < 2 ^ 64) (hn : n < 2 ^ 31) :
    (BitVec.ofInt 64 x - BitVec.ofInt 64 (n : Int)) *
      Runner.IR.bool ((BitVec.ofInt 64 x).ult (BitVec.ofInt 64 (n : Int))) + BitVec.ofInt 64 (n : Int) =
      BitVec.ofNat 64 (if 0 ≤ x ∧ x < n then x.toNat else n) := by
  rw [ult_clamp hx0 hx1 hn]
  by_cases hin : 0 ≤ x ∧ x < n
  · simp only [hin, decide_true, ite_true, Runner.IR.bool, and_self]
    have key : ∀ a b : Runner.W, (a - b) * 1 + b = a := by intro a b; bv_omega
    rw [key, ← BitVec.ofInt_natCast, Int.toNat_of_nonneg hin.1]
  · simp only [hin, decide_false, ite_false, Runner.IR.bool, Bool.false_eq_true]
    have key : ∀ a b : Runner.W, (a - b) * 0 + b = b := by intro a b; bv_omega
    rw [key, BitVec.ofInt_natCast]

/-- The seven clamp instructions leave the clamped index in slot `p + 3` and write nothing below `p + 1`. -/
theorem strGetClamp_ok {n p : Nat} {x : Int} (hn31 : n < 2 ^ 31)
    (hx0 : -2 ^ 63 ≤ x) (hx1 : x < 2 ^ 64)
    (hp : Pre L m pc fp K (p + 1) (strGetClamp n p) ρ W reserved) (hK : p + 4 ≤ K)
    (rd : m.rd64 (slot fp (BitVec.ofNat 64 p)) = some (BitVec.ofInt 64 x)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 7), fp⟩ m' ∧ Agree fp (p + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (p + 3))) =
        some (BitVec.ofNat 64 (if 0 ≤ x ∧ x < n then x.toNat else n)) := by
  have small := hp.small
  have room := hp.frame.room
  have lit : lit32 (n : Int) = true := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega
  have hp' : Pre L m pc fp K (p + 1)
      ([ci 1 ((p + 1 : Nat) : Int) n 0] ++ ([ci 27 ((p + 1 : Nat) : Int) p ((p + 1 : Nat) : Int)] ++
      ([ci 1 ((p + 2 : Nat) : Int) n 0] ++ ([ci 4 ((p + 2 : Nat) : Int) p ((p + 2 : Nat) : Int)] ++
      ([ci 5 ((p + 2 : Nat) : Int) ((p + 2 : Nat) : Int) ((p + 1 : Nat) : Int)] ++
      ([ci 1 ((p + 3 : Nat) : Int) n 0] ++ [ci 3 ((p + 3 : Nat) : Int) ((p + 2 : Nat) : Int) ((p + 3 : Nat) : Int)])))))) ρ W reserved := hp
  obtain ⟨m1, s1, a1, w1, r1, e1⟩ := const_ok hp'.left lit (by omega)
  subst e1
  have p1 := hp'.next a1 (Nat.le_refl _) (by omega)
  have rd1 : m1.rd64 (slot fp (BitVec.ofNat 64 p)) = some (BitVec.ofInt 64 x) := by
    rw [agree_rd_low a1 room (by omega) (by omega)]; exact rd
  obtain ⟨m2, s2, a2, w2, r2, e2⟩ := eng_bin_ok (d := p + 1) (a := p) (b := p + 1) (o := 27) p1.left
    (by omega) (by omega) (by omega) rd1 r1
    (g := fun a b => some (Runner.IR.bool (a.ult b))) rfl (by decide) rfl
  subst e2
  have p2 := p1.next a2 (by omega : p + 1 ≤ p + 2) (by omega)
  have rd2 : m2.rd64 (slot fp (BitVec.ofNat 64 p)) = some (BitVec.ofInt 64 x) := by
    rw [agree_rd_low a2 room (by omega) (by omega)]; exact rd1
  obtain ⟨m3, s3, a3, w3, r3, e3⟩ := const_ok p2.left lit (by omega)
  subst e3
  have p3 := p2.next a3 (Nat.le_refl _) (by omega)
  have rd3 : m3.rd64 (slot fp (BitVec.ofNat 64 p)) = some (BitVec.ofInt 64 x) := by
    rw [agree_rd_low a3 room (by omega) (by omega)]; exact rd2
  obtain ⟨m4, s4, a4, w4, r4, e4⟩ := eng_bin_ok (d := p + 2) (a := p) (b := p + 2) (o := 4) p3.left
    (by omega) (by omega) (by omega) rd3 r3
    (g := fun a b => some (a - b)) rfl (by decide) rfl
  subst e4
  have p4 := p3.next a4 (Nat.le_refl _) (by omega)
  have flag4 : m4.rd64 (slot fp (BitVec.ofNat 64 (p + 1))) =
      some (Runner.IR.bool ((BitVec.ofInt 64 x).ult (BitVec.ofInt 64 (n : Int)))) := by
    rw [agree_rd_low a4 room (by omega) (by omega), agree_rd_low a3 room (by omega) (by omega)]; exact r2
  obtain ⟨m5, s5, a5, w5, r5, e5⟩ := eng_bin_ok (d := p + 2) (a := p + 2) (b := p + 1) (o := 5) p4.left
    (by omega) (by omega) (by omega) r4 flag4
    (g := fun a b => some (a * b)) rfl (by decide) rfl
  subst e5
  have p5 := p4.next a5 (by omega : p + 2 ≤ p + 3) (by omega)
  obtain ⟨m6, s6, a6, w6, r6, e6⟩ := const_ok p5.left lit (by omega)
  subst e6
  have p6 := p5.next a6 (Nat.le_refl _) (by omega)
  have r5' : m6.rd64 (slot fp (BitVec.ofNat 64 (p + 2))) =
      some ((BitVec.ofInt 64 x - BitVec.ofInt 64 (n : Int)) *
        Runner.IR.bool ((BitVec.ofInt 64 x).ult (BitVec.ofInt 64 (n : Int)))) := by
    rw [agree_rd_low a6 room (by omega) (by omega)]; exact r5
  obtain ⟨m7, s7, a7, w7, r7, e7⟩ := eng_bin_ok (d := p + 3) (a := p + 2) (b := p + 3) (o := 3) p6.left
    (by omega) (by omega) (by omega) r5' r6
    (g := fun a b => some (a + b)) rfl (by decide) rfl
  subst e7
  refine ⟨m7, ?_, ?_, ?_⟩
  · have steps := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))
    simpa only [List.length_cons, List.length_nil, List.length_singleton, pc_add, Nat.reduceAdd] using steps
  · exact a1.trans ((a2.mono (Nat.le_refl _)).trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans
      ((a5.mono (by omega)).trans ((a6.mono (by omega)).trans (a7.mono (by omega)))))))
  · rw [r7, clamp_word hx0 hx1 hn31]

/-- Outside `[0, n)` the byte is the zero byte. -/
theorem strGetW_out {n : Nat} (w : Wert D (.str n)) (x : Int)
    (hx : x < 0 ∨ (n : Int) ≤ x) : strGetW (n := n) w x = ⟨0, by omega, by omega⟩ := by
  unfold strGetW
  split
  · next h0 =>
    have none : w.1[x.toNat]? = none := List.getElem?_eq_none (by have := w.2; omega)
    rw [none]; rfl
  · rfl

/-- The clamped position holds the byte: bytes below `n` in the span, the zero sentinel at `n`. -/
theorem strClamped_byte {n : Nat} (hn2 : 2 ≤ n) {m : Runner.Mem} {fp : Runner.W} {d : Nat}
    (w : Wert D (.str n))
    (span : ValueAt L m fp d (.str n) w)
    (sentinel : m.rd64 (slot fp (BitVec.ofNat 64 (d + n + 1))) = some (BitVec.ofInt 64 0))
    (j : Nat) (hj : j ≤ n) :
    ValueAt L m fp ((d + 1) + j * valueWords (.int 0 255)) (.int 0 255) (strGetW (n := n) w (j : Int)) := by
  have w1 : valueWords (.int 0 255) = 1 := by decide
  rw [w1, Nat.mul_one]
  by_cases below : j < n
  · have hget : (encodeWords L (.str n) w)[j + 1]? =
        some (BitVec.ofInt 64 (strGetW (n := n) w (j : Int)).n) := by
      simp only [encodeWords, if_neg (show ¬ n ≤ 1 by omega)]
      exact strBytes_word (n := n) w j below
    have inRange : j + 1 < (encodeWords L (.str n) w).length := by
      rw [encodeWords_length]; simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]; omega
    have atWord := span.2 (1 + j) (by rw [Nat.add_comm 1 j]; exact inRange)
    have key : ∀ k, k = j + 1 → ∀ (hk : k < (encodeWords L (.str n) w).length),
        (encodeWords L (.str n) w)[k]'hk = BitVec.ofInt 64 (strGetW (n := n) w (j : Int)).n := by
      intro k hk' hk
      subst hk'
      exact Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hget)
    refine ValueAt.of_enc w1 ?_ rfl
    rw [show (d + 1) + j = d + (1 + j) by omega, atWord, key (1 + j) (Nat.add_comm 1 j)]
  · have jn : n = j := by omega
    subst jn
    refine ValueAt.of_enc w1 ?_ ?_ (w := BitVec.ofInt 64 0)
    · rw [show (d + 1) + n = d + n + 1 by omega]; exact sentinel
    · rw [strGetW_out (n := n) w (n : Int) (Or.inr (Int.le_refl _))]; rfl

/-- Byte access with a scalar index of any range on a string of capacity at least two: the clamp keeps the
    selection inside the span (or on the sentinel), so the result is the model's byte, zero out of range. -/
theorem strGetWide_ok {n : Nat} {lo hi : Int} (vs : Wert D (.str n)) (vi : Zahl lo hi)
    (fits : scalarFits lo hi = true) (s i : Option (List II × Nat))
    (ihs : ∀ ca ta, s = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) vs)
    (ihi : ∀ ca ta, i = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + n + 2) ca ρ W reserved → ValueOk L m pc fp K (d + n + 2) ca (.int lo hi) vi)
    (h : strGetWideL n d s i = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 255) (strGetW (n := n) vs vi.n) := by
  simp only [strGetWideL] at h
  split at h
  · next g =>
    obtain ⟨hn2, hn31⟩ := g
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs, ⟨cx, tx⟩, hix, rfl, rfl⟩ := h
    have small := hp.small
    have room := hp.frame.room
    have wn : valueWords (.str n) = n + 1 := by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]
    have w1 : valueWords (.int 0 255) = 1 := by decide
    have hxr : -2 ^ 63 ≤ vi.n ∧ vi.n < 2 ^ 64 := by
      have := vi.lo_le; have := vi.le_hi
      simp only [scalarFits, inW, inU, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at fits
      omega
    have hp' : Pre L m pc fp K d (cs ++ ([ci 1 ((d + n + 1 : Nat) : Int) 0 0] ++ (cx ++
        (strGetClamp n (d + n + 1 + 1) ++ selectFrameSpan 1 (d + 1) d (d + n + 1 + 1 + 3) (d + n + 1 + 1 + 4)))))
        ρ W reserved := by
      have h0 := hp
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h0 ⊢
      exact h0
    obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp'.left
    have n1 := hp'.next ch1 (by omega : d ≤ d + n + 1) (by omega)
    obtain ⟨m2, run2, ch2, w2, r2, e2⟩ := const_ok (k := 0) n1.left (by decide) (by omega)
    subst e2
    have n2 := n1.next ch2 (by omega : d + n + 1 ≤ d + n + 1 + 1) (by omega)
    obtain ⟨m3, run3, ch3, vi3⟩ := ihi cx tx hix (by omega) m2 _ n2.left
    have n3 := n2.next ch3 (by omega : d + n + 1 + 1 ≤ d + n + 1 + 1 + 1) (by omega)
    obtain ⟨wi, rdi, enci⟩ := ValueAt.word (.int lo hi) vi trivial vi3
    change wi = BitVec.ofInt 64 vi.n at enci
    subst enci
    obtain ⟨m4, run4, ch4, rd4⟩ := strGetClamp_ok (p := d + n + 1 + 1) hn31 hxr.1 hxr.2 n3.left (by omega) rdi
    have n4 := n3.next ch4 (by omega : d + n + 1 + 1 + 1 ≤ d + n + 1 + 1 + 3) (by omega)
    have frame1 := hp.frame.agree ch1
    have frame2 := frame1.agree ch2
    have frame3 := frame2.agree ch3
    have vs2 := vs1.agree ch2 frame1 (by rw [wn]; omega) (by omega)
    have vs3 := vs2.agree ch3 frame2 (by rw [wn]; omega) (by omega)
    have vs4 := vs3.agree ch4 frame3 (by rw [wn]; omega) (by omega)
    have sent3 : m3.rd64 (slot fp (BitVec.ofNat 64 (d + n + 1))) = some (BitVec.ofInt 64 0) := by
      rw [agree_rd_low ch3 room (by omega) (by omega)]; exact r2
    have sent4 : m4.rd64 (slot fp (BitVec.ofNat 64 (d + n + 1))) = some (BitVec.ofInt 64 0) := by
      rw [agree_rd_low ch4 room (by omega) (by omega)]; exact sent3
    obtain ⟨j, hjdef⟩ : ∃ j : Nat, j = (if 0 ≤ vi.n ∧ vi.n < n then vi.n.toNat else n) := ⟨_, rfl⟩
    have hj : j ≤ n := by rw [hjdef]; split <;> omega
    rw [← hjdef] at rd4
    have byteWord := strClamped_byte (L := L) hn2 vs vs4 sent4 j hj
    obtain ⟨m5, run5, ch5, result⟩ := selectFrameSpan_ok (base := d + 1) (dst := d) (index := j)
      (τ := .int 0 255) (by rw [w1]; omega) (by rw [w1]; omega) (Nat.lt_succ_self _) (by omega)
      (by rw [w1]; decide) rd4 byteWord n4
    have same : strGetW (n := n) vs (j : Int) = strGetW (n := n) vs vi.n := by
      by_cases hin : 0 ≤ vi.n ∧ vi.n < n
      · rw [hjdef, if_pos hin, Int.toNat_of_nonneg hin.1]
      · rw [hjdef, if_neg hin, strGetW_out (n := n) vs (n : Int) (Or.inr (Int.le_refl _)),
          strGetW_out (n := n) vs vi.n (by omega)]
    rw [same] at result
    refine ⟨m5, ?_, ?_, result⟩
    · have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m5 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m5 :=
        fun p q h s => h ▸ s
      refine key _ _ ?_ (run1.trans (run2.trans (run3.trans (run4.trans run5))))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append, List.length_cons,
        List.length_nil, strGetClamp_length, selectFrameSpan_length]
      omega
    · exact ch1.trans ((ch2.mono (by omega)).trans ((ch3.mono (by omega)).trans
        ((ch4.mono (by omega)).trans ch5)))
  · cases h


theorem strGet_ok {n : Nat} {lo hi : Int} (s : Expr D Γ Λ (.str n)) (i : Expr D Γ Λ (.int lo hi))
    (ihs : ∀ ca ta, lowE L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (ihi : ∀ ca ta, lowE L (reserved := reserved) i d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.int lo hi) (eval σ₀ i σ ρ))
    (ihl : ∀ ca ta, lowE L (reserved := reserved) i (d + n + 2) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + n + 2) ca ρ W reserved →
        ValueOk L m pc fp K (d + n + 2) ca (.int lo hi) (eval σ₀ i σ ρ))
    (h : lowE L (reserved := reserved) (.strGet s i) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 255) (eval σ₀ (.strGet s i) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    refine Ok.value ?_ (by decide)
    have hd := strGetL_top h
    refine wennL_ok h hK (by omega) (bc := decide ((eval σ₀ i σ ρ).n = 0)) ?_ ?_ ?_ hp
    · intro cc tc hc htc m pc hp
      refine wordK_ok hc htc (by decide)
        (fun ca ta ha ht m pc hp => (ihi ca ta ha ht m pc hp).word trivial)
        (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) hp
      intro wi hi
      refine ⟨_, rfl, ?_⟩
      rw [hi, beq_in (inW_spec hn.2 (eval σ₀ i σ ρ).lo_le (eval σ₀ i σ ρ).le_hi) (by decide), bool_word]
    · intro he ca ta ha hta m pc hp
      have hz : (eval σ₀ i σ ρ).n = 0 := by simpa using he
      refine wordK_ok ha hta (by decide)
        (fun ca ta ha ht m pc hp => (ihs ca ta ha ht m pc hp).word hn.1)
        (g := fun x y => some (x &&& y)) ?_ rfl (by decide) hp
      intro ws hs
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval]
      rw [hz, hs.2]
      exact strN_byte (eval σ₀ s σ ρ) hn.1
    · intro he cb tb hb htb m pc hp
      have hz : (eval σ₀ i σ ρ).n ≠ 0 := by simpa using he
      cases hb
      exact (const_ok hp (by decide) (by omega)).mono fun w hw => by
        simpa [Enc, eval, short_get_other (eval σ₀ s σ ρ) hn.1 _ hz] using hw
  · split at h
    · next hf =>
      exact strGetWide_ok (eval σ₀ s σ ρ) (eval σ₀ i σ ρ) hf _ _ ihs ihl h hK hp
    · cases h

end Gabbro.Stage0.Senke
