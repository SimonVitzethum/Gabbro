/- Subject: Generic correctness of narrowing a string of capacity at least two to a smaller maximum. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeCode
public import Stage0.Senke.Ausdruck.Aggregat.StringOps
public import Stage0.Senke.Ausdruck.Eng
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

/-- A binary instruction with its exact footprint: only its own destination slot changes. -/
theorem bin_exact_ok {a b o : Nat} {va vb r : Runner.W}
    {g : Runner.W → Runner.W → Option Runner.W}
    (hp : Pre L m pc fp K d [ci o d a b] ρ W reserved) (hd : d < K) (ha : a < K) (hb : b < K)
    (ra : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some va)
    (rb : m.rd64 (slot fp (BitVec.ofNat 64 b)) = some vb)
    (hop : op o = bin g) (ho : o < 256) (hg : g va vb = some r) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m' ∧ Agree fp d (d + 1) m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some r := by
  have small := hp.small
  obtain ⟨hw, hrd, _⟩ := wr_slot hp.frame hd r
  refine ⟨_, ?_, agree_write (K := d + 1) (by have := hp.frame.room; omega) (Nat.le_refl d)
    (Nat.lt_succ_self d) _, hrd⟩
  refine star_ins hp.code (by simpa [ci] using ho) ?_
  have hi := hp.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  simp only [ci]
  rw [hop]
  apply run_bin hi
  · simpa only [sx_nat (d := a) (by omega)] using ra
  · simpa only [sx_nat (d := b) (by omega)] using rb
  · exact hg
  · simpa only [sx_nat (d := d) (by omega)] using hw

/-- Narrowed encoding: the new length word, then the byte words `1 .. m` of the wider string. -/
theorem strTake_encode (L : Lay D) {n m : Nat} (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hmn : m ≤ n)
    (w : Wert D (.str n)) :
    encodeWords L (.str m) (strWeitW (n := n) m w) =
      BitVec.ofNat 64 (min w.1.length m) :: ((encodeWords L (.str n) w).drop 1).take m := by
  have hlen : w.1.length ≤ n := w.2
  simp only [encodeWords, strWeitW, if_neg (show ¬ m ≤ 1 by omega), if_neg (show ¬ n ≤ 1 by omega),
    List.length_take, List.cons_append, List.drop_succ_cons, List.drop_zero]
  rw [Nat.min_comm w.1.length m]
  congr 1
  rw [List.take_append, List.take_replicate, List.length_map, List.map_take]
  congr 2
  omega

/-- The length word of a long string span. -/
theorem span_len_read {n b : Nat} (hn2 : 2 ≤ n) {m : Runner.Mem} {fp : Runner.W} (vs : Wert D (.str n))
    (span : ValueAt L m fp b (.str n) vs) :
    m.rd64 (slot fp (BitVec.ofNat 64 b)) = some (BitVec.ofNat 64 vs.1.length) := by
  have wn : valueWords (.str n) = n + 1 := by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]
  have h0 := span.2 0 (by rw [encodeWords_length, wn]; omega)
  simpa only [Nat.add_zero, encodeWords, if_neg (show ¬ n ≤ 1 by omega), List.cons_append,
    List.getElem_cons_zero] using h0

/-- The word of the first byte of a long string span (zero for the empty string). -/
theorem span_byte_read {n b : Nat} (hn2 : 2 ≤ n) {m : Runner.Mem} {fp : Runner.W} (vs : Wert D (.str n))
    (span : ValueAt L m fp b (.str n) vs) :
    m.rd64 (slot fp (BitVec.ofNat 64 (b + 1))) =
      some (BitVec.ofInt 64 (strGetW (n := n) vs (0 : Nat)).n) := by
  have wn : valueWords (.str n) = n + 1 := by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]
  have h1 := span.2 1 (by rw [encodeWords_length, wn]; omega)
  have hget : (encodeWords L (.str n) vs)[0 + 1]? =
      some (BitVec.ofInt 64 (strGetW (n := n) vs (0 : Nat)).n) := by
    simp only [encodeWords, if_neg (show ¬ n ≤ 1 by omega)]
    exact strBytes_word (n := n) vs 0 (by omega)
  have inRange : 1 < (encodeWords L (.str n) vs).length := by
    rw [encodeWords_length, wn]; omega
  rw [List.getElem?_eq_getElem inRange] at hget
  rw [h1]
  exact congrArg some (Option.some.inj hget)

/-- The branch-free minimum of the length word and the new capacity. -/
theorem take_len_word {len q : Nat} (hl : len < 2 ^ 31) (hq : q < 2 ^ 31) :
    BitVec.ofNat 64 len - (BitVec.ofNat 64 len - BitVec.ofInt 64 (q : Int)) *
      Runner.IR.bool ((BitVec.ofInt 64 (q : Int)).ult (BitVec.ofNat 64 len)) =
      BitVec.ofNat 64 (min len q) := by
  rw [BitVec.ofInt_natCast]
  by_cases h : q < len
  · have flag : (BitVec.ofNat 64 q).ult (BitVec.ofNat 64 len) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have key : ∀ a b : Runner.W, a - (a - b) * 1 = b := by intro a b; bv_omega
    rw [flag]
    simp only [Runner.IR.bool, ite_true]
    rw [key, Nat.min_eq_right (by omega)]
  · have flag : (BitVec.ofNat 64 q).ult (BitVec.ofNat 64 len) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have key : ∀ a b : Runner.W, a - (a - b) * 0 = a := by intro a b; bv_omega
    rw [flag]
    simp only [Runner.IR.bool, Bool.false_eq_true, ite_false]
    rw [key, Nat.min_eq_left (by omega)]

/-- The five length instructions narrow the string span in place: the length word becomes `min len q`, the
    byte words `1 .. q` are untouched, the scratch words above the source are free. -/
theorem strTakeLen_ok {n q : Nat} (hn2 : 2 ≤ n) (hq2 : 2 ≤ q) (hqn : q < n) (hn31 : n < 2 ^ 31)
    (vs : Wert D (.str n))
    (hp : Pre L m pc fp K d (strTakeLenL q d (d + n + 1)) ρ W reserved) (hK : d + n + 1 + 3 ≤ K)
    (span : ValueAt L m fp d (.str n) vs) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 5), fp⟩ m' ∧ Agree fp d K m m' ∧
      ValueAt L m' fp d (.str q) (strWeitW (n := n) q vs) := by
  have small := hp.small
  have room := hp.frame.room
  have wn : valueWords (.str n) = n + 1 := by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]
  have lit : lit32 (q : Int) = true := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega
  have hlen : vs.1.length ≤ n := vs.2
  have hpt : Pre L m pc fp K (d + n + 1)
      ([ci 1 ((d + n + 1 : Nat) : Int) q 0] ++ ([ci 27 ((d + n + 1 + 1 : Nat) : Int) ((d + n + 1 : Nat) : Int) d] ++
      ([ci 4 ((d + n + 1 + 2 : Nat) : Int) d ((d + n + 1 : Nat) : Int)] ++
      ([ci 5 ((d + n + 1 + 2 : Nat) : Int) ((d + n + 1 + 2 : Nat) : Int) ((d + n + 1 + 1 : Nat) : Int)] ++
      [ci 4 d d ((d + n + 1 + 2 : Nat) : Int)])))) ρ W reserved :=
    { (show Pre L m pc fp K d _ ρ W reserved from hp) with ctx := by have := hp.ctx; omega }
  have lenRead := span_len_read hn2 vs span
  obtain ⟨m1, s1, a1, w1, r1, e1⟩ := const_ok (k := q) hpt.left lit (by omega)
  subst e1
  have p1 := hpt.next a1 (by omega : d + n + 1 ≤ d + n + 1 + 1) (by omega)
  have len1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 vs.1.length) := by
    rw [agree_rd_low a1 room (by omega) (by omega)]; exact lenRead
  obtain ⟨m2, s2, a2, w2, r2, e2⟩ := eng_bin_ok (d := d + n + 1 + 1) (a := d + n + 1) (b := d) (o := 27) p1.left
    (by omega) (by omega) (by omega) r1 len1
    (g := fun a b => some (Runner.IR.bool (a.ult b))) rfl (by decide) rfl
  subst e2
  have p2 := p1.next a2 (by omega : d + n + 1 + 1 ≤ d + n + 1 + 2) (by omega)
  have len2 : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 vs.1.length) := by
    rw [agree_rd_low a2 room (by omega) (by omega)]; exact len1
  have q2 : m2.rd64 (slot fp (BitVec.ofNat 64 (d + n + 1))) = some (BitVec.ofInt 64 (q : Int)) := by
    rw [agree_rd_low a2 room (by omega) (by omega)]; exact r1
  obtain ⟨m3, s3, a3, w3, r3, e3⟩ := eng_bin_ok (d := d + n + 1 + 2) (a := d) (b := d + n + 1) (o := 4) p2.left
    (by omega) (by omega) (by omega) len2 q2
    (g := fun a b => some (a - b)) rfl (by decide) rfl
  subst e3
  have p3 := p2.next a3 (Nat.le_refl _) (by omega)
  have len3 : m3.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 vs.1.length) := by
    rw [agree_rd_low a3 room (by omega) (by omega)]; exact len2
  have flag3 : m3.rd64 (slot fp (BitVec.ofNat 64 (d + n + 1 + 1))) =
      some (Runner.IR.bool ((BitVec.ofInt 64 (q : Int)).ult (BitVec.ofNat 64 vs.1.length))) := by
    rw [agree_rd_low a3 room (by omega) (by omega)]; exact r2
  obtain ⟨m4, s4, a4, w4, r4, e4⟩ := eng_bin_ok (d := d + n + 1 + 2) (a := d + n + 1 + 2) (b := d + n + 1 + 1) (o := 5)
    p3.left (by omega) (by omega) (by omega) r3 flag3
    (g := fun a b => some (a * b)) rfl (by decide) rfl
  subst e4
  have p4 := p3.next a4 (Nat.le_refl _) (by omega)
  have len4 : m4.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 vs.1.length) := by
    rw [agree_rd_low a4 room (by omega) (by omega)]; exact len3
  have p4' : Pre L m4 _ fp K d [ci 4 d d ((d + n + 1 + 2 : Nat) : Int)] ρ W reserved :=
    { p4 with ctx := by have := hp.ctx; omega }
  obtain ⟨m5, s5, a5, r5⟩ := bin_exact_ok (d := d) (a := d) (b := d + n + 1 + 2) (o := 4) p4'
    (by omega) (by omega) (by omega) len4 r4 (g := fun a b => some (a - b)) rfl (by decide) rfl
  have kept : ∀ i, 1 ≤ i → i ≤ q → m5.rd64 (slot fp (BitVec.ofNat 64 (d + i))) =
      m.rd64 (slot fp (BitVec.ofNat 64 (d + i))) := by
    intro i h1 h2
    rw [agree_rd_above a5 room (by omega) (by omega), agree_rd_low a4 room (by omega) (by omega),
      agree_rd_low a3 room (by omega) (by omega), agree_rd_low a2 room (by omega) (by omega),
      agree_rd_low a1 room (by omega) (by omega)]
  refine ⟨m5, ?_, ?_, ?_⟩
  · have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m5 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m5 :=
      fun p q h s => h ▸ s
    refine key _ _ ?_ (s1.trans (s2.trans (s3.trans (s4.trans s5))))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_cons, List.length_nil]
    omega
  · exact (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans
      (Agree.widen a5 (by omega)))))
  · refine ⟨span.1, ?_⟩
    rw [strTake_encode L hn2 hq2 (by omega) vs]
    intro i hi
    cases i with
    | zero =>
      rw [Nat.add_zero]
      simp only [List.getElem_cons_zero]
      rw [r5, take_len_word (by omega) (by omega)]
    | succ j =>
      have hj : j < q := by
        simp only [List.length_cons, List.length_take, List.length_drop, encodeWords_length, wn] at hi
        omega
      rw [kept (j + 1) (by omega) (by omega)]
      simp only [List.getElem_cons_succ, List.getElem_take, List.getElem_drop]
      have := span.2 (1 + j) (by rw [encodeWords_length, wn]; omega)
      rw [show d + (1 + j) = d + (j + 1) by omega] at this
      exact this

/-- Narrowing to capacity one packs the first byte: `0` for the empty string, `256 + byte` otherwise. -/
theorem strTakePack_ok {n : Nat} (hn2 : 2 ≤ n) (hn31 : n < 2 ^ 31)
    (vs : Wert D (.str n))
    (hp : Pre L m pc fp K d (strTakePackL d (d + n + 1)) ρ W reserved) (hK : d + n + 1 + 3 ≤ K)
    (span : ValueAt L m fp d (.str n) vs) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 5), fp⟩ m' ∧ Agree fp d K m m' ∧
      ValueAt L m' fp d (.str 1) (strWeitW (n := n) 1 vs) := by
  have small := hp.small
  have room := hp.frame.room
  have wn : valueWords (.str n) = n + 1 := by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]
  have hlen : vs.1.length ≤ n := vs.2
  have hpt : Pre L m pc fp K (d + n + 1)
      ([ci 1 ((d + n + 1 : Nat) : Int) 0 0] ++ ([ci 27 ((d + n + 1 + 1 : Nat) : Int) ((d + n + 1 : Nat) : Int) d] ++
      ([ci 1 ((d + n + 1 + 2 : Nat) : Int) 256 0] ++
      ([ci 3 ((d + n + 1 + 2 : Nat) : Int) ((d + n + 1 + 2 : Nat) : Int) ((d + 1 : Nat) : Int)] ++
      [ci 5 d ((d + n + 1 + 1 : Nat) : Int) ((d + n + 1 + 2 : Nat) : Int)])))) ρ W reserved :=
    { (show Pre L m pc fp K d _ ρ W reserved from hp) with ctx := by have := hp.ctx; omega }
  have lenRead := span_len_read hn2 vs span
  have byteRead := span_byte_read hn2 vs span
  obtain ⟨m1, s1, a1, w1, r1, e1⟩ := const_ok (k := 0) hpt.left (by decide) (by omega)
  subst e1
  have p1 := hpt.next a1 (by omega : d + n + 1 ≤ d + n + 1 + 1) (by omega)
  have len1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 vs.1.length) := by
    rw [agree_rd_low a1 room (by omega) (by omega)]; exact lenRead
  obtain ⟨m2, s2, a2, w2, r2, e2⟩ := eng_bin_ok (d := d + n + 1 + 1) (a := d + n + 1) (b := d) (o := 27) p1.left
    (by omega) (by omega) (by omega) r1 len1
    (g := fun a b => some (Runner.IR.bool (a.ult b))) rfl (by decide) rfl
  subst e2
  have p2 := p1.next a2 (by omega : d + n + 1 + 1 ≤ d + n + 1 + 2) (by omega)
  obtain ⟨m3, s3, a3, w3, r3, e3⟩ := const_ok (k := 256) p2.left (by decide) (by omega)
  subst e3
  have p3 := p2.next a3 (Nat.le_refl _) (by omega)
  have byte3 : m3.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) =
      some (BitVec.ofInt 64 (strGetW (n := n) vs (0 : Nat)).n) := by
    rw [agree_rd_low a3 room (by omega) (by omega), agree_rd_low a2 room (by omega) (by omega),
      agree_rd_low a1 room (by omega) (by omega)]
    exact byteRead
  obtain ⟨m4, s4, a4, w4, r4, e4⟩ := eng_bin_ok (d := d + n + 1 + 2) (a := d + n + 1 + 2) (b := d + 1) (o := 3) p3.left
    (by omega) (by omega) (by omega) r3 byte3
    (g := fun a b => some (a + b)) rfl (by decide) rfl
  subst e4
  have p4 := p3.next a4 (Nat.le_refl _) (by omega)
  have flag4 : m4.rd64 (slot fp (BitVec.ofNat 64 (d + n + 1 + 1))) =
      some (Runner.IR.bool ((BitVec.ofInt 64 0).ult (BitVec.ofNat 64 vs.1.length))) := by
    rw [agree_rd_low a4 room (by omega) (by omega), agree_rd_low a3 room (by omega) (by omega)]; exact r2
  have p4' : Pre L m4 _ fp K d [ci 5 d ((d + n + 1 + 1 : Nat) : Int) ((d + n + 1 + 2 : Nat) : Int)] ρ W reserved :=
    { p4 with ctx := by have := hp.ctx; omega }
  obtain ⟨m5, s5, a5, w5, r5, e5⟩ := eng_bin_ok (d := d) (a := d + n + 1 + 1) (b := d + n + 1 + 2) (o := 5) p4'
    (by omega) (by omega) (by omega) flag4 r4 (g := fun a b => some (a * b)) rfl (by decide) rfl
  subst e5
  refine ⟨m5, ?_, ?_, ?_⟩
  · have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m5 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m5 :=
      fun p q h s => h ▸ s
    refine key _ _ ?_ (s1.trans (s2.trans (s3.trans (s4.trans s5))))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_cons, List.length_nil]
    omega
  · exact (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans
      ((a4.mono (by omega)).trans a5)))
  · refine ValueAt.of_enc (by simp only [valueWords]; decide) r5 ?_
    simp only [Enc, strWeitW]
    refine ⟨Nat.le_refl _, ?_⟩
    rcases hbs : vs.1 with _ | ⟨b, rest⟩
    · have hn0 : strGetW (n := n) vs (0 : Nat) = ⟨0, by omega, by omega⟩ := by
        simp only [strGetW, Int.natCast_nonneg, ↓reduceIte, hbs]; rfl
      simp only [hbs, hn0, List.length_nil, List.take_nil, strN]
      have fl : (BitVec.ofInt 64 0).ult 0#64 = false := by decide
      rw [fl]
      simp only [Runner.IR.bool, Bool.false_eq_true, ite_false]
      bv_omega
    · have hb0 : (strGetW (n := n) vs (0 : Nat)).n = b.n := by
        simp only [strGetW, Int.natCast_nonneg, ↓reduceIte, hbs]; rfl
      have hl : rest.length + 1 ≤ n := by
        have := hlen; rw [hbs] at this; simpa using this
      have fl : (BitVec.ofInt 64 0).ult (BitVec.ofNat 64 (b :: rest).length) = true := by
        simp only [BitVec.ult, BitVec.toNat_ofInt, BitVec.toNat_ofNat, decide_eq_true_eq, List.length_cons]
        omega
      rw [fl, hb0]
      simp only [Runner.IR.bool, ite_true, List.take_succ_cons, List.take_zero, strN]
      have := b.lo_le
      have one : ∀ a : Runner.W, 1 * a = a := by intro a; bv_omega
      rw [one, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
      congr 1
      omega

/-- `strWeit q` of a string of capacity at least two to a smaller maximum: the first `q` bytes. -/
theorem strTake_ok {n q : Nat} (vs : Wert D (.str n)) (s : Option (List II × Nat))
    (ihs : ∀ ca ta, s = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) vs)
    (h : strTakeL n q d s = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str q) (strWeitW (n := n) q vs) := by
  simp only [strTakeL] at h
  split at h
  · next g =>
    obtain ⟨hn2, hqn, hn31⟩ := g
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cs, ts⟩, hs, h⟩ := h
    split at h
    · next hq2 =>
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp.left
      have n1 := hp.next ch1 (Nat.le_refl d) (by have := hp.small; omega)
      obtain ⟨m2, run2, ch2, v2⟩ := strTakeLen_ok hn2 hq2 hqn hn31 vs n1 (by omega) vs1
      refine ⟨m2, ?_, ch1.trans ch2, v2⟩
      simpa only [List.length_append, strTakeLenL_length, pc_add] using run1.trans run2
    · split at h
      · next hq1 =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp.left
        have n1 := hp.next ch1 (Nat.le_refl d) (by have := hp.small; omega)
        obtain ⟨m2, run2, ch2, v2⟩ := strTakePack_ok hn2 hn31 vs n1 (by omega) vs1
        subst hq1
        refine ⟨m2, ?_, ch1.trans ch2, v2⟩
        simpa only [List.length_append, strTakePackL_length, pc_add] using run1.trans run2
      · next hq1 =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hq0 : q = 0 := by omega
        subst hq0
        obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp.left
        have n1 := hp.next ch1 (Nat.le_refl d) (by have := hp.small; omega)
        obtain ⟨m2, run2, ch2, w, r, e⟩ := const_ok (k := 0) n1 (by decide) (by omega)
        subst e
        refine ⟨m2, ?_, ch1.trans ch2, ?_⟩
        · simpa only [List.length_append, List.length_cons, List.length_nil, pc_add] using run1.trans run2
        · refine ValueAt.of_enc (by simp only [valueWords]; decide) r ?_
          simp only [Enc, strWeitW, List.take_zero, strN]
          exact ⟨Nat.zero_le _, rfl⟩
  · cases h


end Gabbro.Stage0.Senke
