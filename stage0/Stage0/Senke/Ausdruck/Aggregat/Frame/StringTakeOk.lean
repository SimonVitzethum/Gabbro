/- Subject: Generic correctness of narrowing a string of capacity at least two to a smaller maximum. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeOka
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeCode
public import Stage0.Senke.Ausdruck.Aggregat.StringOps
public import Stage0.Senke.Ausdruck.Tops.Eng
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

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
