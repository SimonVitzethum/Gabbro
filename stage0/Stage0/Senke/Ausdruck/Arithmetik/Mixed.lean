/- Mixed signed/unsigned scalar comparisons after single operand evaluation. -/
import Stage0.Senke.Ausdruck.Arithmetik.Interval

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem mixedCmpC_length (leftSigned equal : Bool) (d : Nat) :
    (mixedCmpC leftSigned equal d).length = if leftSigned && !equal then 4 else 6 := by
  cases leftSigned <;> cases equal <;> rfl

/-- Every pair of complete scalar domains is accepted once its children lower. -/
theorem scalarCompareL_success (equal : Bool) (d : Nat) (l1 h1 l2 h2 : Int)
    (a b : List II × Nat)
    (sx : scalarFits l1 h1 = true) (sy : scalarFits l2 h2 = true) :
    ∃ code top, scalarCompareL equal d l1 h1 l2 h2 (some a) (some b) = some (code, top) := by
  unfold scalarCompareL
  simp only [bind, Option.bind_some]
  cases scalarOrder l1 h1 l2 h2 <;> simp only [sx, sy, Bool.and_self, ↓reduceIte, pure]
  all_goals exact ⟨_, _, rfl⟩

/-- No common interpretation means exactly one operand needs a signed guard. -/
theorem mixedCmp_spec {l1 h1 l2 h2 x y : Int} (equal : Bool)
    (sx : scalarFits l1 h1 = true) (sy : scalarFits l2 h2 = true)
    (different : scalarOrder l1 h1 l2 h2 = none)
    (hx0 : l1 ≤ x) (hx1 : x ≤ h1) (hy0 : l2 ≤ y) (hy1 : y ≤ h2) :
    (if inW l1 h1 && !equal then
      (if inW l1 h1 then BitVec.ofInt 64 x else BitVec.ofInt 64 y).slt 0 ||
        (BitVec.ofInt 64 x).ult (BitVec.ofInt 64 y)
     else (!(if inW l1 h1 then BitVec.ofInt 64 x else BitVec.ofInt 64 y).slt 0) &&
       (if equal then BitVec.ofInt 64 x == BitVec.ofInt 64 y else
         (BitVec.ofInt 64 x).ult (BitVec.ofInt 64 y))) =
      (if equal then decide (x = y) else decide (x < y)) := by
  by_cases signed : inW l1 h1 = true
  · have other : inW l2 h2 = false := by
      by_cases h : inW l2 h2 = true
      · simp [scalarOrder, signed, h] at different
      · exact Bool.eq_false_iff.mpr h
    have unsigned : inU l2 h2 = true := by simpa [scalarFits, other] using sy
    have rx := inW_spec signed hx0 hx1
    have ry : 0 ≤ y ∧ y < 2 ^ 64 := by
      simp only [inU, Bool.and_eq_true, decide_eq_true_eq] at unsigned; omega
    have sign : (BitVec.ofInt 64 x).slt 0 = decide (x < 0) := slt_in (y := 0) rx (by constructor <;> decide)
    cases equal <;> simp only [signed, Bool.true_and, Bool.not_false, Bool.not_true, ↓reduceIte, sign]
    · exact mixed_left_lt rx ry
    · exact mixed_left_eq rx ry
  · have leftUnsigned : inU l1 h1 = true := by simpa [scalarFits, signed] using sx
    have rightSigned : inW l2 h2 = true := by
      by_cases h : inW l2 h2 = true
      · exact h
      · have rightUnsigned : inU l2 h2 = true := by simpa [scalarFits, h] using sy
        simp [scalarOrder, signed, leftUnsigned, rightUnsigned] at different
    have rx : 0 ≤ x ∧ x < 2 ^ 64 := by
      simp only [inU, Bool.and_eq_true, decide_eq_true_eq] at leftUnsigned; omega
    have ry := inW_spec rightSigned hy0 hy1
    have sign : (BitVec.ofInt 64 y).slt 0 = decide (y < 0) := slt_in (y := 0) ry (by constructor <;> decide)
    cases equal <;> simp only [Bool.eq_false_iff.mpr signed, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, sign]
    · exact mixed_right_lt rx ry
    · exact mixed_right_eq rx ry

/-- The sign is tested before either operand is overwritten. The guard prevents
    negative signed integers from aliasing high unsigned integers. -/
theorem mixedCmpC_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {va vb : Runner.W}
    (leftSigned equal : Bool)
    (hp : Pre L m pc fp K d (mixedCmpC leftSigned equal d) ρ W reserved)
    (fit : d + 5 ≤ K)
    (ra : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some va)
    (rb : m.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) = some vb) :
    Ok m pc fp K d (mixedCmpC leftSigned equal d)
      (· = Runner.IR.bool (if leftSigned && !equal then
        (if leftSigned then va else vb).slt 0 || va.ult vb
        else (!(if leftSigned then va else vb).slt 0) && (if equal then va == vb else va.ult vb))) := by
  let tail := if leftSigned && !equal then [ci 9 d (d + 2) (d + 3)]
    else [ci 1 (d + 4) 1 0, ci 10 (d + 4) (d + 2) (d + 4), ci 8 d (d + 3) (d + 4)]
  have hq : Pre L m pc fp K d ([ci 1 (d + 2) 0 0] ++
      ([ci 13 (d + 2) ((if leftSigned then d else d + 1) : Nat) (d + 2)] ++
      ([ci (if equal then 14 else 27) (d + 3) d (d + 1)] ++ tail))) ρ W reserved := by
    simpa only [mixedCmpC, tail, List.cons_append, List.nil_append] using hp
  obtain ⟨m1, s1, a1, w1, r1, rfl⟩ := const_ok (d := d + 2)
    { hq.left with ctx := by have := hp.ctx; omega } (by decide) (by omega)
  have h1 := hq.next (a1.mono (by omega : d ≤ d + 2)) (Nat.le_refl _) (by omega)
  have ra1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some va := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]; exact ra
  have rb1 : m1.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) = some vb := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]; exact rb
  have rs1 : m1.rd64 (slot fp (BitVec.ofNat 64 (if leftSigned then d else d + 1))) =
      some (if leftSigned then va else vb) := by cases leftSigned <;> assumption
  obtain ⟨m2, s2, a2, w2, r2, rfl⟩ := eng_bin_ok (d := d + 2) (a := if leftSigned then d else d + 1) (b := d + 2) (o := 13)
    { h1.left with ctx := by have := hp.ctx; omega }
    (by omega) (by cases leftSigned <;> simp <;> omega) (by omega) rs1 r1
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) rfl
  have h2 := h1.next (a2.mono (by omega : d ≤ d + 2)) (Nat.le_refl _) (by omega)
  have ra2 : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some va := by
    rw [agree_rd_low a2 hp.frame.room (by omega) (by omega)]; exact ra1
  have rb2 : m2.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) = some vb := by
    rw [agree_rd_low a2 hp.frame.room (by omega) (by omega)]; exact rb1
  obtain ⟨m3, s3, a3, w3, r3, rfl⟩ := eng_bin_ok (d := d + 3) (a := d) (b := d + 1) (o := if equal then 14 else 27) { h2.left with ctx := by have := hp.ctx; omega }
    (by omega) (by omega) (by omega) ra2 rb2
    (g := fun a b => some (Runner.IR.bool (if equal then a == b else a.ult b)))
    (by cases equal <;> rfl) (by cases equal <;> decide) rfl
  have h3 := h2.next (a3.mono (by omega : d ≤ d + 3)) (Nat.le_refl _) (by omega)
  have r23 : m3.rd64 (slot fp (BitVec.ofNat 64 (d + 2))) =
      some (Runner.IR.bool ((if leftSigned then va else vb).slt 0)) := by
    rw [agree_rd_low a3 hp.frame.room (by omega) (by omega)]; exact r2
  have changed := (a1.mono (by omega : d ≤ d + 2)).trans
    ((a2.mono (by omega : d ≤ d + 2)).trans (a3.mono (by omega : d ≤ d + 3)))
  by_cases short : (leftSigned && !equal) = true
  · have tailCode : tail = [ci 9 d (d + 2) (d + 3)] := by simp [tail, short]
    rw [tailCode] at h3
    obtain ⟨out, run, agree, w, read, rfl⟩ := eng_bin_ok (d := d) (a := d + 2) (b := d + 3) (o := 9) h3
      (by omega) (by omega) (by omega) r23 r3
      (g := fun a b => some (a ||| b)) rfl (by decide) rfl
    refine ⟨out, ?_, changed.trans agree, _, read, ?_⟩
    · simpa only [mixedCmpC, short, ↓reduceIte, List.length_append, List.length_cons,
        List.length_nil, Bool.false_eq_true, pc_add, Nat.reduceAdd, Nat.add_assoc] using s1.trans (s2.trans (s3.trans run))
    · have signed : leftSigned = true := by cases leftSigned <;> simp_all
      have unequal : equal = false := by cases equal <;> simp_all
      simp only [signed, unequal, ↓reduceIte, bool_word]
      exact or_word _ _
  · have tailCode : tail = [ci 1 (d + 4) 1 0] ++
        ([ci 10 (d + 4) (d + 2) (d + 4)] ++ [ci 8 d (d + 3) (d + 4)]) := by
      simp [tail, short]
    rw [tailCode] at h3
    obtain ⟨m4, s4, a4, w4, r4, rfl⟩ := const_ok (d := d + 4)
      { h3.left with ctx := by have := hp.ctx; omega } (by decide) (by omega)
    have h4 := h3.next (a4.mono (by omega : d ≤ d + 4)) (Nat.le_refl _) (by omega)
    have r24 : m4.rd64 (slot fp (BitVec.ofNat 64 (d + 2))) =
        some (Runner.IR.bool ((if leftSigned then va else vb).slt 0)) := by
      rw [agree_rd_low a4 hp.frame.room (by omega) (by omega)]; exact r23
    obtain ⟨m5, s5, a5, w5, r5, rfl⟩ := eng_bin_ok (d := d + 4) (a := d + 2) (b := d + 4) (o := 10)
      { h4.left with ctx := by have := hp.ctx; omega }
      (by omega) (by omega) (by omega) r24 r4
      (g := fun a b => some (a ^^^ b)) rfl (by decide) rfl
    have h5 := h4.next (a5.mono (by omega : d ≤ d + 4)) (Nat.le_refl _) (by omega)
    have r35 : m5.rd64 (slot fp (BitVec.ofNat 64 (d + 3))) =
        some (Runner.IR.bool (if equal then va == vb else va.ult vb)) := by
      rw [agree_rd_low (a4.trans a5) hp.frame.room (by omega) (by omega)]; exact r3
    obtain ⟨out, run, agree, w, read, rfl⟩ := eng_bin_ok (d := d) (a := d + 3) (b := d + 4) (o := 8) h5
      (by omega) (by omega) (by omega) r35 r5
      (g := fun a b => some (a &&& b)) rfl (by decide) rfl
    refine ⟨out, ?_, changed.trans ((a4.mono (by omega)).trans ((a5.mono (by omega)).trans agree)), _, read, ?_⟩
    · simpa only [mixedCmpC, short, ↓reduceIte, List.length_append, List.length_cons,
        List.length_nil, Bool.false_eq_true, pc_add, Nat.reduceAdd, Nat.add_assoc] using s1.trans (s2.trans (s3.trans (s4.trans (s5.trans run))))
    · simp only [short, Bool.false_eq_true, ↓reduceIte, bool_word]
      simp only [not_word, and_word, Bool.and_comm]

/-- Both operand programs run once; the selected comparison preserves their
    complete scalar integer values, including mixed signed/unsigned domains. -/
theorem scalarCompareL_ok {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {l1 h1 l2 h2 x y : Int} {a b : Option (List II × Nat)} {code : List II}
    (equal : Bool)
    (hx0 : l1 ≤ x) (hx1 : x ≤ h1) (hy0 : l2 ≤ y) (hy1 : y ≤ h2)
    (rightTop : ∀ cb tb, b = some (cb, tb) → d + 1 < tb)
    (left : ∀ ca ta, a = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (· = BitVec.ofInt 64 x))
    (right : ∀ cb tb, b = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (· = BitVec.ofInt 64 y))
    (lower : scalarCompareL equal d l1 h1 l2 h2 a b = some (code, top))
    (fit : top ≤ K) (hp : Pre L m pc fp K d code ρ W reserved) :
    Ok m pc fp K d code (· = Runner.IR.bool (if equal then decide (x = y) else decide (x < y))) := by
  simp only [scalarCompareL, bind, Option.bind_eq_some_iff] at lower
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, lower⟩ := lower
  have bt := rightTop cb tb hb
  cases order : scalarOrder l1 h1 l2 h2 with
  | some o =>
    simp only [order, pure, Option.some.injEq, Prod.mk.injEq, bin2] at lower
    obtain ⟨rfl, rfl⟩ := lower
    obtain ⟨opcode, byte, less, same⟩ := scalarOrder_spec order hx0 hx1 hy0 hy1
    refine bin_ok (left ca ta ha (by omega)) (right cb tb hb (by omega))
      (g := fun u v => some (Runner.IR.bool (if equal then u == v else scalarCmp o u v)))
      (fun u v hu hv => ⟨_, rfl, by rw [hu, hv]; cases equal <;> simp only [↓reduceIte, less, same]⟩)
      (by cases equal with | false => exact opcode | true => rfl)
      (by cases equal with | false => exact byte | true => exact (by decide : 14 < 256)) (by omega) hp
  | none =>
    simp only [order] at lower
    split at lower
    · next domains =>
      simp only [Bool.and_eq_true] at domains
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at lower
      obtain ⟨rfl, rfl⟩ := lower
      have hq : Pre L m pc fp K d (ca ++ (cb ++ mixedCmpC (inW l1 h1) equal d)) ρ W reserved := by
        simpa only [List.append_assoc] using hp
      obtain ⟨m1, s1, a1, w1, r1, rfl⟩ := left ca ta ha (by omega) m pc hq.left
      have next1 := hq.next a1 (Nat.le_succ d) (by omega)
      obtain ⟨m2, s2, a2, w2, r2, rfl⟩ := right cb tb hb (by omega) m1 _ next1.left
      have next2 := next1.next a2 (Nat.le_refl _) (by omega)
      have r12 : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 x) := by
        rw [agree_rd_low a2 hp.frame.room (by omega) (by omega)]; exact r1
      obtain ⟨out, run, agree, w, read, value⟩ := mixedCmpC_ok (inW l1 h1) equal
        { next2 with ctx := hp.ctx } (by omega) r12 r2
      refine ⟨out, ?_, a1.trans ((a2.mono (by omega)).trans agree), w, read, ?_⟩
      · simpa only [List.length_append, pc_add] using s1.trans (s2.trans run)
      · rw [mixedCmp_spec equal domains.1 domains.2 order hx0 hx1 hy0 hy1] at value
        exact value
    · cases lower

end Gabbro.Stage0.Senke
