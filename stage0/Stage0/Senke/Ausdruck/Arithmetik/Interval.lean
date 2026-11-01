/- Shared scalar interval predicates for expression and statement lowering. -/
import Stage0.Senke.Ausdruck.Gleit.Wort

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
attribute [local irreducible] wordConstant
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- A binary instruction may read any two frame slots, including its destination. -/
theorem eng_bin_ok {m : Runner.Mem} {pc fp : Runner.W} {K d a b o reserved : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {va vb r : Runner.W}
    {g : Runner.W → Runner.W → Option Runner.W}
    (hp : Pre L m pc fp K d [ci o d a b] ρ W reserved) (hd : d < K) (ha : a < K) (hb : b < K)
    (ra : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some va)
    (rb : m.rd64 (slot fp (BitVec.ofNat 64 b)) = some vb)
    (hop : op o = bin g) (ho : o < 256) (hg : g va vb = some r) :
    Ok m pc fp K d [ci o d a b] (· = r) := by
  have := hp.small
  refine one_ok hp (by simpa [ci] using ho) hd rfl fun m' hw => ?_
  have hi := hp.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  simp only [ci]
  rw [hop]
  apply run_bin hi
  · simpa only [sx_nat (d := a) (by omega)] using ra
  · simpa only [sx_nat (d := b) (by omega)] using rb
  · exact hg
  · simpa only [sx_nat (d := d) (by omega)] using hw

theorem engTest_length (o d : Nat) (lo hi : Int) :
    (engTest o d lo hi).1.length =
      (if lit32 lo then 1 else 17) + (if lit32 hi then 1 else 17) + 3 := by
  simp only [engTest, List.length_append, List.length_cons, List.length_nil, wordConstant_length]
  omega

theorem engTest_top (o d : Nat) (lo hi : Int) :
    d + 2 < (engTest o d lo hi).2 ∧ (engTest o d lo hi).2 ≤ d + 4 := by
  have lower := wordConstant_top (d + 1) lo
  have upper := wordConstant_top (d + 2) hi
  simp only [engTest]
  omega

/-- The raw test preserves the input and computes the exact word predicate.
    Its actual top, rather than an assumed constant instruction size, bounds
    both materializers and the comparison temporaries. -/
theorem eng_test_ok {m : Runner.Mem} {pc fp : Runner.W} {K o d : Nat} {lo hi : Int}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {v : Runner.W}
    (hp : Pre L m pc fp K (d + 1) (engTest o d lo hi).1 ρ W reserved)
    (fit : (engTest o d lo hi).2 ≤ K)
    (opcode : op o = bin (fun x y => some (Runner.IR.bool (scalarCmp o x y)))) (byte : o < 256)
    (rv : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some v) :
    Ok m pc fp K (d + 1) (engTest o d lo hi).1
      (· = Runner.IR.bool (scalarCmp o v (BitVec.ofInt 64 lo) || scalarCmp o (BitVec.ofInt 64 hi) v)) := by
  have loFit : (wordConstant (d + 1) lo).2 ≤ K := Nat.le_trans (Nat.le_max_left _ _) fit
  have hiFit : (wordConstant (d + 2) hi).2 ≤ K := Nat.le_trans (Nat.le_max_right _ _) fit
  have hd := (engTest_top o d lo hi).1
  have hq : Pre L m pc fp K (d + 1)
      ((wordConstant (d + 1) lo).1 ++ ([ci o (d + 1) d (d + 1)] ++
      ((wordConstant (d + 2) hi).1 ++ ([ci o (d + 2) (d + 2) d] ++ [ci 9 (d + 1) (d + 1) (d + 2)]))))
      ρ W reserved := by simpa only [engTest, List.append_assoc, List.cons_append, List.nil_append] using hp
  obtain ⟨m1, s1, a1, w1, r1, rfl⟩ := wordConstant_ok loFit hq.left
  have h1 := hq.next a1 (Nat.le_refl _) (by omega)
  have rv1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some v := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]; exact rv
  obtain ⟨m2, s2, a2, w2, r2, rfl⟩ := eng_bin_ok (d := d + 1) (a := d) (b := d + 1)
    h1.left (by omega) (by omega) (by omega) rv1 r1 opcode byte rfl
  have h2 := h1.next a2 (Nat.le_refl _) (by omega)
  obtain ⟨m3, s3, a3, w3, r3, rfl⟩ := wordConstant_ok hiFit
    { h2.left with ctx := by have := hp.ctx; omega }
  have h3 := h2.next (a3.mono (by omega : d + 1 ≤ d + 2)) (Nat.le_refl _) (by omega)
  have rv3 : m3.rd64 (slot fp (BitVec.ofNat 64 d)) = some v := by
    rw [agree_rd_low (a1.trans a2 |>.trans (a3.mono (by omega))) hp.frame.room (by omega) (by omega)]
    exact rv
  obtain ⟨m4, s4, a4, w4, r4, rfl⟩ := eng_bin_ok (d := d + 2) (a := d + 2) (b := d)
    { h3.left with ctx := by have := hp.ctx; omega }
    (by omega) (by omega) (by omega) r3 rv3 opcode byte rfl
  have h4 := h3.next (a4.mono (by omega : d + 1 ≤ d + 2)) (Nat.le_refl _) (by omega)
  have r24 : m4.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) =
      some (Runner.IR.bool (scalarCmp o v (BitVec.ofInt 64 lo))) := by
    rw [agree_rd_low (a3.trans a4) h2.frame.room (by omega) (by omega)]; exact r2
  obtain ⟨m5, s5, a5, w5, r5, rfl⟩ := eng_bin_ok (d := d + 1) (a := d + 1) (b := d + 2)
    h4 (by omega) (by omega) (by omega) r24 r4
    (g := fun x y => some (x ||| y)) rfl (by decide) rfl
  refine ⟨m5, ?_, a1.trans (a2.trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans a5))), _, r5, ?_⟩
  · simpa only [engTest, List.length_append, List.length_cons, List.length_nil, List.length_singleton,
      pc_add, Nat.reduceAdd, Nat.add_assoc] using s1.trans (s2.trans (s3.trans (s4.trans s5)))
  · simp only [bool_word]; exact or_word _ _

/-- Intersecting with the input's known range preserves the source test exactly. -/
theorem interval_clip_iff {lo hi lo' hi' x : Int} (hx0 : lo ≤ x) (hx1 : x ≤ hi) :
    (max lo lo' ≤ x ∧ x ≤ min hi hi') ↔ (lo' ≤ x ∧ x ≤ hi') := by omega

theorem intervalTestL_top {d top : Nat} {lo hi lo' hi' : Int} {code : List II}
    (lower : intervalTestL d lo hi lo' hi' = some (code, top)) :
    d + 1 < top ∧ top ≤ d + 4 := by
  unfold intervalTestL at lower
  split at lower
  · split at lower
    · cases lower; omega
    · obtain ⟨o, _, lower⟩ := Option.bind_eq_some_iff.mp lower
      cases Option.some.inj lower
      have bounds := engTest_top o d (max lo lo') (min hi hi')
      simp only [engTest] at bounds
      omega
  · cases lower

/-- The common generated predicate compares complete scalar values and returns
    the canonical outside flag. The static disjoint case still runs after the
    caller's input code; no child evaluation is erased or duplicated here. -/
theorem interval_test_ok {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat}
    {lo hi lo' hi' x : Int} {code : List II} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : intervalTestL d lo hi lo' hi' = some (code, top)) (fit : top ≤ K)
    (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (hp : Pre L m pc fp K (d + 1) code ρ W reserved)
    (rv : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 x)) :
    Ok m pc fp K (d + 1) code (· = Runner.IR.bool (decide (¬ (lo' ≤ x ∧ x ≤ hi')))) := by
  unfold intervalTestL at lower
  split at lower
  · split at lower
    · next disjoint =>
      cases lower
      have outside : ¬ (lo' ≤ x ∧ x ≤ hi') := by omega
      simpa [Runner.IR.bool, outside] using const_ok hp (by decide) (by omega)
    · next overlap =>
      obtain ⟨o, selected, lower⟩ := Option.bind_eq_some_iff.mp lower
      cases Option.some.inj lower
      have low0 : lo ≤ max lo lo' := by omega
      have low1 : max lo lo' ≤ hi := by omega
      have high0 : lo ≤ min hi hi' := by omega
      have high1 : min hi hi' ≤ hi := by omega
      obtain ⟨opcode, byte, below, _⟩ := scalarOrder_spec selected hx0 hx1 low0 low1
      obtain ⟨_, _, above, _⟩ := scalarOrder_spec selected high0 high1 hx0 hx1
      have flags : (scalarCmp o (BitVec.ofInt 64 x) (BitVec.ofInt 64 (max lo lo')) ||
          scalarCmp o (BitVec.ofInt 64 (min hi hi')) (BitVec.ofInt 64 x)) =
          decide (¬ (lo' ≤ x ∧ x ≤ hi')) := by
        rw [below, above]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
        omega
      exact (eng_test_ok hp fit opcode byte rv).mono (fun _ h => by simpa only [flags] using h)
  · cases lower

/-- Every pair of scalar domains has a generated interval predicate. -/
theorem intervalTestL_success (d : Nat) (lo hi lo' hi' : Int)
    (source : scalarFits lo hi = true) (target : scalarFits lo' hi' = true) :
    ∃ code top, intervalTestL d lo hi lo' hi' = some (code, top) := by
  unfold intervalTestL
  simp only [source, target, Bool.and_self, ↓reduceIte]
  split
  · exact ⟨_, _, rfl⟩
  · unfold scalarFits at source
    rcases Bool.or_eq_true_iff.mp source with signed | unsigned
    · simp only [scalarOrder, signed, Bool.and_self, ↓reduceIte]
      exact ⟨_, _, rfl⟩
    · by_cases signed : inW lo hi = true
      · simp only [scalarOrder, signed, Bool.and_self, ↓reduceIte]
        exact ⟨_, _, rfl⟩
      · simp only [scalarOrder, signed, unsigned, Bool.and_self, ↓reduceIte]
        exact ⟨_, _, rfl⟩

theorem intervalTestL_zeuge :
    (∃ code top, intervalTestL 4 0 18446744073709551615 (-3) 5 = some (code, top)) ∧
    (∃ code top, intervalTestL 4 (-100) (-1) 0 18446744073709551615 = some (code, top)) :=
  ⟨intervalTestL_success _ _ _ _ _ (by decide) (by decide),
   intervalTestL_success _ _ _ _ _ (by decide) (by decide)⟩

end Gabbro.Stage0.Senke

