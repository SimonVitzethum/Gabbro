/- Exact-footprint copying of the second string at a runtime byte offset. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Code
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Store
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {fp : Runner.W} {K : Nat}

@[simp] theorem stringAppendC_length (n base src len ptr index : Nat) :
    (stringAppendC n base src len ptr index).length = 9 * n := by
  induction n generalizing src index with
  | zero => rfl
  | succ n ih => simp only [stringAppendC, List.length_append, List.length_cons, List.length_nil,
      storeFrameSpan_length, ih]; omega

/-- Copy arbitrary byte words. The length header, operand spans and all destination
    words outside the copied interval remain unchanged. Only the pointer scratch is free. -/
theorem stringAppend_ok (words : List Runner.W) :
    ∀ {m : Runner.Mem} {pc : Runner.W} {base src lenSlot ptr index len : Nat},
      base + len + index + words.length ≤ lenSlot → lenSlot < src → src + words.length ≤ ptr →
      ptr + 2 ≤ K →
      m.rd64 (slot fp (BitVec.ofNat 64 lenSlot)) = some (BitVec.ofNat 64 len) →
      WordsAt m fp src words →
      Pre L m pc fp K base (stringAppendC words.length base src lenSlot ptr index) ρ W reserved →
      ∃ m', Star ⟨pc, fp⟩ m
          ⟨pc + BitVec.ofNat 64 (16 * (stringAppendC words.length base src lenSlot ptr index).length), fp⟩ m' ∧
        Agree fp base K m m' ∧ WordsAt m' fp (base + len + index) words ∧
        ∀ s, s < ptr → (s < base + len + index ∨ base + len + index + words.length ≤ s) →
          m'.rd64 (slot fp (BitVec.ofNat 64 s)) = m.rd64 (slot fp (BitVec.ofNat 64 s)) := by
  induction words with
  | nil =>
    intro m pc base src lenSlot ptr index len _ _ _ _ _ _ pre
    exact ⟨m, by simpa [stringAppendC] using Star.refl ⟨pc, fp⟩ m,
      Agree.refl _ _ _ _, by intro i hi; simp at hi, by intros; rfl⟩
  | cons w ws ih =>
    intro m pc base src lenSlot ptr index len destEnd lenSrc srcEnd frameEnd lenRead input pre
    have small := pre.small
    have room := pre.frame.room
    have p : Pre L m pc fp K base
        ([ci 1 ptr index 0] ++ ([ci 3 ptr lenSlot ptr] ++
          (storeFrameSpan 1 base src ptr (ptr + 1) ++
            stringAppendC ws.length base (src + 1) lenSlot ptr (index + 1)))) ρ W reserved := pre
    obtain ⟨m1, s1, ch1, v1, rd1, eq1⟩ := const_ok
      ({ p.left with ctx := by have := pre.ctx; omega } : Pre L m pc fp K ptr _ ρ W reserved)
      (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; simp at destEnd; omega) (by omega)
    subst v1
    have p1 := p.next (ch1.mono (by omega : base ≤ ptr)) (Nat.le_refl _) (by omega)
    have len1 : m1.rd64 (slot fp (BitVec.ofNat 64 lenSlot)) = some (BitVec.ofNat 64 len) := by
      rw [agree_rd_low ch1 room (by simp at srcEnd; omega) (by omega)]; exact lenRead
    obtain ⟨m2, s2, ch2, v2, rd2, eq2⟩ := eng_bin_ok
      ({ p1.left with ctx := by have := pre.ctx; omega } : Pre L m1 _ fp K ptr _ ρ W reserved)
      (by omega) (by simp at srcEnd; omega) (by omega) len1 rd1
      (g := fun a b => some (a + b)) rfl (by decide) rfl
    subst v2
    have index2 : m2.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 (len + index)) := by
      simpa only [BitVec.ofInt_natCast, ← BitVec.ofNat_add] using rd2
    have ch12 := ch1.trans ch2
    have p2 := p1.next (ch2.mono (by omega : base ≤ ptr)) (Nat.le_refl _) (by omega)
    have source2 : WordsAt m2 fp src [w] := by
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      rw [Nat.add_zero, agree_rd_low ch12 room (by simp at srcEnd; omega) (by omega)]
      exact input 0 (by simp)
    obtain ⟨m3, s3, ch3, written, kept⟩ := storeFrameWords_ok (L := L) [w]
      (by simp at destEnd; simp; omega) (by simp at srcEnd; simp; omega) (by omega) (by omega)
      (by change 8 < 2 ^ 31; decide) index2 source2
      ({ p2.left with ctx := by have := pre.ctx; omega } : Pre L m2 _ fp K ptr _ ρ W reserved)
    have p3 := p2.next ch3 (Nat.le_refl _) (by omega)
    have keptAll : ∀ s, s < ptr → (s < base + len + index ∨ base + len + index + 1 ≤ s) →
        m3.rd64 (slot fp (BitVec.ofNat 64 s)) = m.rd64 (slot fp (BitVec.ofNat 64 s)) := by
      intro s hs outside
      rw [kept s hs (by simp only [List.length_singleton, Nat.mul_one]; omega),
        agree_rd_low ch12 room hs (by omega)]
    have len3 : m3.rd64 (slot fp (BitVec.ofNat 64 lenSlot)) = some (BitVec.ofNat 64 len) := by
      rw [keptAll lenSlot (by simp at srcEnd; omega) (Or.inr (by simp at destEnd; omega))]
      exact lenRead
    have source3 : WordsAt m3 fp (src + 1) ws := by
      intro j hj
      rw [keptAll (src + 1 + j) (by simp at srcEnd; omega) (Or.inr (by simp at destEnd; omega)),
        show src + 1 + j = src + (j + 1) by omega]
      exact input (j + 1) (by simp only [List.length_cons]; omega)
    obtain ⟨m4, s4, ch4, out, preserved⟩ := ih (by simp at destEnd; omega) (by omega)
      (by simp at srcEnd; omega) frameEnd len3 source3 p3
    refine ⟨m4, ?_, (ch12.mono (by omega)).trans (ch3.trans ch4), ?_, ?_⟩
    · have steps := s1.trans (s2.trans (s3.trans s4))
      simp only [stringAppendC_length, storeFrameSpan_length, List.length_cons,
        List.length_nil, Nat.reduceAdd, Nat.reduceMul] at steps
      rw [pc_add pc 1 1, pc_add pc (1 + 1) 7,
        pc_add pc (1 + 1 + 7) (9 * ws.length)] at steps
      rw [show 1 + 1 + 7 + 9 * ws.length = 9 * (ws.length + 1) by omega] at steps
      simpa only [stringAppendC_length, List.length_cons] using steps
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.add_zero, preserved (base + len + index) (by simp at srcEnd destEnd; omega) (Or.inl (by omega))]
        have h := written 0 (by simp)
        simpa only [List.length_singleton, List.getElem_cons_zero,
          Nat.mul_one, Nat.add_zero, Nat.add_assoc] using h
      | succ j =>
        have bound : j < ws.length := by simp only [List.length_cons] at hj; omega
        change m4.rd64 (slot fp (BitVec.ofNat 64 (base + len + index + (j + 1)))) = some ws[j]
        rw [show base + len + index + (j + 1) = base + len + (index + 1) + j by omega]
        exact out j bound
    · intro s hs outside
      rw [preserved s hs (by simp at outside; omega), keptAll s hs (by simp at outside; omega)]

end Gabbro.Stage0.Senke
