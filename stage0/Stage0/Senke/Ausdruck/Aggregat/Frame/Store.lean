/- Subject: Execution of the runtime-pointer store loop into a frame array with an exact footprint. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Storea
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Code
public import Stage0.Senke.Ausdruck.Quant.Memory
public import Stage0.Senke.Welt.Spans.SpanWrite
public import Stage0.Senke.Welt.Schreib
public import Stage0.Senke.Ausdruck.Tops.Eng
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Replace element `index` of a frame array by a complete value: the address arithmetic is the one of
    `selectFrameSpan_ok`, followed by the exact-footprint store loop. Everything below `base`, outside the
    target span and below the index word keeps its words; the target span holds the value's encoding. -/
theorem storeFrameWords_ok {m : Runner.Mem} {pc fp : Runner.W} {K base src ptr tmp index : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (words : List Runner.W)
    (fits : base + (index + 1) * words.length ≤ src) (source : src + words.length ≤ ptr)
    (pt : ptr < tmp) (ht : tmp < K) (literal : 8 * words.length < 2 ^ 31)
    (indexWord : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 index))
    (input : WordsAt m fp src words)
    (pre : Pre L m pc fp K ptr (storeFrameSpan (words.length) base src ptr tmp) ρ W reserved) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (4 + 3 * words.length)), fp⟩ m' ∧
      Agree fp base K m m' ∧
      WordsAt m' fp (base + index * words.length) words ∧
      ∀ s, s < ptr → (s < base + index * words.length ∨ base + (index + 1) * words.length ≤ s) →
        m'.rd64 (slot fp (BitVec.ofNat 64 s)) = m.rd64 (slot fp (BitVec.ofNat 64 s)) := by
  have fits' : (index + 1) * words.length = index * words.length + words.length := by rw [Nat.add_mul, Nat.one_mul]
  have sourceBound : base + index * words.length + words.length ≤ src := by omega
  have hp : Pre L m pc fp K ptr
      ([ci 1 tmp (8 * words.length) 0] ++ ([ci 5 ptr ptr tmp] ++
      ([ci 17 tmp base 0] ++ ([ci 3 ptr tmp ptr] ++ storePointerSpan (words.length) src ptr tmp 0)))) ρ W reserved := pre
  obtain ⟨m1, s1, a1, factor, r1, ef⟩ := const_ok
    { hp.left with ctx := by have := pre.ctx; omega }
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega) ht
  subst factor
  have a1' := a1.mono (by omega : ptr ≤ tmp)
  have p1 := hp.next a1' (Nat.le_refl _) (by omega)
  have index1 : m1.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 index) := by
    rw [agree_rd_low a1 pre.frame.room pt (by omega)]; exact indexWord
  obtain ⟨m2, s2, a2, offset, r2, eo⟩ := eng_bin_ok p1.left (by omega) (by omega) ht index1 r1
    (g := fun a b => some (a * b)) rfl (by decide) rfl
  subst offset
  have p2 := p1.next a2 (Nat.le_refl _) (by omega)
  have addressRun : Ok m2 (pc + 16 + 16) fp K tmp [ci 17 tmp base 0]
      (· = slot fp (BitVec.ofNat 64 base)) := by
    have p : Pre L m2 _ fp K tmp [ci 17 tmp base 0] ρ W reserved :=
      { p2.left with ctx := by have := pre.ctx; omega }
    refine one_ok p (by simp [ci]) ht rfl fun m' write => ?_
    have instruction := p.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at instruction
    simp only [ci, op]
    refine f2_run (t := ⟨_, fp⟩) instruction ?_
    simp only [ret1]
    refine f1_run (t := ⟨_, fp⟩) instruction ?_
    rw [sx_nat (by have := pre.small; omega), sx_nat (by have := pre.small; omega)]
    exact run_wr64 write
  obtain ⟨m3, s3, a3, address, r3, ea⟩ := addressRun
  subst address
  have p3 := p2.next (a3.mono (by omega : ptr ≤ tmp)) (Nat.le_refl _) (by omega)
  have offset3 : m3.rd64 (slot fp (BitVec.ofNat 64 ptr)) =
      some (BitVec.ofNat 64 index * BitVec.ofInt 64 (8 * words.length)) := by
    rw [agree_rd_low a3 p2.frame.room pt (by omega)]; exact r2
  obtain ⟨m4, s4, a4, selected, r4, es⟩ := eng_bin_ok p3.left (by omega) ht (by omega) r3 offset3
    (g := fun a b => some (a + b)) rfl (by decide) rfl
  subst selected
  have pointerEq : slot fp (BitVec.ofNat 64 base) +
      BitVec.ofNat 64 index * BitVec.ofInt 64 (8 * words.length) =
      BitVec.ofNat 64 (fp.toNat + 8 * (base + index * words.length)) := by
    rw [← natural_slot]
    simp only [BitVec.ofInt_natCast, slot, BitVec.ofNat_add,
      BitVec.ofNat_mul, BitVec.mul_assoc, BitVec.add_mul, BitVec.add_assoc]
    congr 2
    have eight : BitVec.ofInt 64 (8 * (words.length : Int)) = BitVec.ofNat 64 (words.length) * 8 := by
      have : (8 * (words.length : Int)) = ((8 * words.length : Nat) : Int) := by push_cast; rfl
      rw [this, BitVec.ofInt_natCast, BitVec.ofNat_mul, BitVec.mul_comm]; rfl
    rw [eight]
  rw [pointerEq] at r4
  have a14 : Agree fp ptr K m m4 := a1'.trans (a2.trans ((a3.mono (by omega : ptr ≤ tmp)).trans a4))
  have source' := WordsAt.agree_low input a14 pre.frame.room (by omega) (by omega)
  have next := p3.next a4 (Nat.le_refl _) (by omega : ptr ≤ K)
  have frame := pre.frame.agree a14
  obtain ⟨m5, s5, effect, output, pointer⟩ := storeFramePointerSpan_run (base := base + index * words.length)
    words (m := m4) (src := src) (offset := 0) frame
    pre.small (by omega) pt ht
    (by simp only [Nat.zero_add]; exact literal)
    (by simp only [Nat.add_zero]; omega)
    (by simpa only using next.code)
    (by simpa only [storePointerSpan_length] using next.far) r4 source'
  have effect' : SpanEffect fp tmp (fp.toNat + 8 * (base + index * words.length)) (words.length) m4 m5 := by
    have h := effect
    simpa only [Nat.add_zero] using h
  have agreeAll : Agree fp base K m m5 :=
    (a14.mono (by omega : base ≤ ptr)).trans
      ((effect'.agreeFrame (by omega) ht (Nat.le_refl _) (by omega)).mono (by omega))
  refine ⟨m5, ?_, agreeAll, by simpa only [Nat.add_zero] using output, ?_⟩
  · have steps := s1.trans (s2.trans (s3.trans (s4.trans s5)))
    rw [show 16 * (4 + 3 * words.length) = 16 * 4 + 48 * words.length by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc]
    simpa only [List.length_cons, List.length_nil, pc_add, Nat.reduceAdd, Nat.zero_add] using steps
  · intro s hs outside
    have hlt : s < K := by omega
    rw [natural_slot, effect'.read (by have := pre.frame.room; omega) (Or.inl (by omega))
      (by rcases outside with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)), ← natural_slot, agree_rd_low a14 pre.frame.room hs (by omega)]

theorem elementEncoding_get {n width : Nat} (f : Fin n → List Runner.W)
    (lengths : ∀ i, (f i).length = width) (j : Fin n) (k : Nat) (hk : k < width) :
    (elementEncoding n f)[j.val * width + k]? = (f j)[k]? := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [elementEncoding]
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      exact List.getElem?_append_left (by rw [lengths]; exact hk)
    | succ j =>
      have hl := lengths ⟨0, by omega⟩
      have idx : (Fin.succ j).val * width + k = (f ⟨0, by omega⟩).length + (j.val * width + k) := by
        rw [hl, Fin.val_succ, Nat.add_mul, Nat.one_mul]; omega
      rw [idx, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact ih (fun i => f i.succ) (fun i => lengths i.succ) j

/-- Replacing one element keeps every word outside its span and writes the new element's words into it. -/
theorem wordsAt_arrSet {m3 m4 : Runner.Mem} {fp : Runner.W} {d ptr n : Nat} {τ : Ty}
    (a : Wert D (.arr τ n)) (v : Wert D τ) (j : Fin n)
    (kept : WordsAt m3 fp d (encodeWords L (.arr τ n) a))
    (written : WordsAt m4 fp (d + j.val * words.length) words)
    (preserved : ∀ s, s < ptr → (s < d + j.val * words.length ∨ d + (j.val + 1) * words.length ≤ s) →
      m4.rd64 (slot fp (BitVec.ofNat 64 s)) = m3.rd64 (slot fp (BitVec.ofNat 64 s)))
    (fits : d + n * words.length ≤ ptr) :
    WordsAt m4 fp d (encodeWords L (.arr τ n) (arrSetW a j v)) := by
  have nonempty : n ≠ 0 := by have := j.isLt; omega
  have positive := valueWords_pos τ
  have lengths : ∀ i, (encodeWords L τ (a i)).length = words.length := fun i => encodeWords_length L τ _
  intro p hp
  simp only [encodeWords, if_neg nonempty] at hp kept ⊢
  have hlen : (elementEncoding n (fun i => encodeWords L τ (arrSetW a j v i))).length = n * words.length :=
    elementEncoding_length n _ _ (fun i => encodeWords_length L τ _)
  have pBound : p < n * words.length := by omega
  have split : ∃ q r, r < words.length ∧ p = q * words.length + r :=
    ⟨p / words.length, p % words.length, Nat.mod_lt _ positive, (Nat.div_add_mod' p _).symm⟩
  obtain ⟨q, r, hr, hp'⟩ := split
  have qLt : q < n := by
    rcases Nat.lt_or_ge q n with below | above
    · exact below
    · have := Nat.mul_le_mul_right (words.length) above
      omega
  have hget : ∀ (g : Fin n → List Runner.W) (hg : ∀ i, (g i).length = words.length)
      (hp : p < (elementEncoding n g).length),
      (elementEncoding n g)[p] = (g ⟨q, qLt⟩)[r]'(by rw [hg]; exact hr) := by
    intro g hg hp
    have e := elementEncoding_get g hg ⟨q, qLt⟩ r hr
    simp only [← hp'] at e
    rw [List.getElem?_eq_getElem hp] at e
    have inner : r < (g ⟨q, qLt⟩).length := by rw [hg]; exact hr
    rw [List.getElem?_eq_getElem inner] at e
    exact Option.some.inj e
  rw [hget _ (fun i => encodeWords_length L τ _) hp]
  by_cases same : q = j.val
  · have h := written r (by rw [encodeWords_length]; exact hr)
    have hjq : (⟨q, qLt⟩ : Fin n) = j := Fin.ext same
    have e : arrSetW a j v ⟨q, qLt⟩ = v := by simp only [arrSetW]; exact if_pos hjq
    have ep : d + p = d + j.val * words.length + r := by rw [hp', same, Nat.add_assoc]
    simp only [e]
    rw [ep]
    exact h
  · have hne : (⟨q, qLt⟩ : Fin n) ≠ j := fun h => same (congrArg Fin.val h)
    simp only [arrSetW, if_neg hne]
    have outside : p < j.val * words.length ∨ (j.val + 1) * words.length ≤ p := by
      rcases Nat.lt_or_gt_of_ne same with lt | gt
      · left
        have := Nat.mul_le_mul_right (words.length) (Nat.succ_le_of_lt lt)
        rw [Nat.succ_mul] at this
        omega
      · right
        exact Nat.le_trans (Nat.mul_le_mul_right (words.length) (Nat.succ_le_of_lt gt)) (by omega)
    rw [show d + p = d + p by rfl, preserved (d + p) (by omega)
      (by rcases outside with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega))]
    have hlenA : (elementEncoding n (fun i => encodeWords L τ (a i))).length = n * words.length :=
      elementEncoding_length n _ _ lengths
    have hk := kept p (by omega)
    rw [hk, hget (fun i => encodeWords L τ (a i)) lengths (by omega)]

end Gabbro.Stage0.Senke

/-- Typed specialization of the shared arbitrary-word frame store. -/
theorem storeFrameSpan_ok {m : Runner.Mem} {pc fp : Runner.W} {K base src ptr tmp index : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {τ : Ty} {v : Wert D τ}
    (fits : base + (index + 1) * valueWords τ ≤ src) (source : src + valueWords τ ≤ ptr)
    (pt : ptr < tmp) (ht : tmp < K) (literal : 8 * valueWords τ < 2 ^ 31)
    (indexWord : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 index))
    (input : ValueAt L m fp src τ v)
    (pre : Pre L m pc fp K ptr (storeFrameSpan (valueWords τ) base src ptr tmp) ρ W reserved) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (4 + 3 * valueWords τ)), fp⟩ m' ∧
      Agree fp base K m m' ∧
      WordsAt m' fp (base + index * valueWords τ) (encodeWords L τ v) ∧
      ∀ s, s < ptr → (s < base + index * valueWords τ ∨ base + (index + 1) * valueWords τ ≤ s) →
        m'.rd64 (slot fp (BitVec.ofNat 64 s)) = m.rd64 (slot fp (BitVec.ofNat 64 s)) := by
  simpa only [encodeWords_length] using storeFrameWords_ok (encodeWords L τ v)
    (by simpa only [encodeWords_length] using fits)
    (by simpa only [encodeWords_length] using source) pt ht
    (by simpa only [encodeWords_length] using literal) indexWord input.2
    (by simpa only [encodeWords_length] using pre)
