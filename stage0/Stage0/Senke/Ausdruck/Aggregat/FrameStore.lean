/- Subject: Execution of the runtime-pointer store loop into a frame array with an exact footprint. -/
import Stage0.Senke.Ausdruck.Aggregat.FrameCode
import Stage0.Senke.Ausdruck.Quant.Memory
import Stage0.Senke.Welt.Spans.SpanWrite
import Stage0.Senke.Welt.Schreib
import Stage0.Senke.Ausdruck.Eng
import Stage0.Senke.Ausdruck.Aggregat.Scalar

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

set_option maxHeartbeats 2000000 in
/-- The words `ws` at slots `src ..` are stored through the address word in `ptr` (the address of frame slot
    `base`) into the slots `base + offset ..`, which lie below the source. Only the scratch word and the exact
    target span change; the pointer and the source words are preserved. -/
theorem storeFramePointerSpan_run [Kern] {fp : Runner.W} {K ptr tmp base : Nat} (ws : List Runner.W) :
    ∀ {m : Runner.Mem} {pc : Runner.W} {src offset : Nat},
    FrameOK m fp K → K < 2 ^ 31 → src + ws.length ≤ ptr → ptr < tmp → tmp < K →
    8 * (offset + ws.length) < 2 ^ 31 → base + offset + ws.length ≤ src →
    CodeAt m pc (storePointerSpan ws.length src ptr tmp offset) →
    CodeFar pc (3 * ws.length) fp K →
    m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 (fp.toNat + 8 * base)) →
    WordsAt m fp src ws →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * ws.length), fp⟩ m' ∧
      SpanEffect fp tmp (fp.toNat + 8 * (base + offset)) ws.length m m' ∧
      WordsAt m' fp (base + offset) ws ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 (fp.toNat + 8 * base)) := by
  induction ws with
  | nil =>
    intro m pc src offset frame small source pt ht literal below code far pointer input
    exact ⟨m, by simpa using Star.refl _ m, SpanEffect.refl _ _ _ _ _, by intro i h; simp at h, pointer⟩
  | cons w ws ih =>
    intro m pc src offset frame small source pt ht literal below code far pointer input
    have hlen : (w :: ws).length = ws.length + 1 := rfl
    have hroom := frame.room
    have hp : ptr < K := by omega
    have hs : src < K := by omega
    have hb : base + offset < K := by omega
    let m1 := write m (slot fp (BitVec.ofNat 64 tmp)) 8 (BitVec.ofNat 64 (8 * offset)).toNat
    have a1 : Agree fp tmp K m m1 := agree_write frame.room (Nat.le_refl _) ht _
    have e1 : SpanEffect fp tmp (fp.toNat + 8 * (base + offset)) (w :: ws).length m m1 :=
      SpanEffect.scratch frame ht _
    have s1 := quant_lit frame small ht (codeAt_left code)
      (show lit32 ((8 * offset : Nat) : Int) = true by
        simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega)
    have f1 : CodeFar (pc + 16) (1 + (1 + 3 * ws.length)) fp K := by
      have eq : 3 * (w :: ws).length = 1 + (2 + 3 * ws.length) := by omega
      rw [eq] at far
      have h := codeFar_right (n := 1) (k := 2 + 3 * ws.length) far
      rw [show 1 + (1 + 3 * ws.length) = 2 + 3 * ws.length by omega]
      simpa using h
    have c1 := (codeAt_right (a := [ci 1 tmp (8 * offset) 0]) code).agree a1
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using f1)
    have pointer1 : m1.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 (fp.toNat + 8 * base)) := by
      rw [natural_slot, e1.read (by omega) (Or.inl (by omega)) (Or.inr (by omega))]
      simpa only [natural_slot] using pointer
    have offset1 : m1.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (BitVec.ofNat 64 (8 * offset)) :=
      (wr_slot frame ht _).2.1
    have s2 := span_add_step (frame.agree a1) small ht hp (codeAt_left c1) pointer1 offset1
    let m2 := write m1 (slot fp (BitVec.ofNat 64 tmp)) 8
      (BitVec.ofNat 64 (fp.toNat + 8 * base) + BitVec.ofNat 64 (8 * offset)).toNat
    have a2 : Agree fp tmp K m1 m2 := agree_write frame.room (Nat.le_refl _) ht _
    have e12 : SpanEffect fp tmp (fp.toNat + 8 * (base + offset)) (w :: ws).length m m2 :=
      e1.trans (SpanEffect.scratch (frame.agree a1) ht _)
    have f2 : CodeFar (pc + 32) (3 * ws.length + 1) fp K := by
      have eq : 3 * (w :: ws).length = 2 + (1 + 3 * ws.length) := by omega
      rw [eq] at far
      have h := codeFar_right (n := 2) (k := 1 + 3 * ws.length) far
      rw [show 3 * ws.length + 1 = 1 + 3 * ws.length by omega]
      simpa using h
    have c2 := (codeAt_right (a := [ci 1 tmp (8 * offset) 0, ci 3 tmp ptr tmp]) code).agree (a1.trans a2)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using f2)
    have addressEq : BitVec.ofNat 64 (fp.toNat + 8 * base) + BitVec.ofNat 64 (8 * offset) =
        BitVec.ofNat 64 (fp.toNat + 8 * (base + offset)) := by
      rw [← BitVec.ofNat_add]; congr 1; omega
    have addr2 : m2.rd64 (slot fp (BitVec.ofNat 64 tmp)) =
        some (BitVec.ofNat 64 (fp.toNat + 8 * (base + offset))) := by
      have h : m2.rd64 (slot fp (BitVec.ofNat 64 tmp)) =
          some (BitVec.ofNat 64 (fp.toNat + 8 * base) + BitVec.ofNat 64 (8 * offset)) :=
        (wr_slot (m := m1) (fp := fp) (K := K) (d := tmp) (frame.agree a1) ht _).2.1
      rwa [addressEq] at h
    have val : m2.rd64 (slot fp (BitVec.ofNat 64 src)) = some w := by
      rw [natural_slot, e12.read (by omega) (Or.inl (by omega)) (Or.inr (by omega))]
      have h := input 0 (by simp)
      simpa only [natural_slot, Nat.add_zero, List.getElem_cons_zero] using h
    have wr0 : all m2.wr (BitVec.ofNat 64 (fp.toNat + 8 * (base + offset))) 8 = true := by
      have h := frame.wr (base + offset) hb
      rw [natural_slot] at h
      rw [e12.wr]; exact h
    have rd0 : all m2.rd (BitVec.ofNat 64 (fp.toNat + 8 * (base + offset))) 8 = true := by
      have h := frame.rd (base + offset) hb
      rw [natural_slot] at h
      rw [e12.rd]; exact h
    have s3 := span_store_step small ht hs (codeAt_left c2) addr2 val (wr64_some wr0)
    let m3 := write m2 (BitVec.ofNat 64 (fp.toNat + 8 * (base + offset))) 8 w.toNat
    have e3 : SpanEffect fp tmp (fp.toNat + 8 * (base + offset)) (w :: ws).length m2 m3 :=
      SpanEffect.store (by simp) (by omega) _
    have effect := e12.trans e3
    have changed : Agree fp (base + offset) K m m3 := effect.agreeFrame (by omega) ht (by omega) (by omega)
    have tailInput : WordsAt m3 fp (src + 1) ws := by
      intro i hi'
      rw [show src + 1 + i = src + (i + 1) by omega, natural_slot,
        effect.read (by omega) (Or.inl (by omega)) (Or.inr (by omega))]
      have h := input (i + 1) (by simp; omega)
      rw [natural_slot] at h
      simpa using h
    have pointer3 : m3.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 (fp.toNat + 8 * base)) := by
      rw [natural_slot, effect.read (by omega) (Or.inl (by omega)) (Or.inr (by omega))]
      simpa only [natural_slot] using pointer
    have tf : CodeFar (pc + 48) (3 * ws.length) fp K := by
      have eq : 3 * (w :: ws).length = 3 + 3 * ws.length := by omega
      rw [eq] at far
      simpa using codeFar_right (n := 3) (k := 3 * ws.length) far
    have tc : CodeAt m3 (pc + 48) (storePointerSpan ws.length (src + 1) ptr tmp (offset + 1)) := by
      have h := (codeAt_right (a := [ci 1 tmp (8 * offset) 0, ci 3 tmp ptr tmp, ci 16 tmp src 0]) code).agree
        changed (by simpa using tf)
      simpa using h
    obtain ⟨m4, steps, tailEffect, output, pointer4⟩ := ih (effect.frame frame) small
      (by omega) pt ht (by omega) (by omega) tc tf pointer3 tailInput
    have chAdj : SpanEffect fp tmp (fp.toNat + 8 * (base + offset) + 8) ws.length m3 m4 := by
      have e : fp.toNat + 8 * (base + offset) + 8 = fp.toNat + 8 * (base + (offset + 1)) := by omega
      rw [e]; exact tailEffect
    refine ⟨m4, ?_, effect.trans (by simpa using chAdj.tail), ?_, ?_⟩
    · have s2' : Star ⟨pc + 16, fp⟩ m1 ⟨pc + 32, fp⟩ m2 := by
        simpa [m2, BitVec.add_assoc] using s2
      have s3' : Star ⟨pc + 32, fp⟩ m2 ⟨pc + 48, fp⟩ m3 := by
        simpa [m3, BitVec.add_assoc] using s3
      have combined := s1.trans (s2'.trans (s3'.trans steps))
      simpa [m1, m2, m3, BitVec.ofInt_natCast, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc,
        BitVec.add_comm] using combined
    · intro i hi'
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [natural_slot, chAdj.read (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
        exact rd64_write_same rd0
      | succ i =>
        have h := output i (by simp at hi'; omega)
        rw [show base + offset + (i + 1) = base + (offset + 1) + i by omega]
        simpa using h
    · exact pointer4

variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Replace element `index` of a frame array by a complete value: the address arithmetic is the one of
    `selectFrameSpan_ok`, followed by the exact-footprint store loop. Everything below `base`, outside the
    target span and below the index word keeps its words; the target span holds the value's encoding. -/
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
  have positive : 0 < valueWords τ := valueWords_pos τ
  have fits' : (index + 1) * valueWords τ = index * valueWords τ + valueWords τ := by rw [Nat.add_mul, Nat.one_mul]
  have sourceBound : base + index * valueWords τ + valueWords τ ≤ src := by omega
  have hp : Pre L m pc fp K ptr
      ([ci 1 tmp (8 * valueWords τ) 0] ++ ([ci 5 ptr ptr tmp] ++
      ([ci 17 tmp base 0] ++ ([ci 3 ptr tmp ptr] ++ storePointerSpan (valueWords τ) src ptr tmp 0)))) ρ W reserved := pre
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
      some (BitVec.ofNat 64 index * BitVec.ofInt 64 (8 * valueWords τ)) := by
    rw [agree_rd_low a3 p2.frame.room pt (by omega)]; exact r2
  obtain ⟨m4, s4, a4, selected, r4, es⟩ := eng_bin_ok p3.left (by omega) ht (by omega) r3 offset3
    (g := fun a b => some (a + b)) rfl (by decide) rfl
  subst selected
  have pointerEq : slot fp (BitVec.ofNat 64 base) +
      BitVec.ofNat 64 index * BitVec.ofInt 64 (8 * valueWords τ) =
      BitVec.ofNat 64 (fp.toNat + 8 * (base + index * valueWords τ)) := by
    rw [← natural_slot]
    simp only [BitVec.ofInt_natCast, slot, BitVec.ofNat_add,
      BitVec.ofNat_mul, BitVec.mul_assoc, BitVec.add_mul, BitVec.add_assoc]
    congr 2
    have eight : BitVec.ofInt 64 (8 * (valueWords τ : Int)) = BitVec.ofNat 64 (valueWords τ) * 8 := by
      have : (8 * (valueWords τ : Int)) = ((8 * valueWords τ : Nat) : Int) := by push_cast; rfl
      rw [this, BitVec.ofInt_natCast, BitVec.ofNat_mul, BitVec.mul_comm]; rfl
    rw [eight]
  rw [pointerEq] at r4
  have a14 : Agree fp ptr K m m4 := a1'.trans (a2.trans ((a3.mono (by omega : ptr ≤ tmp)).trans a4))
  have source' := input.agree a14 pre.frame (by omega) (by omega)
  have next := p3.next a4 (Nat.le_refl _) (by omega : ptr ≤ K)
  have frame := pre.frame.agree a14
  obtain ⟨m5, s5, effect, output, pointer⟩ := storeFramePointerSpan_run (base := base + index * valueWords τ)
    (encodeWords L τ v) (m := m4) (src := src) (offset := 0) frame
    pre.small (by simp only [encodeWords_length]; omega) pt ht
    (by simp only [encodeWords_length, Nat.zero_add]; exact literal)
    (by simp only [encodeWords_length, Nat.add_zero]; omega)
    (by simpa only [encodeWords_length] using next.code)
    (by simpa only [encodeWords_length, storePointerSpan_length] using next.far) r4 source'.2
  have effect' : SpanEffect fp tmp (fp.toNat + 8 * (base + index * valueWords τ)) (valueWords τ) m4 m5 := by
    have h := effect
    simpa only [encodeWords_length, Nat.add_zero] using h
  have agreeAll : Agree fp base K m m5 :=
    (a14.mono (by omega : base ≤ ptr)).trans
      ((effect'.agreeFrame (by omega) ht (Nat.le_refl _) (by omega)).mono (by omega))
  refine ⟨m5, ?_, agreeAll, by simpa only [Nat.add_zero] using output, ?_⟩
  · have steps := s1.trans (s2.trans (s3.trans (s4.trans s5)))
    rw [show 16 * (4 + 3 * valueWords τ) = 16 * 4 + 48 * valueWords τ by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc]
    simpa only [List.length_cons, List.length_nil, pc_add, Nat.reduceAdd, Nat.zero_add, encodeWords_length] using steps
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
    (written : WordsAt m4 fp (d + j.val * valueWords τ) (encodeWords L τ v))
    (preserved : ∀ s, s < ptr → (s < d + j.val * valueWords τ ∨ d + (j.val + 1) * valueWords τ ≤ s) →
      m4.rd64 (slot fp (BitVec.ofNat 64 s)) = m3.rd64 (slot fp (BitVec.ofNat 64 s)))
    (fits : d + n * valueWords τ ≤ ptr) :
    WordsAt m4 fp d (encodeWords L (.arr τ n) (arrSetW a j v)) := by
  have nonempty : n ≠ 0 := by have := j.isLt; omega
  have positive := valueWords_pos τ
  have lengths : ∀ i, (encodeWords L τ (a i)).length = valueWords τ := fun i => encodeWords_length L τ _
  intro p hp
  simp only [encodeWords, if_neg nonempty] at hp kept ⊢
  have hlen : (elementEncoding n (fun i => encodeWords L τ (arrSetW a j v i))).length = n * valueWords τ :=
    elementEncoding_length n _ _ (fun i => encodeWords_length L τ _)
  have pBound : p < n * valueWords τ := by omega
  have split : ∃ q r, r < valueWords τ ∧ p = q * valueWords τ + r :=
    ⟨p / valueWords τ, p % valueWords τ, Nat.mod_lt _ positive, (Nat.div_add_mod' p _).symm⟩
  obtain ⟨q, r, hr, hp'⟩ := split
  have qLt : q < n := by
    rcases Nat.lt_or_ge q n with below | above
    · exact below
    · have := Nat.mul_le_mul_right (valueWords τ) above
      omega
  have hget : ∀ (g : Fin n → List Runner.W) (hg : ∀ i, (g i).length = valueWords τ)
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
    have ep : d + p = d + j.val * valueWords τ + r := by rw [hp', same, Nat.add_assoc]
    simp only [e]
    rw [ep]
    exact h
  · have hne : (⟨q, qLt⟩ : Fin n) ≠ j := fun h => same (congrArg Fin.val h)
    simp only [arrSetW, if_neg hne]
    have outside : p < j.val * valueWords τ ∨ (j.val + 1) * valueWords τ ≤ p := by
      rcases Nat.lt_or_gt_of_ne same with lt | gt
      · left
        have := Nat.mul_le_mul_right (valueWords τ) (Nat.succ_le_of_lt lt)
        rw [Nat.succ_mul] at this
        omega
      · right
        exact Nat.le_trans (Nat.mul_le_mul_right (valueWords τ) (Nat.succ_le_of_lt gt)) (by omega)
    rw [show d + p = d + p by rfl, preserved (d + p) (by omega)
      (by rcases outside with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega))]
    have hlenA : (elementEncoding n (fun i => encodeWords L τ (a i))).length = n * valueWords τ :=
      elementEncoding_length n _ _ lengths
    have hk := kept p (by omega)
    rw [hk, hget (fun i => encodeWords L τ (a i)) lengths (by omega)]

end Gabbro.Stage0.Senke
