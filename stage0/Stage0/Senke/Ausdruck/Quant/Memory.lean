/- Generic physical pointer span transport on the actual IR machine. -/
module
public import Stage0.Senke.Ausdruck.Sim
public import Stage0.Senke.Ausdruck.Quant.Literal
public import Stage0.Senke.Ausdruck.Quant.TransportCode
public import Stage0.Senke.Ausdruck.Aggregat.Footprint
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
/-- A real indirect-load instruction, with no source-environment assumptions. -/
theorem span_load_step [Kern] {m : Runner.Mem} {pc fp a w : Runner.W} {K dst ptr : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (hd : dst < K) (hp : ptr < K)
    (code : CodeAt m pc [ci 15 dst ptr 0])
    (address : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a)
    (input : m.rd64 a = some w) :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩
      (write m (slot fp (BitVec.ofNat 64 dst)) 8 w.toNat) := by
  have hi := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply Star.one
  apply run_step (t := ⟨pc, fp⟩) hi (by decide)
  simp only [op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 address (run_rd64 input ?_)
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 (wr64_some (frame.wr dst hd))

theorem absolute_slot (a i : Nat) :
    slot (BitVec.ofNat 64 a) (BitVec.ofNat 64 i) = BitVec.ofNat 64 (a + 8 * i) := by
  unfold slot
  change BitVec.ofNat 64 a + BitVec.ofNat 64 i * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  omega

theorem natural_slot (a : Runner.W) (i : Nat) :
    slot a (BitVec.ofNat 64 i) = BitVec.ofNat 64 (a.toNat + 8 * i) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using absolute_slot a.toNat i

/-- The pointer arithmetic is ordinary checked IR addition; no host address is used. -/
theorem span_add_step [Kern] {m : Runner.Mem} {pc fp a b : Runner.W} {K dst ptr : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (hd : dst < K) (hp : ptr < K)
    (code : CodeAt m pc [ci 3 dst ptr dst])
    (address : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a)
    (offset : m.rd64 (slot fp (BitVec.ofNat 64 dst)) = some b) :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ (write m (slot fp (BitVec.ofNat 64 dst)) 8 (a + b).toNat) := by
  have hi := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply Star.one
  apply run_step (t := ⟨pc, fp⟩) hi (by decide)
  simp only [op]
  apply run_bin hi
  · rw [sx_nat (by omega)]; exact address
  · rw [sx_nat (by omega)]; exact offset
  · rfl
  · rw [sx_nat (by omega)]; exact wr64_some (frame.wr dst hd)

/-- A frame word and an absolute word with separated natural extents are disjoint. -/
theorem frame_absolute_far {fp : Runner.W} {K i a : Nat} (frame : fp.toNat + 8 * K ≤ 2 ^ 64)
    (index : i < K) (bound : a + 8 ≤ 2 ^ 64)
    (sep : fp.toNat + 8 * i + 8 ≤ a ∨ a + 8 ≤ fp.toNat + 8 * i) :
    Far (slot fp (BitVec.ofNat 64 i)) 8 (BitVec.ofNat 64 a) 8 := by
  unfold Far
  rw [slot_toNat frame index]
  have ha : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
  rw [ha]
  omega

set_option maxHeartbeats 2000000 in
/-- Dynamic physical-span transport also supports forward-safe overlapping frame copies.
    The pointer is preserved; only the destination and one explicit scratch word change. -/
theorem loadPointerSpan_core_run [Kern] {fp : Runner.W} {K ptr tmp : Nat} (words : List Runner.W) :
    ∀ {m : Runner.Mem} {pc a : Runner.W} {dst offset : Nat},
    FrameOK m fp K → K < 2 ^ 31 → dst + words.length ≤ ptr → ptr < tmp → tmp < K →
    8 * (offset + words.length) < 2 ^ 31 →
    CodeAt m pc (loadPointerSpan words.length dst ptr tmp offset) →
    CodeFar pc (3 * words.length) fp K →
    m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a →
    (∀ m' i (hi : i < words.length), SpanEffect fp tmp (fp.toNat + 8 * dst) i m m' →
      m'.rd64 (slot a (BitVec.ofNat 64 (offset + i))) = some words[i]) →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * words.length), fp⟩ m' ∧
      SpanEffect fp tmp (fp.toNat + 8 * dst) words.length m m' ∧
      WordsAt m' fp dst words ∧ m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
  induction words with
  | nil =>
    intro m pc a dst offset frame small dest pt ht literal code far pointer reads
    exact ⟨m, by simpa using Star.refl _ m, SpanEffect.refl _ _ _ _ _,
      (by intro i hi; simp at hi), pointer⟩
  | cons w ws ih =>
    intro m pc a dst offset frame small dest pt ht literal code far pointer reads
    have hp : ptr < K := by omega
    have hd : dst < K := by simp at dest; omega
    let m1 := write m (slot fp (BitVec.ofNat 64 tmp)) 8 (BitVec.ofNat 64 (8 * offset)).toNat
    have a1 : Agree fp dst K m m1 := agree_write frame.room (by omega) ht _
    have e1 : SpanEffect fp tmp (fp.toNat + 8 * dst) 1 m m1 := SpanEffect.scratch frame ht _
    have s1 := quant_lit frame small ht (codeAt_left code)
      (show lit32 ((8 * offset : Nat) : Int) = true by
        simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega)
    have f1 := codeFar_right (n := 1) (k := 2 + 3 * ws.length)
      (by rw [show 1 + (2 + 3 * ws.length) = 3 * (w :: ws).length by simp; omega]; exact far)
    have f1' : CodeFar (pc + 16) (1 + (1 + 3 * ws.length)) fp K := by
      rw [show 1 + (1 + 3 * ws.length) = 2 + 3 * ws.length by omega]
      simpa using f1
    have c1 := (codeAt_right (a := [ci 1 tmp (8 * offset) 0]) code).agree a1 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using f1')
    have pointer1 : m1.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
      rw [natural_slot, e1.read (by have := frame.room; omega) (Or.inl (by omega)) (Or.inr (by simp at dest; omega))]
      simpa only [natural_slot] using pointer
    have offset1 : m1.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (BitVec.ofNat 64 (8 * offset)) :=
      (wr_slot frame ht _).2.1
    have s2 := span_add_step (frame.agree a1) small ht hp (codeAt_left c1) pointer1 offset1
    let m2 := write m1 (slot fp (BitVec.ofNat 64 tmp)) 8 (a + BitVec.ofNat 64 (8 * offset)).toNat
    have a2 : Agree fp dst K m1 m2 := agree_write frame.room (by omega) ht _
    have e2 : SpanEffect fp tmp (fp.toNat + 8 * dst) 1 m1 m2 := SpanEffect.scratch (frame.agree a1) ht _
    have f2 := codeFar_right (n := 2) (k := 1 + 3 * ws.length)
      (by rw [show 2 + (1 + 3 * ws.length) = 3 * (w :: ws).length by simp; omega]; exact far)
    have c2 := (codeAt_right (a := [ci 1 tmp (8 * offset) 0, ci 3 tmp ptr tmp]) code).agree (a1.trans a2)
      (by simpa [Nat.add_comm] using f2)
    have addressEq : a + BitVec.ofNat 64 (8 * offset) = BitVec.ofNat 64 (a.toNat + 8 * offset) := by
      simp [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have addr2 : m2.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (BitVec.ofNat 64 (a.toNat + 8 * offset)) := by
      have h : m2.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (a + BitVec.ofNat 64 (8 * offset)) :=
        (wr_slot (m := m1) (fp := fp) (K := K) (d := tmp) (frame.agree a1) ht _).2.1
      rwa [addressEq] at h
    have read2 : m2.rd64 (BitVec.ofNat 64 (a.toNat + 8 * offset)) = some w := by
      have scratchOnly : SpanEffect fp tmp (fp.toNat + 8 * dst) 0 m m2 :=
        (SpanEffect.scratch frame ht _).trans (SpanEffect.scratch (frame.agree a1) ht _)
      have h := reads m2 0 (by simp) scratchOnly
      change m2.rd64 (slot a (BitVec.ofNat 64 offset)) = some w at h
      simpa only [natural_slot] using h
    have s3 := span_load_step (frame.agree (a1.trans a2)) small hd ht (codeAt_left c2) addr2 read2
    let m3 := write m2 (slot fp (BitVec.ofNat 64 dst)) 8 w.toNat
    have e3 : SpanEffect fp tmp (fp.toNat + 8 * dst) 1 m2 m3 := by
      dsimp only [m3]
      rw [natural_slot]
      exact SpanEffect.store (fp := fp) (tmp := tmp)
        (m := m2) (address := fp.toNat + 8 * dst) (count := 1) (by decide)
        (by have := frame.room; omega) w
    have effect := e1.trans (e2.trans e3)
    have changed : Agree fp dst K m m3 := effect.agreeFrame (by omega) ht (by omega) (by have := frame.room; omega)
    have pointer3 : m3.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
      rw [natural_slot, effect.read (by have := frame.room; omega) (Or.inl (by omega)) (Or.inr (by simp at dest; omega))]
      simpa only [natural_slot] using pointer
    have tailReads : ∀ m' i (hi : i < ws.length),
        SpanEffect fp tmp (fp.toNat + 8 * (dst + 1)) i m3 m' →
        m'.rd64 (slot a (BitVec.ofNat 64 (offset + 1 + i))) = some ws[i] := by
      intro m' i hi tailEffect
      have wholePrefix : SpanEffect fp tmp (fp.toNat + 8 * dst) (i + 1) m m' :=
        (effect.widenCount (by omega)).trans (by simpa [Nat.mul_add, Nat.add_assoc] using tailEffect.tail)
      have h := reads m' (i + 1) (by simp; omega) wholePrefix
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have tf := codeFar_right (n := 3) (k := 3 * ws.length)
      (by simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using far)
    have tc : CodeAt m3 (pc + 48) (loadPointerSpan ws.length (dst + 1) ptr tmp (offset + 1)) := by
      have h := (codeAt_right (a := [ci 1 tmp (8 * offset) 0, ci 3 tmp ptr tmp, ci 15 dst tmp 0]) code).agree
        changed (by simpa using tf)
      simpa using h
    obtain ⟨m4, steps, tailEffect, output, pointer4⟩ := ih (frame.agree changed) small
      (by simp at dest; omega) pt ht (by simp at literal; omega) tc (by simpa using tf) pointer3 tailReads
    have allEffect : SpanEffect fp tmp (fp.toNat + 8 * dst) (w :: ws).length m m4 :=
      (effect.widenCount (by simp)).trans (by simpa [Nat.mul_add, Nat.add_assoc] using tailEffect.tail)
    refine ⟨m4, ?_, allEffect, ?_, pointer4⟩
    · have last := s3.trans (by simpa [m3, BitVec.add_assoc] using steps)
      have middle := s2.trans (by simpa [m2, BitVec.add_assoc] using last)
      have combined := s1.trans middle
      simpa [m1, m2, m3, BitVec.ofInt_natCast, Nat.mul_add, BitVec.ofNat_add,
        BitVec.add_assoc, BitVec.add_comm] using combined
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, natural_slot]
        rw [tailEffect.read (by have := frame.room; omega) (Or.inl (by simp at dest; omega)) (Or.inl (by omega))]
        simpa only [m3, natural_slot] using (wr_slot (frame.agree (a1.trans a2)) hd w).2.1
      | succ i => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using output i (by simp at hi; omega)

/-- Forward-safe physical transport is a specialization of the single prefix-stable loop. -/
theorem loadPointerSpan_run [Kern] {fp : Runner.W} {K ptr tmp : Nat} (words : List Runner.W) :
    ∀ {m : Runner.Mem} {pc a : Runner.W} {dst offset : Nat},
    FrameOK m fp K → K < 2 ^ 31 → dst + words.length ≤ ptr → ptr < tmp → tmp < K →
    8 * (offset + words.length) < 2 ^ 31 → a.toNat + 8 * (offset + words.length) ≤ 2 ^ 64 →
    (fp.toNat + 8 * dst ≤ a.toNat + 8 * offset ∨
      a.toNat + 8 * (offset + words.length) ≤ fp.toNat + 8 * dst) →
    (a.toNat + 8 * (offset + words.length) ≤ fp.toNat + 8 * tmp ∨
      fp.toNat + 8 * (tmp + 1) ≤ a.toNat + 8 * offset) →
    CodeAt m pc (loadPointerSpan words.length dst ptr tmp offset) →
    CodeFar pc (3 * words.length) fp K →
    m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a → WordsAt m a offset words →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * words.length), fp⟩ m' ∧
      SpanEffect fp tmp (fp.toNat + 8 * dst) words.length m m' ∧
      WordsAt m' fp dst words ∧ m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
  intro m pc a dst offset frame small dest pt ht literal bound forward scratch code far pointer input
  apply loadPointerSpan_core_run words frame small dest pt ht literal code far pointer
  intro m' i hi effect
  simp only [natural_slot]
  rw [effect.read (by omega) (by omega) (by omega)]
  simpa only [natural_slot] using input i hi

/-- A stable source world uses the same runtime-pointer execution core, with no
    new layout or physical-separation assumption on generic expression lowering. -/
theorem loadPointerSpan_stable_run [Kern] {fp : Runner.W} {K ptr tmp : Nat} (words : List Runner.W)
    {m : Runner.Mem} {pc a : Runner.W} {dst offset : Nat} {W : Runner.Mem → Prop}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (dest : dst + words.length ≤ ptr)
    (pt : ptr < tmp) (ht : tmp < K) (literal : 8 * (offset + words.length) < 2 ^ 31)
    (code : CodeAt m pc (loadPointerSpan words.length dst ptr tmp offset))
    (far : CodeFar pc (3 * words.length) fp K)
    (pointer : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a)
    (stable : WStab W fp K) (world : W m)
    (source : ∀ m', W m' → WordsAt m' a offset words) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * words.length), fp⟩ m' ∧
      SpanEffect fp tmp (fp.toNat + 8 * dst) words.length m m' ∧
      WordsAt m' fp dst words ∧ m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
  apply loadPointerSpan_core_run words frame small dest pt ht literal code far pointer
  intro m' i hi effect
  have changed : Agree fp dst K m m' := effect.agreeFrame (by omega) ht (by omega) (by omega)
  exact source m' (stable m m' world (changed.mono (Nat.zero_le _))) i hi

/-- Complete typed dynamic transport; the exact same encoding and recursive validity
    are used for frame selections, world columns and reference-based reads. -/
theorem loadPointerValue_run [Kern] {D : Deklaration} {L : Lay D}
    {m : Runner.Mem} {pc fp a : Runner.W} {K dst ptr tmp offset : Nat} {τ : Ty} {v : Wert D τ}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (dest : dst + valueWords τ ≤ ptr)
    (pt : ptr < tmp) (ht : tmp < K) (literal : 8 * (offset + valueWords τ) < 2 ^ 31)
    (bound : a.toNat + 8 * (offset + valueWords τ) ≤ 2 ^ 64)
    (forward : fp.toNat + 8 * dst ≤ a.toNat + 8 * offset ∨
      a.toNat + 8 * (offset + valueWords τ) ≤ fp.toNat + 8 * dst)
    (scratch : a.toNat + 8 * (offset + valueWords τ) ≤ fp.toNat + 8 * tmp ∨
      fp.toNat + 8 * (tmp + 1) ≤ a.toNat + 8 * offset)
    (code : CodeAt m pc (loadPointerSpan (valueWords τ) dst ptr tmp offset))
    (far : CodeFar pc (3 * valueWords τ) fp K)
    (pointer : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a)
    (input : ValueAt L m a offset τ v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * valueWords τ), fp⟩ m' ∧
      Agree fp dst K m m' ∧ SpanEffect fp tmp (fp.toNat + 8 * dst) (valueWords τ) m m' ∧
      ValueAt L m' fp dst τ v ∧ m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
  obtain ⟨m', steps, effect, output, pointer'⟩ := loadPointerSpan_run (encodeWords L τ v)
    frame small (by simpa only [encodeWords_length] using dest) pt ht
    (by simpa only [encodeWords_length] using literal) (by simpa only [encodeWords_length] using bound)
    (by simpa only [encodeWords_length] using forward) (by simpa only [encodeWords_length] using scratch)
    (by simpa only [encodeWords_length] using code) (by simpa only [encodeWords_length] using far) pointer input.2
  have effect' : SpanEffect fp tmp (fp.toNat + 8 * dst) (valueWords τ) m m' :=
    by simpa only [encodeWords_length] using effect
  exact ⟨m', by simpa only [encodeWords_length] using steps,
    effect'.agreeFrame (by omega) ht (by omega) (by have := frame.room; omega), effect', ⟨input.1, output⟩, pointer'⟩

/-- Typed stable-source specialization used by generic world expression lowering. -/
theorem loadPointerValue_stable_run [Kern] {D : Deklaration} {L : Lay D}
    {m : Runner.Mem} {pc fp a : Runner.W} {K dst ptr tmp offset : Nat} {τ : Ty} {v : Wert D τ}
    {W : Runner.Mem → Prop}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (dest : dst + valueWords τ ≤ ptr)
    (pt : ptr < tmp) (ht : tmp < K) (literal : 8 * (offset + valueWords τ) < 2 ^ 31)
    (code : CodeAt m pc (loadPointerSpan (valueWords τ) dst ptr tmp offset))
    (far : CodeFar pc (3 * valueWords τ) fp K)
    (pointer : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a)
    (stable : WStab W fp K) (world : W m) (source : ∀ m', W m' → ValueAt L m' a offset τ v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * valueWords τ), fp⟩ m' ∧
      Agree fp dst K m m' ∧ SpanEffect fp tmp (fp.toNat + 8 * dst) (valueWords τ) m m' ∧
      ValueAt L m' fp dst τ v ∧ m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
  obtain ⟨m', steps, effect, output, pointer'⟩ := loadPointerSpan_stable_run (encodeWords L τ v)
    frame small (by simpa only [encodeWords_length] using dest) pt ht
    (by simpa only [encodeWords_length] using literal)
    (by simpa only [encodeWords_length] using code) (by simpa only [encodeWords_length] using far)
    pointer stable world (fun m hm => (source m hm).2)
  have effect' : SpanEffect fp tmp (fp.toNat + 8 * dst) (valueWords τ) m m' :=
    by simpa only [encodeWords_length] using effect
  exact ⟨m', by simpa only [encodeWords_length] using steps,
    effect'.agreeFrame (by omega) ht (by omega) (by have := frame.room; omega), effect',
    ⟨(source m world).1, output⟩, pointer'⟩

end Gabbro.Stage0.Senke
