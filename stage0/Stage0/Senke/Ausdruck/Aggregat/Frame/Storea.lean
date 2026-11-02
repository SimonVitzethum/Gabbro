/- Subject: Execution of the runtime-pointer store loop into a frame array with an exact footprint. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Code
public import Stage0.Senke.Ausdruck.Quant.Memory
public import Stage0.Senke.Welt.Spans.SpanWrite
public import Stage0.Senke.Welt.Schreib
public import Stage0.Senke.Ausdruck.Tops.Eng
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
@[expose] public section


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


end Gabbro.Stage0.Senke
