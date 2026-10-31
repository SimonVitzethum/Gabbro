/- Execution of the runtime-pointer store loop with an exact scratch/world footprint. -/
import Stage0.Senke.Welt.Spans.CellCode
import Stage0.Senke.Welt.Spans.SpanStore
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem storePointerSpan_run {fp : Runner.W} {K ptr tmp : Nat} (ws : List Runner.W)
    (layout : LayIn L) (frameWorld : fp.toNat + 8 * K ≤ L.lo) (small : K < 2 ^ 31)
    (pt : ptr < tmp) (ht : tmp < K) :
    ∀ {m : Runner.Mem} {pc a : Runner.W} {src offset : Nat},
    FrameOK m fp K → src + ws.length ≤ ptr → 8 * (offset + ws.length) < 2 ^ 31 →
    L.lo ≤ a.toNat + 8 * offset → a.toNat + 8 * (offset + ws.length) ≤ L.hi →
    CodeAt m pc (storePointerSpan ws.length src ptr tmp offset) → CodeFar pc (3 * ws.length) fp K →
    m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a → WordsAt m fp src ws →
    (∀ i, i < ws.length → all m.wr (BitVec.ofNat 64 (a.toNat + 8 * (offset + i))) 8 = true) →
    (∀ i, i < ws.length → all m.rd (BitVec.ofNat 64 (a.toNat + 8 * (offset + i))) 8 = true) →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * ws.length), fp⟩ m' ∧
      SpanEffect fp tmp (a.toNat + 8 * offset) ws.length m m' ∧
      WordsAt m' (BitVec.ofNat 64 (a.toNat + 8 * offset)) 0 ws ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
  induction ws with
  | nil =>
    intro m pc a src offset frame source literal lo hi code far pointer input wr rd
    exact ⟨m, by simpa using Star.refl _ m, SpanEffect.refl _ _ _ _ _, by intro i h; simp at h, pointer⟩
  | cons w ws ih =>
    intro m pc a src offset frame source literal lo hi code far pointer input wr rd
    have bound := layout.2.2
    have hord : L.lo ≤ L.hi := by omega
    have hroom := frame.room
    have hp : ptr < K := by omega
    have hs : src < K := by simp at source; omega
    let m1 := write m (slot fp (BitVec.ofNat 64 tmp)) 8 (BitVec.ofNat 64 (8 * offset)).toNat
    have a1 : Agree fp tmp K m m1 := agree_write frame.room (Nat.le_refl _) ht _
    have e1 : SpanEffect fp tmp (a.toNat + 8 * offset) (w :: ws).length m m1 := SpanEffect.scratch frame ht _
    have loSpan : L.lo ≤ a.toNat + 8 * offset := lo
    have hiSpan : a.toNat + 8 * offset + 8 * (w :: ws).length ≤ L.hi := by simp only [List.length_cons] at hi ⊢; omega
    have aw1 := e1.agreeW ht loSpan hiSpan
    have s1 := quant_lit frame small ht (codeAt_left code)
      (show lit32 ((8 * offset : Nat) : Int) = true by
        simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; simp at literal; constructor <;> omega)
    have f1 : CodeFar (pc + 16) (1 + (1 + 3 * ws.length)) fp K := by
      have eq : 3 * (w :: ws).length = 1 + (2 + 3 * ws.length) := by simp; omega
      rw [eq] at far
      have h := codeFar_right (n := 1) (k := 2 + 3 * ws.length) far
      rw [show 1 + (1 + 3 * ws.length) = 2 + 3 * ws.length by omega]
      simpa using h
    have c1 := (codeAt_right (a := [ci 1 tmp (8 * offset) 0]) code).agree a1
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using f1)
    have pointer1 : m1.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
      rw [agreeW_rd_low aw1 frameWorld hroom pt (by omega)]
      exact pointer
    have offset1 : m1.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (BitVec.ofNat 64 (8 * offset)) :=
      (wr_slot frame ht _).2.1
    have s2 := span_add_step (frame.agree a1) small ht hp (codeAt_left c1) pointer1 offset1
    let m2 := write m1 (slot fp (BitVec.ofNat 64 tmp)) 8 (a + BitVec.ofNat 64 (8 * offset)).toNat
    have a2 : Agree fp tmp K m1 m2 := agree_write frame.room (Nat.le_refl _) ht _
    have e12 : SpanEffect fp tmp (a.toNat + 8 * offset) (w :: ws).length m m2 :=
      e1.trans (SpanEffect.scratch (frame.agree a1) ht _)
    have aw12 := e12.agreeW ht loSpan hiSpan
    have f2 : CodeFar (pc + 32) (3 * ws.length + 1) fp K := by
      have eq : 3 * (w :: ws).length = 2 + (1 + 3 * ws.length) := by simp; omega
      rw [eq] at far
      have h := codeFar_right (n := 2) (k := 1 + 3 * ws.length) far
      rw [show 3 * ws.length + 1 = 1 + 3 * ws.length by omega]
      simpa using h
    have c2 := (codeAt_right (a := [ci 1 tmp (8 * offset) 0, ci 3 tmp ptr tmp]) code).agree (a1.trans a2)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using f2)
    have addressEq : a + BitVec.ofNat 64 (8 * offset) = BitVec.ofNat 64 (a.toNat + 8 * offset) := by
      simp [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have addr2 : m2.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (BitVec.ofNat 64 (a.toNat + 8 * offset)) := by
      have h : m2.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (a + BitVec.ofNat 64 (8 * offset)) :=
        (wr_slot (m := m1) (fp := fp) (K := K) (d := tmp) (frame.agree a1) ht _).2.1
      rwa [addressEq] at h
    have val : m2.rd64 (slot fp (BitVec.ofNat 64 src)) = some w := by
      rw [agreeW_rd_low aw12 frameWorld hroom (by omega) (by omega)]
      have h := input 0 (by simp)
      simpa using h
    have wr0 : all m2.wr (BitVec.ofNat 64 (a.toNat + 8 * offset)) 8 = true := by
      have h := wr 0 (by simp)
      rw [Nat.add_zero] at h
      rw [e12.wr]; exact h
    have rd0 : all m2.rd (BitVec.ofNat 64 (a.toNat + 8 * offset)) 8 = true := by
      have h := rd 0 (by simp)
      rw [Nat.add_zero] at h
      rw [e12.rd]; exact h
    have s3 := span_store_step small ht hs (codeAt_left c2) addr2 val (wr64_some wr0)
    let m3 := write m2 (BitVec.ofNat 64 (a.toNat + 8 * offset)) 8 w.toNat
    have e3 : SpanEffect fp tmp (a.toNat + 8 * offset) (w :: ws).length m2 m3 :=
      SpanEffect.store (by simp) (by simp only [List.length_cons] at hi ⊢; omega) _
    have effect := e12.trans e3
    have aw := effect.agreeW ht loSpan hiSpan
    have tailInput : WordsAt m3 fp (src + 1) ws := by
      intro i hi'
      rw [agreeW_rd_low aw frameWorld hroom (by simp at source; omega) (by omega)]
      have h := input (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have pointer3 : m3.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
      rw [agreeW_rd_low aw frameWorld hroom pt (by omega)]
      exact pointer
    have tf : CodeFar (pc + 48) (3 * ws.length) fp K := by
      have eq : 3 * (w :: ws).length = 3 + 3 * ws.length := by simp; omega
      rw [eq] at far
      simpa using codeFar_right (n := 3) (k := 3 * ws.length) far
    have tc : CodeAt m3 (pc + 48) (storePointerSpan ws.length (src + 1) ptr tmp (offset + 1)) := by
      have h := codeAt_agreeW aw frameWorld bound hord
        (codeAt_right (a := [ci 1 tmp (8 * offset) 0, ci 3 tmp ptr tmp, ci 16 tmp src 0]) code)
        (by simpa using tf)
      simpa using h
    obtain ⟨m4, steps, changed, output, pointer4⟩ := ih (effect.frame frame)
      (by simp at source; omega) (by simp at literal; omega) (by omega)
      (by simp only [List.length_cons] at hi; omega) tc tf pointer3 tailInput
      (fun i hi' => by
        have h := wr (i + 1) (by simp; omega)
        rw [show offset + (i + 1) = offset + 1 + i by omega] at h
        rw [effect.wr]; exact h)
      (fun i hi' => by
        have h := rd (i + 1) (by simp; omega)
        rw [show offset + (i + 1) = offset + 1 + i by omega] at h
        rw [effect.rd]; exact h)
    have chAdj : SpanEffect fp tmp (a.toNat + 8 * offset + 8) ws.length m3 m4 := by
      have e : a.toNat + 8 * offset + 8 = a.toNat + 8 * (offset + 1) := by omega
      rw [e]; exact changed
    refine ⟨m4, ?_, effect.trans (by simpa using chAdj.tail), ?_, pointer4⟩
    · have s2' : Star ⟨pc + 16, fp⟩ m1 ⟨pc + 32, fp⟩ m2 := by
        simpa [m2, BitVec.add_assoc] using s2
      have s3' : Star ⟨pc + 32, fp⟩ m2 ⟨pc + 48, fp⟩ m3 := by
        simpa [m3, BitVec.add_assoc] using s3
      have combined := s1.trans (s2'.trans (s3'.trans steps))
      simpa [m1, m2, m3, BitVec.ofInt_natCast, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc,
        BitVec.add_comm] using combined
    · intro i hi'
      simp only [Nat.zero_add, absolute_slot]
      cases i with
      | zero =>
        simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
        rw [chAdj.read (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
        exact rd64_write_same rd0
      | succ i =>
        have h := output i (by simp at hi'; omega)
        simp only [Nat.zero_add, absolute_slot] at h
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Complete typed value stored through a runtime physical address. The stored value keeps
    its recursive validity; only the scratch word and the exact address span change. -/
theorem storePointerValue_run {m : Runner.Mem} {pc fp a : Runner.W} {K src ptr tmp : Nat}
    {τ : Ty} {v : Wert D τ}
    (layout : LayIn L) (frameWorld : fp.toNat + 8 * K ≤ L.lo) (small : K < 2 ^ 31)
    (pt : ptr < tmp) (ht : tmp < K) (frame : FrameOK m fp K)
    (source : src + valueWords τ ≤ ptr) (literal : 8 * valueWords τ < 2 ^ 31)
    (lo : L.lo ≤ a.toNat) (hi : a.toNat + 8 * valueWords τ ≤ L.hi)
    (code : CodeAt m pc (storePointerSpan (valueWords τ) src ptr tmp 0))
    (far : CodeFar pc (3 * valueWords τ) fp K)
    (pointer : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a) (input : ValueAt L m fp src τ v)
    (wr : ∀ i, i < valueWords τ → all m.wr (BitVec.ofNat 64 (a.toNat + 8 * i)) 8 = true)
    (rd : ∀ i, i < valueWords τ → all m.rd (BitVec.ofNat 64 (a.toNat + 8 * i)) 8 = true) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (48 * valueWords τ), fp⟩ m' ∧
      SpanEffect fp tmp a.toNat (valueWords τ) m m' ∧
      StorageAt L m' a.toNat τ v ∧ m'.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
  obtain ⟨m', steps, effect, output, pointer'⟩ := storePointerSpan_run (encodeWords L τ v) layout
    frameWorld small pt ht (m := m) (pc := pc) (a := a) (src := src) (offset := 0) frame
    (by simpa only [encodeWords_length] using source)
    (by simpa only [encodeWords_length, Nat.zero_add] using literal) (by simpa using lo)
    (by simpa only [encodeWords_length, Nat.zero_add] using hi)
    (by simpa only [encodeWords_length] using code) (by simpa only [encodeWords_length] using far)
    pointer input.2
    (fun i h => by simpa only [Nat.zero_add] using wr i (by simpa only [encodeWords_length] using h))
    (fun i h => by simpa only [Nat.zero_add] using rd i (by simpa only [encodeWords_length] using h))
  refine ⟨m', by simpa only [encodeWords_length] using steps,
    by simpa only [encodeWords_length, Nat.mul_zero, Nat.add_zero] using effect, ⟨input.1, ?_⟩, pointer'⟩
  simpa only [Nat.mul_zero, Nat.add_zero] using output

end Gabbro.Stage0.Senke
