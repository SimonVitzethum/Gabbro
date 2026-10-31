/- Execution of the complete store loop with an exact scratch/world footprint. -/
import Stage0.Senke.Welt.Spans.SpanEffect
import Stage0.Senke.Welt.Schreib
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem storeSpan_run {fp : Runner.W} {K tmp : Nat} (ws : List Runner.W)
    (layout : LayIn L) (frameWorld : fp.toNat + 8 * K ≤ L.lo) (ht : tmp < K)
    (small : K < 2 ^ 31) :
    ∀ {m : Runner.Mem} {pc : Runner.W} {src address : Nat},
    FrameOK m fp K → src + ws.length ≤ tmp → L.lo ≤ address →
    address + 8 * ws.length ≤ L.hi →
    CodeAt m pc (storeSpan ws.length tmp src address) → CodeFar pc (2 * ws.length) fp K →
    WordsAt m fp src ws →
    (∀ i, i < ws.length → all m.wr (BitVec.ofNat 64 (address + 8 * i)) 8 = true) →
    (∀ i, i < ws.length → all m.rd (BitVec.ofNat 64 (address + 8 * i)) 8 = true) →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (32 * ws.length), fp⟩ m' ∧
      SpanEffect fp tmp address ws.length m m' ∧
      WordsAt m' (BitVec.ofNat 64 address) 0 ws := by
  induction ws with
  | nil =>
    intro m pc src address frame source lo hi code far input wr rd
    exact ⟨m, by simpa using Star.refl _ m, SpanEffect.refl _ _ _ _ _, by intro i h; simp at h⟩
  | cons w ws ih =>
    intro m pc src address frame source lo hi code far input wr rd
    have bound := layout.2.2
    have hord : L.lo ≤ L.hi := by omega
    let m1 := write m (slot fp (BitVec.ofNat 64 tmp)) 8 (BitVec.ofNat 64 address).toNat
    have e1 : SpanEffect fp tmp address (w :: ws).length m m1 := SpanEffect.scratch frame ht _
    have aw1 := e1.agreeW ht lo hi
    have s1 := quant_lit frame small ht (codeAt_left code)
      (show lit32 (address : Int) = true by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega)
    have f1 : CodeFar (pc + 16) (1 + 2 * ws.length) fp K := by
      have eq : 2 * (w :: ws).length = 1 + (1 + 2 * ws.length) := by simp; omega
      rw [eq] at far
      simpa using codeFar_right (n := 1) (k := 1 + 2 * ws.length) far
    have c1 := codeAt_agreeW aw1 frameWorld bound hord
      (codeAt_right (a := [ci 1 tmp address 0]) code) (by simpa [Nat.add_comm] using f1)
    have adr : m1.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some (BitVec.ofNat 64 address) :=
      (wr_slot frame ht _).2.1
    have val : m1.rd64 (slot fp (BitVec.ofNat 64 src)) = some w := by
      rw [agreeW_rd_low aw1 frameWorld frame.room (by simp at source; omega) (by omega)]
      exact input 0 (by simp)
    have wr0 : all m1.wr (BitVec.ofNat 64 address) 8 = true := by simpa [m1] using wr 0 (by simp)
    have s2 := span_store_step small ht (by simp at source; omega) (codeAt_left c1) adr val (wr64_some wr0)
    let m2 := write m1 (BitVec.ofNat 64 address) 8 w.toNat
    have e2 : SpanEffect fp tmp address (w :: ws).length m1 m2 :=
      SpanEffect.store (by simp) (by simp at hi; omega) _
    have effect := e1.trans e2
    have aw := effect.agreeW ht lo hi
    have tailInput : WordsAt m2 fp (src + 1) ws := by
      intro i hi'
      rw [agreeW_rd_low aw frameWorld frame.room (by simp at source; omega) (by omega)]
      have h := input (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have tf : CodeFar (pc + 32) (2 * ws.length) fp K := by
      have eq : 2 * (w :: ws).length = 2 + 2 * ws.length := by simp; omega
      rw [eq] at far
      simpa using codeFar_right (n := 2) (k := 2 * ws.length) far
    have tc : CodeAt m2 (pc + 32) (storeSpan ws.length tmp (src + 1) (address + 8)) := by
      have h := codeAt_agreeW aw frameWorld bound hord
        (codeAt_right (a := [ci 1 tmp address 0, ci 16 tmp src 0]) code) (by simpa using tf)
      simpa using h
    obtain ⟨m3, steps, changed, output⟩ := ih (effect.frame frame)
      (by simp at source; omega) (by omega) (by simp at hi; omega) tc tf tailInput
      (fun i hi' => by have h := wr (i + 1) (by simp; omega); simpa [effect.wr, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      (fun i hi' => by have h := rd (i + 1) (by simp; omega); simpa [effect.rd, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
    refine ⟨m3, ?_, effect.trans (by simpa using changed.tail), ?_⟩
    · have combined := s1.trans (s2.trans (by simpa [m2, BitVec.add_assoc] using steps))
      simpa [m1, m2, BitVec.ofInt_natCast, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm] using combined
    · intro i hi'
      simp only [Nat.zero_add, absolute_slot]
      cases i with
      | zero =>
        simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
        rw [changed.read (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
        exact rd64_write_same (by simpa [m1] using rd 0 (by simp))
      | succ i =>
        have h := output i (by simp at hi'; omega)
        simpa [absolute_slot, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Complete typed source value stored by the actual emitted loop. -/
theorem storeValue_run {m : Runner.Mem} {pc fp : Runner.W} {K tmp src address : Nat}
    {τ : Ty} {v : Wert D τ}
    (layout : LayIn L) (frameWorld : fp.toNat + 8 * K ≤ L.lo) (ht : tmp < K)
    (small : K < 2 ^ 31) (frame : FrameOK m fp K) (source : src + valueWords τ ≤ tmp)
    (lo : L.lo ≤ address) (hi : address + 8 * valueWords τ ≤ L.hi)
    (code : CodeAt m pc (storeSpan (valueWords τ) tmp src address))
    (far : CodeFar pc (2 * valueWords τ) fp K) (input : ValueAt L m fp src τ v)
    (wr : ∀ i, i < valueWords τ → all m.wr (BitVec.ofNat 64 (address + 8 * i)) 8 = true)
    (rd : ∀ i, i < valueWords τ → all m.rd (BitVec.ofNat 64 (address + 8 * i)) 8 = true) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (32 * valueWords τ), fp⟩ m' ∧
      SpanEffect fp tmp address (valueWords τ) m m' ∧ StorageAt L m' address τ v := by
  obtain ⟨m', steps, changed, output⟩ := storeSpan_run (encodeWords L τ v) layout frameWorld ht small
    frame (by simpa only [encodeWords_length] using source) lo
    (by simpa only [encodeWords_length] using hi)
    (by simpa only [encodeWords_length] using code)
    (by simpa only [encodeWords_length] using far) input.2
    (fun i h => wr i (by simpa only [encodeWords_length] using h))
    (fun i h => rd i (by simpa only [encodeWords_length] using h))
  exact ⟨m', by simpa only [encodeWords_length] using steps,
    by simpa only [encodeWords_length] using changed, input.1, output⟩

end Gabbro.Stage0.Senke
