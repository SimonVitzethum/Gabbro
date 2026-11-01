/- Complete typed storage spans use the canonical value encoding. Physical addresses
   are supplied by the checked layout, never decoded from logical pointer values. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Encoding
public import Stage0.Senke.Welt.Spans.SpanCode
public import Stage0.Senke.Ausdruck.Aggregat.Footprint
public import Stage0.Senke.Ausdruck.Quant.Memory
public import Stage0.Senke.Ausdruck.Quant.Literal
public import Stage0.Senke.Welt.WeltAt
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration} {L : Lay D}

/-- Absolute storage uses exactly the same ValueAt relation as parameters/results. -/
def StorageAt (L : Lay D) (m : Runner.Mem) (address : Nat)
    (τ : Ty) (v : Wert D τ) : Prop :=
  ValueAt L m (BitVec.ofNat 64 address) 0 τ v

/-- Reading an absolute span does not require writable source storage. -/
theorem loadSpan_stable_run [Kern] {fp : Runner.W} {K : Nat} (words : List Runner.W) :
    ∀ {m : Runner.Mem} {pc : Runner.W} {dst address : Nat} {W : Runner.Mem → Prop},
    FrameOK m fp K → K < 2 ^ 31 → dst + words.length ≤ K →
    address + 8 * words.length < 2 ^ 31 →
    CodeAt m pc (loadSpan words.length dst address) →
    CodeFar pc (2 * words.length) fp K →
    WStab W fp K → W m → (∀ m', W m' → WordsAt m' (BitVec.ofNat 64 address) 0 words) →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (32 * words.length), fp⟩ m' ∧
      Agree fp dst (dst + words.length) m m' ∧ WordsAt m' fp dst words := by
  induction words with
  | nil =>
    intro m pc dst address W frame small hd bound code far stable world source
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, by intro i hi; simp at hi⟩
  | cons w ws ih =>
    intro m pc dst address W frame small hd bound code far stable world source
    have hd' : dst < K := by simp at hd; omega
    let m1 := write m (slot fp (BitVec.ofNat 64 dst)) 8 (BitVec.ofNat 64 address).toNat
    have a1 : Agree fp dst K m m1 := agree_write frame.room (Nat.le_refl _) hd' _
    have s1 := quant_lit frame small hd' (codeAt_left code)
      (show lit32 (address : Int) = true by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega)
    have far1 : CodeFar pc (1 + (1 + 2 * ws.length)) fp K := by
      rw [show 1 + (1 + 2 * ws.length) = 2 * (w :: ws).length by simp; omega]
      exact far
    have f1 := codeFar_right (n := 1) (k := 1 + 2 * ws.length) far1
    have c1 := (codeAt_right (a := [ci 1 dst address 0]) code).agree a1 (by simpa [Nat.add_comm] using f1)
    have input0 : m.rd64 (BitVec.ofNat 64 address) = some w := by
      have h := source m world 0 (by simp)
      change m.rd64 (slot (BitVec.ofNat 64 address) 0) = some w at h
      simpa [slot] using h
    have r1 : m1.rd64 (BitVec.ofNat 64 address) = some w := by
      have h := source m1 (stable m m1 world (a1.mono (Nat.zero_le _))) 0 (by simp)
      change m1.rd64 (slot (BitVec.ofNat 64 address) 0) = some w at h
      simpa [slot] using h
    have addr1 : m1.rd64 (slot fp (BitVec.ofNat 64 dst)) = some (BitVec.ofNat 64 address) :=
      (wr_slot frame hd' (BitVec.ofNat 64 address)).2.1
    have s2 := span_load_step (frame.agree a1) small hd' hd' (codeAt_left c1) addr1 r1
    let m2 := write m1 (slot fp (BitVec.ofNat 64 dst)) 8 w.toNat
    have a2 : Agree fp dst K m1 m2 := agree_write frame.room (Nat.le_refl _) hd' _
    have tail : ∀ m', W m' → WordsAt m' (BitVec.ofNat 64 (address + 8)) 0 ws := by
      intro m' hm i hi
      have h := source m' hm (i + 1) (by simp; omega)
      simp only [Nat.zero_add, absolute_slot] at h ⊢
      have e : address + 8 + 8 * i = address + 8 * (i + 1) := by omega
      rw [e]
      exact h
    have tf := codeFar_right (n := 2) (k := 2 * ws.length) (by simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using far)
    have tc : CodeAt m2 (pc + 32) (loadSpan ws.length (dst + 1) (address + 8)) := by
      have h := (codeAt_right (a := [ci 1 dst address 0, ci 15 dst dst 0]) code).agree (a1.trans a2) (by simpa using tf)
      simpa using h
    obtain ⟨m3, steps, changed, output⟩ := ih (frame.agree (a1.trans a2)) small
      (by simp at hd; omega) (by simp at bound; omega) tc
      (by simpa using tf) stable (stable m m2 world ((a1.trans a2).mono (Nat.zero_le _))) tail
    have room : fp.toNat + 8 * (dst + (w :: ws).length) ≤ 2 ^ 64 := by have := frame.room; simp only [List.length_cons] at hd ⊢; omega
    have first : Agree fp dst (dst + (w :: ws).length) m m2 :=
      (agree_write room (Nat.le_refl _) (by simp) _).trans
        (agree_write room (Nat.le_refl _) (by simp) _)
    refine ⟨m3, ?_, first.trans (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using changed.mono (Nat.le_succ dst)), ?_⟩
    · have combined := s1.trans (s2.trans (by simpa [m2, BitVec.add_assoc] using steps))
      simpa [m1, m2, BitVec.ofInt_natCast, Nat.mul_add, BitVec.ofNat_add,
        BitVec.add_assoc, BitVec.add_comm, Nat.add_left_comm] using combined
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero, agree_rd_low changed (by have := frame.room; simp at hd; omega) (by omega) (by omega)]
        exact (wr_slot (frame.agree a1) hd' w).2.1
      | succ i => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using output i (by simp at hi; omega)

/-- The physically separated specialization, with no source writability assumption. -/
theorem loadSpan_run [Kern] {fp : Runner.W} {K : Nat} (words : List Runner.W)
    {m : Runner.Mem} {pc : Runner.W} {dst address : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (hd : dst + words.length ≤ K)
    (sep : fp.toNat + 8 * K ≤ address) (bound : address + 8 * words.length < 2 ^ 31)
    (code : CodeAt m pc (loadSpan words.length dst address)) (far : CodeFar pc (2 * words.length) fp K)
    (input : WordsAt m (BitVec.ofNat 64 address) 0 words) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (32 * words.length), fp⟩ m' ∧
      Agree fp dst (dst + words.length) m m' ∧ WordsAt m' fp dst words := by
  apply loadSpan_stable_run words frame small hd bound code far
    (W := fun m => WordsAt m (BitVec.ofNat 64 address) 0 words) ?_ input (fun _ h => h)
  intro m1 m2 h changed i hi
  simp only [Nat.zero_add, absolute_slot]
  rw [rd64_agree_out changed (by omega) (Or.inr (by omega))]
  simpa only [Nat.zero_add, absolute_slot] using h i hi

/-- Complete typed load, preserving recursive reference and IEEE validity. -/
theorem loadValue_run [Kern] {m : Runner.Mem} {pc fp : Runner.W}
    {K dst address : Nat} {τ : Ty} {v : Wert D τ}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (hd : dst + valueWords τ ≤ K) (sep : fp.toNat + 8 * K ≤ address)
    (bound : address + 8 * valueWords τ < 2 ^ 31)
    (code : CodeAt m pc (loadSpan (valueWords τ) dst address))
    (far : CodeFar pc (2 * valueWords τ) fp K)
    (input : StorageAt L m address τ v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (32 * valueWords τ), fp⟩ m' ∧
      Agree fp dst (dst + valueWords τ) m m' ∧ ValueAt L m' fp dst τ v := by
  obtain ⟨m', steps, changed, output⟩ := loadSpan_run (encodeWords L τ v) frame small
    (by simpa only [encodeWords_length] using hd) sep
    (by simpa only [encodeWords_length] using bound)
    (by simpa only [encodeWords_length] using code)
    (by simpa only [encodeWords_length] using far) input.2
  exact ⟨m', by simpa only [encodeWords_length] using steps,
    by simpa only [encodeWords_length] using changed, input.1, output⟩

end Gabbro.Stage0.Senke
