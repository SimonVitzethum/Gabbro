/- Image stack initialization from the shared value encoder's words. This module only
   serializes words; it defines no alternative value encoding or startup execution path. -/
import Stage0.Senke.Welt.StartLayout
import Stage0.Senke.BildLese

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- The emitted initialized bytes supply full frame permissions; zero contents are unnecessary. -/
theorem startFrameBytes_frame {slots base p : Nat} {words : List Runner.W} {bytes : List Runner.B}
    (made : startFrameBytes slots base words = some bytes) {m : Runner.Mem}
    (loaded : BytesAt m p bytes) (room : p + 8 * slots < 2 ^ 64) :
    FrameOK m (BitVec.ofNat 64 p) slots :=
  frameOK_bytes loaded (by rw [startFrameBytes_length made]) room

/-- Every serialized word reads back exactly, including all high bits and trailing words. -/
theorem startWordBytes_read {m : Runner.Mem} (words : List Runner.W) (p : Nat)
    (loaded : BytesAt m p (startWordBytes words)) :
    ∀ i (hi : i < words.length),
      m.rd64 (BitVec.ofNat 64 (p + 8 * i)) = some words[i] := by
  induction words generalizing p with
  | nil => intro i hi; simp at hi
  | cons word rest ih =>
    intro i hi
    have bytes : BytesAt m p (Runner.Prog.leN 8 word.toNat ++ startWordBytes rest) := loaded
    cases i with
    | zero =>
      simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        rd64_leN bytes word.isLt
    | succ i =>
      have tail := bytes.right
      simp only [Runner.Prog.leN, List.length_map, List.length_range] at tail
      have result := ih (p + 8) tail i (by simpa using hi)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using result

/-- Actual initialized frame bytes establish every parameter word under the same final image
    address. The word list will be supplied by `encodeWords` after relocation, not host pointers. -/
theorem startFrameBytes_read {slots base p : Nat} {words : List Runner.W} {bytes : List Runner.B}
    (made : startFrameBytes slots base words = some bytes) {m : Runner.Mem}
    (loaded : BytesAt m p bytes) :
    ∀ i (hi : i < words.length),
      m.rd64 (BitVec.ofNat 64 (p + 8 * (base + i))) = some words[i] := by
  unfold startFrameBytes at made
  split at made
  · cases made
    have params := loaded.left.right
    simp only [List.length_replicate] at params
    intro i hi
    have result := startWordBytes_read words (p + 8 * base) params i hi
    convert result using 1; congr 2; omega
  · cases made

private theorem zeroBytes_read {m : Runner.Mem} {p slots : Nat}
    (loaded : BytesAt m p (List.replicate (8 * slots) 0)) (j : Nat) (bound : j < slots) :
    m.rd64 (BitVec.ofNat 64 (p + 8 * j)) = some 0 := by
  have split : List.replicate (8 * slots) (0 : Runner.B) =
      List.replicate (8 * j) 0 ++ (List.replicate 8 0 ++ List.replicate (8 * (slots - j - 1)) 0) := by
    rw [List.replicate_append_replicate, List.replicate_append_replicate]
    congr 1
    omega
  rw [split] at loaded
  have tail := loaded.right
  simp only [List.length_replicate] at tail
  have zero : Runner.Prog.leN 8 0 = List.replicate 8 (0 : Runner.B) := by decide
  rw [← zero] at tail
  exact rd64_leN tail (by decide)

/-- Headers and all slots after the full parameter span retain zero initialization.
    In particular result/status/counter areas cannot be overwritten by argument limbs. -/
theorem startFrameBytes_outside {slots base p : Nat} {words : List Runner.W} {bytes : List Runner.B}
    (made : startFrameBytes slots base words = some bytes) {m : Runner.Mem}
    (loaded : BytesAt m p bytes) (j : Nat) (bound : j < slots)
    (outside : j < base ∨ base + words.length ≤ j) :
    m.rd64 (BitVec.ofNat 64 (p + 8 * j)) = some 0 := by
  unfold startFrameBytes at made
  split at made
  · next room =>
    cases made
    rcases outside with before | after
    · exact zeroBytes_read loaded.left.left j before
    · have suffix := loaded.right
      simp only [List.length_append, List.length_replicate, startWordBytes_length] at suffix
      have read := zeroBytes_read suffix (j - base - words.length) (by omega)
      convert read using 1; congr 2; omega
  · cases made

theorem startStackBytes_frame {slots base : Nat} {frames : List (List Runner.W)}
    {bytes : List Runner.B} (made : startStackBytes slots base frames = some bytes)
    {m : Runner.Mem} (p : Nat) (loaded : BytesAt m p bytes) :
    ∀ j (hj : j < frames.length), ∃ frame,
      startFrameBytes slots base frames[j] = some frame ∧
      BytesAt m (p + 8 * slots * j) frame := by
  induction frames generalizing p bytes with
  | nil => intro j hj; simp at hj
  | cons words rest ih =>
    unfold startStackBytes at made
    cases hf : startFrameBytes slots base words with
    | none => rw [hf] at made; cases made
    | some frame =>
      rw [hf] at made
      cases ht : startStackBytes slots base rest with
      | none => rw [ht] at made; cases made
      | some tail =>
        rw [ht] at made
        change some (frame ++ tail) = some bytes at made
        cases made
        intro j hj
        cases j with
        | zero => exact ⟨frame, hf, by simpa using loaded.left⟩
        | succ j =>
          have part := ih ht (p + frame.length) loaded.right j (by simpa using hj)
          obtain ⟨b, hb, loadedb⟩ := part
          refine ⟨b, hb, ?_⟩
          rw [startFrameBytes_length hf] at loadedb
          simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using loadedb

end Gabbro.Stage0.Senke
