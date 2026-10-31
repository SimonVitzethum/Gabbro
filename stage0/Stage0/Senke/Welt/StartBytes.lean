/- Image stack initialization from the shared value encoder's words. This module only
   serializes words; it defines no alternative value encoding or startup execution path. -/
import Stage0.Senke.BildLese

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Serialize frame words with the runner loader's existing little-endian byte format. -/
def startWordBytes (words : List Runner.W) : List Runner.B :=
  words.flatMap (fun word => Runner.Prog.leN 8 word.toNat)

@[simp] theorem startWordBytes_length (words : List Runner.W) :
    (startWordBytes words).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [startWordBytes, List.flatMap_cons, List.length_append, Runner.Prog.leN,
      List.length_map, List.length_range, List.length_cons] at *
    omega

/-- One stack frame, with its declared parameter words at `base`. Bounds are checked
    before allocating bytes. Other slots retain zero initialization. -/
def startFrameBytes (slots base : Nat) (words : List Runner.W) : Option (List Runner.B) :=
  if base + words.length ≤ slots then
    some (List.replicate (8 * base) 0 ++ startWordBytes words ++
      List.replicate (8 * (slots - base - words.length)) 0)
  else none

/-- Accepted frame initialization occupies exactly the allocated frame. -/
theorem startFrameBytes_length {slots base : Nat} {words : List Runner.W} {bytes : List Runner.B}
    (made : startFrameBytes slots base words = some bytes) : bytes.length = 8 * slots := by
  unfold startFrameBytes at made
  split at made
  · next room =>
    cases made
    simp only [List.length_append, List.length_replicate, startWordBytes_length]
    omega
  · cases made

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

/-- Concatenate one initialized stack for each semantic start, retaining list order and
    multiplicity. The caller includes the primary thread as the first entry. -/
def startStackBytes (slots base : Nat) : List (List Runner.W) → Option (List Runner.B)
  | [] => some []
  | words :: rest => do
    let frame ← startFrameBytes slots base words
    let tail ← startStackBytes slots base rest
    pure (frame ++ tail)

theorem startStackBytes_length {slots base : Nat} {frames : List (List Runner.W)}
    {bytes : List Runner.B} (made : startStackBytes slots base frames = some bytes) :
    bytes.length = 8 * slots * frames.length := by
  induction frames generalizing bytes with
  | nil => cases made; rfl
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
        rw [List.length_append, startFrameBytes_length hf, ih ht, List.length_cons, Nat.mul_succ]
        omega

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

/-- Frame spans are pairwise disjoint under the same stack stride used by existing spawn code. -/
theorem startStackBytes_disjoint (p slots i j : Nat) (ordered : i < j) :
    (p + 8 * slots * i) + 8 * slots ≤ p + 8 * slots * j := by
  have bound := Nat.mul_le_mul_left (8 * slots) (show i + 1 ≤ j by omega)
  rw [Nat.mul_succ] at bound
  omega

end Gabbro.Stage0.Senke
