/- Pure stack-image construction, independent of compiler/image execution proofs.
   Bild can consume these constructors without importing BildLese or creating a cycle. -/
import Runner.Prog.IRAsm

namespace Gabbro.Stage0.Senke

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


/-- Parameterless startup retains the existing zero-filled stack image exactly. -/
theorem startFrameBytes_empty {slots base : Nat} (room : base ≤ slots) :
    startFrameBytes slots base [] = some (List.replicate (8 * slots) 0) := by
  simp only [startFrameBytes, List.length_nil, Nat.add_zero, room, ↓reduceIte,
    startWordBytes, List.flatMap_nil, List.append_nil, Nat.sub_zero]
  rw [List.replicate_append_replicate]
  congr 2
  omega

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


/-- An image of parameterless roots is byte-for-byte identical to the established stack area. -/
theorem startStackBytes_empty {slots base : Nat} (room : base ≤ slots) (count : Nat) :
    startStackBytes slots base (List.replicate count []) =
      some (List.replicate (8 * slots * count) 0) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ, startStackBytes, startFrameBytes_empty room, ih]
    change some (List.replicate (8 * slots) 0 ++ List.replicate (8 * slots * count) 0) = _
    rw [List.replicate_append_replicate]
    congr 2
    rw [Nat.mul_succ]
    omega

/-- Frame spans are pairwise disjoint under the same stack stride used by existing spawn code. -/
theorem startStackBytes_disjoint (p slots i j : Nat) (ordered : i < j) :
    (p + 8 * slots * i) + 8 * slots ≤ p + 8 * slots * j := by
  have bound := Nat.mul_le_mul_left (8 * slots) (show i + 1 ≤ j by omega)
  rw [Nat.mul_succ] at bound
  omega


end Gabbro.Stage0.Senke
