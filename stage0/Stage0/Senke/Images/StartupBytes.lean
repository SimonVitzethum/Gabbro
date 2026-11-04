/- Existence and extraction of initialized stacks through the shared serializer. -/
module
public import Stage0.Senke.Welt.StartEnv
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

theorem startStackBytes_some {slots base : Nat} (frames : List (List Runner.W))
    (room : ∀ words ∈ frames, base + words.length ≤ slots) :
    ∃ bytes, startStackBytes slots base frames = some bytes := by
  induction frames with
  | nil => exact ⟨[], rfl⟩
  | cons words rest ih =>
    have fits := room words (by simp)
    have made : ∃ bytes, startFrameBytes slots base words = some bytes := by
      unfold startFrameBytes
      simp only [fits, ↓reduceIte]
      exact ⟨_, rfl⟩
    obtain ⟨frame, hf⟩ := made
    obtain ⟨tail, ht⟩ := ih (fun ws hws => room ws (by simp [hws]))
    refine ⟨frame ++ tail, ?_⟩
    simp only [startStackBytes, hf, ht, bind, Option.bind_some, pure]

/-- The suffix after all initialized stacks starts at their full byte length. -/
theorem startStackBytes_tail {slots base : Nat} {frames : List (List Runner.W)}
    {bytes tail : List Runner.B} (made : startStackBytes slots base frames = some bytes)
    {m : Runner.Mem} {p : Nat} (loaded : BytesAt m p (bytes ++ tail)) :
    BytesAt m (p + 8 * slots * frames.length) tail := by
  have suffix := loaded.right
  rwa [startStackBytes_length made] at suffix

/-- Select padding or synchronization bytes without assuming that initialized world data is zero. -/
theorem zeroBytes_slice {m : Runner.Mem} {p n q count : Nat}
    (loaded : BytesAt m p (List.replicate n 0)) (start : p ≤ q) (finish : q + count ≤ p + n) :
    BytesAt m q (List.replicate count 0) := by
  intro i hi
  have read := loaded (q - p + i) (by simp only [List.length_replicate] at hi ⊢; omega)
  rw [show p + (q - p + i) = q + i by omega] at read
  simpa only [List.getElem_replicate] using read

end Gabbro.Stage0.Senke
