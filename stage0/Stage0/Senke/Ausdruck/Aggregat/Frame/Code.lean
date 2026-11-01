/- Subject: Code storing a complete value span into an array that lives in the frame, below all proofs. -/
import Stage0.Senke.Welt.Spans.CellCode

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Replace the element `index` (a scalar held in slot `ptr`) of the frame array starting at slot `base` by the
    `width` words starting at slot `src`. The address word is computed in `ptr` (it overwrites the index), `tmp`
    is the scratch word; `src`, `ptr` and `tmp` follow the array's complete span. -/
def storeFrameSpan (width base src ptr tmp : Nat) : List II :=
  [⟨1, tmp, 8 * width, 0⟩, ⟨5, ptr, ptr, tmp⟩, ⟨17, tmp, base, 0⟩, ⟨3, ptr, tmp, ptr⟩] ++
    storePointerSpan width src ptr tmp 0

@[simp] theorem storeFrameSpan_length (width base src ptr tmp : Nat) :
    (storeFrameSpan width base src ptr tmp).length = 4 + 3 * width := by
  simp only [storeFrameSpan, List.length_append, List.length_cons, List.length_nil, storePointerSpan_length]

end Gabbro.Stage0.Senke
