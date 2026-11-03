/- Multiword byte reads iterate the established at-most-eight-byte kernel. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- One output limb per chunk. The final partial chunk is zero-extended by the
    byte kernel; extra canonical limbs (if any) are zero chunks. -/
def readBytesWordsL (L : Lay D) (t : D.Tab) (f : D.Feld t)
    (idx : Nat → Option (List II × Nat)) : Nat → Nat → Nat → Nat → Option (List II × Nat)
  | 0, _, _, d => some ([], d)
  | words + 1, n, j, d => do
    let head ← readBytesL L t f idx j (min 8 n) d
    let tail ← readBytesWordsL L t f idx words (n - 8) (j + min 8 n) (d + 1)
    pure (head.1 ++ tail.1, max head.2 tail.2)

/-- Offsets outside the immediate range already require unrepresentable emitted
    code (at least one load per byte); keep that bound explicit before expansion. -/
def readBytesWideL (L : Lay D) (t : D.Tab) (f : D.Feld t)
    (idx : Nat → Option (List II × Nat)) (n d : Nat) : Option (List II × Nat) :=
  if n < 2 ^ 31 then
    readBytesWordsL L t f idx (integerWords 0 (256 ^ n - 1)) n 0 d
  else none

theorem readBytesWordsL_top {L : Lay D} {t : D.Tab} {f : D.Feld t}
    {idx : Nat → Option (List II × Nat)} : ∀ {words n j d c top},
    readBytesWordsL L t f idx words n j d = some (c, top) → d + words ≤ top
  | 0, _, _, _, _, _, made => by
    simp only [readBytesWordsL, Option.some.injEq, Prod.mk.injEq] at made
    omega
  | words + 1, _, _, _, _, _, made => by
    simp only [readBytesWordsL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨head, _, tail, tailMade, _, rfl⟩ := made
    have := readBytesWordsL_top tailMade
    omega

theorem readBytesWideL_top {L : Lay D} {t : D.Tab} {f : D.Feld t}
    {idx : Nat → Option (List II × Nat)} {n d top : Nat} {c : List II}
    (made : readBytesWideL L t f idx n d = some (c, top)) : d < top := by
  simp only [readBytesWideL] at made
  split at made
  · have := readBytesWordsL_top made
    have positive : 0 < integerWords 0 (256 ^ n - 1) := by unfold integerWords; omega
    omega
  · cases made

end Gabbro.Stage0.Senke
