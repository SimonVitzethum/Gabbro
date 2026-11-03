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

/-- Capture the start once in `d`, compute consecutive limbs above it, then
    copy the result down in increasing order. Only frame moves are repeated by
    the byte kernels. Empty spans retain the original constant-zero lowering.
    Offsets beyond the immediate range are refused before code expansion. -/
def readBytesWideL (L : Lay D) (t : D.Tab) (f : D.Feld t)
    (idx : Nat → Option (List II × Nat)) (n d : Nat) : Option (List II × Nat) :=
  if n = 0 then some ([ci 1 d 0 0], d + 1) else
  if n < 2 ^ 31 then do
    let captured ← idx d
    let words := integerWords 0 (256 ^ n - 1)
    let chunks ← readBytesWordsL L t f (fun dst => some (copyWords 1 dst d, dst + 1))
      words n 0 (d + 1)
    pure (captured.1 ++ chunks.1 ++ copyWords words d (d + 1),
      max captured.2 (max chunks.2 (d + 1 + words)))
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
  · simp only [Option.some.injEq, Prod.mk.injEq] at made
    omega
  · split at made
    · simp only [bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq, Prod.mk.injEq] at made
      obtain ⟨captured, _, chunks, _, _, rfl⟩ := made
      omega
    · cases made

end Gabbro.Stage0.Senke
