/- Subject: Widening a packed string (capacity at most one) to a long string span, below all proofs. -/
import Stage0.Senke.Ausdruck.Aggregat.Kopie

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- The packed word `w` at `d` is `0` (empty) or `256 + byte`. In the scratch words above the target span the head
    leaves the length word `[w <> 0]` in `t` and the first byte `(w - 256) * [w <> 0]` in `t + 1`. -/
def strExpandHead (d t : Nat) : List II :=
  [⟨1, t + 2, 0, 0⟩, ⟨27, t, t + 2, d⟩, ⟨1, t + 1, 256, 0⟩, ⟨4, t + 1, d, t + 1⟩, ⟨5, t + 1, t + 1, t⟩]

@[simp] theorem strExpandHead_length (d t : Nat) : (strExpandHead d t).length = 5 := rfl

/-- `strWeit m` of a string of capacity at most one to a long capacity `m >= 2`: the scratch words are copied into
    the first two words of the span and the remaining `m - 1` words are zero. `z` materializes those zeros
    (`constWords (List.replicate (m - 1) 0) (d + 2)`). -/
def strExpandL (n m d : Nat) (s : Option (List II × Nat)) (z : List II × Nat) : Option (List II × Nat) :=
  if n ≤ 1 ∧ 2 ≤ m ∧ m < 2 ^ 31 then do
    let cs ← s
    let t := d + m + 1
    pure (cs.1 ++ (strExpandHead d t ++ (copyWords 2 d t ++ z.1)), max cs.2 (max (t + 3) z.2))
  else none

end Gabbro.Stage0.Senke
