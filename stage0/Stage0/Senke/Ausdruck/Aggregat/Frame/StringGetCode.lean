/- Subject: Byte access to a string of capacity at least two with an arbitrary scalar index, below all proofs. -/
module
public import Stage0.Senke.Ausdruck.Quant.TransportCode
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

/-- With the index word in slot `p`, leave `n + (i <u n) * (i - n)` in slot `p + 3`; only the slots `p + 1` to
    `p + 3` are written, each at or above the previous one. -/
def strGetClamp (n p : Nat) : List II :=
  let f := p + 1
  let g := f + 1
  let h := g + 1
  [⟨1, f, n, 0⟩, ⟨27, f, p, f⟩, ⟨1, g, n, 0⟩, ⟨4, g, p, g⟩, ⟨5, g, g, f⟩, ⟨1, h, n, 0⟩, ⟨3, h, g, h⟩]

@[simp] theorem strGetClamp_length (n p : Nat) : (strGetClamp n p).length = 7 := by rfl

/-- Byte `i` of a string of capacity `n >= 2`, `0` outside `[0, n)`. The string occupies `n + 1` words at `d`;
    a zero sentinel word follows it, then the index word `p`. The unsigned test `i < n` (negative indices are
    large unsigned words) clamps the index to the sentinel position `n` branch-free. The selected word, copied
    to `d`, is then the byte (a padding or sentinel word is zero). The selection comes last. -/
def strGetWideL (n d : Nat) (s i : Option (List II × Nat)) : Option (List II × Nat) :=
  if 2 ≤ n ∧ n < 2 ^ 31 then do
    let cs ← s
    let ci ← i
    let z := d + n + 1
    let p := z + 1
    pure (cs.1 ++ (⟨1, z, 0, 0⟩ :: ci.1) ++ strGetClamp n p ++ selectFrameSpan 1 (d + 1) d (p + 3) (p + 4),
      max (max cs.2 ci.2) (p + 5))
  else none

end Gabbro.Stage0.Senke
