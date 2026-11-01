/- Subject: Equality between a packed string (capacity at most one) and a long string, below all proofs. -/
module
public import Runner.IR.Rahmen
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

/-- The packed word `p0` equals the long string at `l0` exactly when the long string has at most one byte and its
    packed form (`0` if empty, `256 + first byte` otherwise) is `p0`. All scratch words `t .. t + 3` lie above both
    operands; the Boolean replaces the word `d`. -/
def strEqMixedC (p0 l0 d t : Nat) : List II :=
  [⟨1, t, 0, 0⟩, ⟨27, t + 1, t, l0⟩, ⟨1, t + 2, 256, 0⟩, ⟨3, t + 2, t + 2, l0 + 1⟩, ⟨5, t + 2, t + 1, t + 2⟩,
   ⟨14, t + 2, t + 2, p0⟩, ⟨1, t + 3, 2, 0⟩, ⟨27, t + 3, l0, t + 3⟩, ⟨8, d, t + 2, t + 3⟩]

@[simp] theorem strEqMixedC_length (p0 l0 d t : Nat) : (strEqMixedC p0 l0 d t).length = 9 := by rfl

/-- Equality of strings where exactly one has capacity at most one. `s` occupies its complete span at `d`, `t`
    follows; the Boolean replaces the first word of `s`. -/
def strEqMixedL (n m d : Nat) (s t : Option (List II × Nat)) : Option (List II × Nat) :=
  if n ≤ 1 ∧ 2 ≤ m ∧ m < 2 ^ 31 then do
    let cs ← s
    let ct ← t
    let t0 := d + 1 + (m + 1)
    pure (cs.1 ++ ct.1 ++ strEqMixedC d (d + 1) d t0, max (max cs.2 ct.2) (t0 + 4))
  else if 2 ≤ n ∧ m ≤ 1 ∧ n < 2 ^ 31 then do
    let cs ← s
    let ct ← t
    let t0 := d + (n + 1) + 1
    pure (cs.1 ++ ct.1 ++ strEqMixedC (d + (n + 1)) d d t0, max (max cs.2 ct.2) (t0 + 4))
  else none

end Gabbro.Stage0.Senke
