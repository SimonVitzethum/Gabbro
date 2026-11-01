/- Subject: Narrowing a string of capacity at least two to a smaller maximum, below all proofs. -/
module
public import Runner.IR.Rahmen
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Narrow the string of capacity `n >= 2` at `d` to capacity `m >= 2`: its byte words `1 .. m` already lie in
    place (the bytes beyond `m` are dropped by the smaller span, a padding word is zero), only the length word
    becomes `min len m`, computed branch-free from the scratch words `t, t + 1, t + 2` above the source span. -/
def strTakeLenL (m d t : Nat) : List II :=
  [⟨1, t, m, 0⟩, ⟨27, t + 1, t, d⟩, ⟨4, t + 2, d, t⟩, ⟨5, t + 2, t + 2, t + 1⟩, ⟨4, d, d, t + 2⟩]

/-- Narrow to capacity one: the packed word is `0` for the empty string and `256 + first byte` otherwise. -/
def strTakePackL (d t : Nat) : List II :=
  [⟨1, t, 0, 0⟩, ⟨27, t + 1, t, d⟩, ⟨1, t + 2, 256, 0⟩, ⟨3, t + 2, t + 2, d + 1⟩, ⟨5, d, t + 1, t + 2⟩]

/-- `strWeit m` of a string of capacity `n >= 2` to the smaller maximum `m < n`. -/
def strTakeL (n m d : Nat) (s : Option (List II × Nat)) : Option (List II × Nat) :=
  if 2 ≤ n ∧ m < n ∧ n < 2 ^ 31 then do
    let cs ← s
    let t := d + n + 1
    if 2 ≤ m then pure (cs.1 ++ strTakeLenL m d t, max cs.2 (t + 3))
    else if m = 1 then pure (cs.1 ++ strTakePackL d t, max cs.2 (t + 3))
    else pure (cs.1 ++ [⟨1, d, 0, 0⟩], max cs.2 (t + 1))
  else none

@[simp] theorem strTakeLenL_length (m d t : Nat) : (strTakeLenL m d t).length = 5 := rfl
@[simp] theorem strTakePackL_length (d t : Nat) : (strTakePackL d t).length = 5 := rfl

end Gabbro.Stage0.Senke
