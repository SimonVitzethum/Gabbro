/- Subject: Branch-free comparison of two frame word spans, below all proofs. -/
module
public import Runner.IR.Rahmen
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

/-- OR together the XORs of `n` word pairs of the spans at `a` and `b` into the word `acc`
    (which must hold the running value): it stays zero exactly when every pair is equal. -/
def xorOrSpan : Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _ => []
  | n + 1, a, b, acc, tmp =>
      ⟨10, tmp, a, b⟩ :: ⟨9, acc, acc, tmp⟩ :: xorOrSpan n (a + 1) (b + 1) acc tmp

@[simp] theorem xorOrSpan_length (n a b acc tmp : Nat) : (xorOrSpan n a b acc tmp).length = 2 * n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [xorOrSpan, List.length_cons, ih]; omega

/-- Equality of two strings of capacity at least two: the length word and `min n m` byte words are compared,
    the padding beyond the shorter capacity is zero whenever the lengths agree. The string `s` occupies
    `n + 1` words at `d`, `t` follows it; the accumulator and one scratch word follow `t`, and the Boolean
    replaces the first word of `s`. -/
def strEqLongL (n m d : Nat) (s t : Option (List II × Nat)) : Option (List II × Nat) :=
  if 2 ≤ n ∧ 2 ≤ m ∧ n < 2 ^ 31 ∧ m < 2 ^ 31 then do
    let cs ← s
    let ct ← t
    let acc := d + (n + 1) + (m + 1)
    let tmp := acc + 1
    pure (cs.1 ++ ct.1 ++ (⟨1, acc, 0, 0⟩ :: (xorOrSpan (min n m + 1) d (d + (n + 1)) acc tmp ++
        [⟨1, tmp, 0, 0⟩, ⟨14, d, acc, tmp⟩])), max (max cs.2 ct.2) (tmp + 1))
  else none

end Gabbro.Stage0.Senke
