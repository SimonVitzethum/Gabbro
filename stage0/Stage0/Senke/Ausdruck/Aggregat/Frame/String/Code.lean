/- Shared long-string normalization and the actual concatenation/order kernels. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringExpandCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Code
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Short operands enter the same length/byte span used by existing long-string operations. -/
def stringCapacity (n : Nat) : Nat := max 2 n

def stringSpanL (n d : Nat) (child : Option (List II × Nat)) : Option (List II × Nat) :=
  if n ≤ 1 then strExpandL n 2 d child (constWords [0] (d + 2))
  else child.map fun p => (p.1, max p.2 (d + n + 1))

/-- A key is zero beyond the length, otherwise byte + 1. Thus embedded zero bytes
    remain distinguishable from a missing byte. Scratch starts at `tmp`. -/
def stringKeyC (capacity base index out tmp : Nat) : List II :=
  if index < capacity then
    [⟨1, tmp, index, 0⟩, ⟨27, out, tmp, base⟩, ⟨1, tmp, 1, 0⟩,
      ⟨3, tmp, tmp, base + 1 + index⟩, ⟨5, out, out, tmp⟩]
  else [⟨1, out, 0, 0⟩]

/-- The existing unsigned/equality ALU kernel updates a lexicographic suffix flag. -/
def stringCompareC (x y acc tmp : Nat) : List II :=
  [⟨27, tmp, x, y⟩, ⟨14, tmp + 1, x, y⟩,
    ⟨8, acc, tmp + 1, acc⟩, ⟨9, acc, tmp, acc⟩]

/-- Descending scan: the smaller index overwrites the suffix only when it differs. -/
def stringScanC : Nat → Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _, _ => []
  | k + 1, n, q, a, b, acc =>
      stringKeyC n a k (acc + 1) (acc + 3) ++
      stringKeyC q b k (acc + 2) (acc + 3) ++
      stringCompareC (acc + 1) (acc + 2) acc (acc + 3) ++
      stringScanC k n q a b acc

/-- Both operands are preserved above the one-word result. -/
def strLtSpanL (n q d : Nat) (s t : Option (List II × Nat)) : Option (List II × Nat) :=
  if stringCapacity n < 2 ^ 31 ∧ stringCapacity q < 2 ^ 31 then do
    let cs ← stringSpanL n (d + 1) s
    let b := d + 1 + (stringCapacity n + 1)
    let ct ← stringSpanL q b t
    let acc := b + (stringCapacity q + 1)
    pure (cs.1 ++ ct.1 ++ [⟨1, acc, 0, 0⟩] ++
      stringScanC (max (stringCapacity n) (stringCapacity q)) (stringCapacity n)
        (stringCapacity q) (d + 1) b acc ++ [⟨2, d, acc, 0⟩],
      max (max cs.2 ct.2) (acc + 5))
  else none

/-- Copy each byte through the existing dynamic-offset frame store. Its stride is
    always eight bytes, so large capacities do not introduce a stride-literal refusal. -/
def stringAppendC : Nat → Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _, _ => []
  | k + 1, base, src, len, ptr, index =>
      [⟨1, ptr, index, 0⟩, ⟨3, ptr, len, ptr⟩] ++
      storeFrameSpan 1 base src ptr (ptr + 1) ++
      stringAppendC k base (src + 1) len ptr (index + 1)

/-- Copy the complete padded second byte span at the first string's runtime length.
    The output starts below both operand spans and has exactly the declared capacity. -/
def stringCatC (n q d a b ptr : Nat) : List II :=
  copyWords n (d + 1) (a + 1) ++
  (constWords (List.replicate q 0) (d + 1 + n)).1 ++
  stringAppendC q (d + 1) (b + 1) a ptr 0 ++
  [⟨3, d, a, b⟩]

def strCatSpanL (n q d : Nat) (s t : Option (List II × Nat)) : Option (List II × Nat) :=
  if 2 ≤ n + q ∧ n + q < 2 ^ 31 then do
    let a := d + (n + q + 1)
    let cs ← stringSpanL n a s
    let b := a + (stringCapacity n + 1)
    let ct ← stringSpanL q b t
    let ptr := b + (stringCapacity q + 1)
    pure (cs.1 ++ ct.1 ++ stringCatC n q d a b ptr,
      max (max cs.2 ct.2) (max (ptr + 2) (constWords (List.replicate q 0) (d + 1 + n)).2))
  else none

end Gabbro.Stage0.Senke
