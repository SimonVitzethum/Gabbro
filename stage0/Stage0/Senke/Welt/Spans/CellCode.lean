/- Canonical typed cell addressing and runtime-pointer span stores, below all proofs.
   Every cell occupies its complete value span; the stride is the span, never one word. -/
import Stage0.Senke.Welt.Spans.SpanCode
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Store a complete frame span through a physical address held in a reserved frame slot.
    The pointer is untouched; the single scratch word is rewritten for every limb. -/
def storePointerSpan : Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _ => []
  | n + 1, src, ptr, tmp, offset =>
      ⟨1, tmp, 8 * offset, 0⟩ :: ⟨3, tmp, ptr, tmp⟩ :: ⟨16, tmp, src, 0⟩ ::
        storePointerSpan n (src + 1) ptr tmp (offset + 1)

@[simp] theorem storePointerSpan_length (n src ptr tmp offset : Nat) :
    (storePointerSpan n src ptr tmp offset).length = 3 * n := by
  induction n generalizing src offset with
  | zero => rfl
  | succ n ih => simp [storePointerSpan, ih]; omega

/-- Physical address of element `index` of column `f`: column plus index times the
    complete cell span. The index word is computed by `index` into slot `d`. -/
def cellAddressC (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) (index : List II × Nat) :
    Option (List II × Nat) :=
  if L.col t f < 2 ^ 31 ∧ 8 * valueWords (D.typ t f) < 2 ^ 31 then
    some (index.1 ++ [⟨1, d + 1, 8 * valueWords (D.typ t f), 0⟩, ⟨5, d, d, d + 1⟩,
        ⟨1, d + 1, L.col t f, 0⟩, ⟨3, d, d, d + 1⟩], max index.2 (d + 2))
  else none

/-- Read a complete cell: the address word above the result span, then every limb. The
    index code is lowered at slot `d + valueWords`. -/
def slotValueC (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) (index : List II × Nat) :
    Option (List II × Nat) := do
  let a ← cellAddressC L t f (d + valueWords (D.typ t f)) index
  pure (a.1 ++ loadPointerSpan (valueWords (D.typ t f)) d (d + valueWords (D.typ t f))
      (d + valueWords (D.typ t f) + 1) 0, max a.2 (d + valueWords (D.typ t f) + 2))

/-- Write a complete cell: the child value spans `d ..`, the index and address above it. -/
def slotStoreC (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) (child index : List II × Nat) :
    Option (List II × Nat) := do
  let a ← cellAddressC L t f (d + valueWords (D.typ t f)) index
  pure (child.1 ++ a.1 ++ storePointerSpan (valueWords (D.typ t f)) d (d + valueWords (D.typ t f))
      (d + valueWords (D.typ t f) + 1) 0,
    max (max child.2 a.2) (d + valueWords (D.typ t f) + 2))

end Gabbro.Stage0.Senke
