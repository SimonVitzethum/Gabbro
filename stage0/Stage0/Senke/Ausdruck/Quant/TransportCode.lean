/- Shared raw IR span builders; independent of world, environments and codecs. -/
import Runner.IR.Rahmen
namespace Gabbro.Stage0.Senke
open Runner.IR
/-- Read a complete span at a checked physical address into fresh frame slots.
    Each address is materialized separately so no hidden temporary slot is needed. -/
def loadSpan : Nat → Nat → Nat → List II
  | 0, _, _ => []
  | n + 1, dst, address =>
      ⟨1, dst, address, 0⟩ :: ⟨15, dst, dst, 0⟩ :: loadSpan n (dst + 1) (address + 8)

@[simp] theorem loadSpan_length (n dst address : Nat) :
    (loadSpan n dst address).length = 2 * n := by
  induction n generalizing dst address with
  | zero => rfl
  | succ n ih => simp [loadSpan, ih]; omega

/-- Emit one real store per limb. The sole temporary is explicitly reserved by callers. -/
def storeSpan : Nat → Nat → Nat → Nat → List II
  | 0, _, _, _ => []
  | n + 1, tmp, src, address =>
      ⟨1, tmp, address, 0⟩ :: ⟨16, tmp, src, 0⟩ :: storeSpan n tmp (src + 1) (address + 8)

@[simp] theorem storeSpan_length (n tmp src address : Nat) :
    (storeSpan n tmp src address).length = 2 * n := by
  induction n generalizing src address with
  | zero => rfl
  | succ n ih => simp [storeSpan, ih]; omega

/-- Load through a physical address supplied in a reserved frame slot. Offset and
    destination are explicit; the pointer remains unchanged and one scratch word is reused. -/
def loadPointerSpan : Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _ => []
  | n + 1, dst, ptr, tmp, offset =>
      ⟨1, tmp, 8 * offset, 0⟩ :: ⟨3, tmp, ptr, tmp⟩ :: ⟨15, dst, tmp, 0⟩ ::
        loadPointerSpan n (dst + 1) ptr tmp (offset + 1)

@[simp] theorem loadPointerSpan_length (n dst ptr tmp offset : Nat) :
    (loadPointerSpan n dst ptr tmp offset).length = 3 * n := by
  induction n generalizing dst offset with
  | zero => rfl
  | succ n ih => simp [loadPointerSpan, ih]; omega

/-- Select a complete frame element using the scalar index in `ptr`. The
    pointer and one scratch slot follow the source aggregate's complete span. -/
def selectFrameSpan (width dst ptr tmp : Nat) : List II :=
  [⟨1, tmp, 8 * width, 0⟩, ⟨5, ptr, ptr, tmp⟩,
   ⟨17, tmp, dst, 0⟩, ⟨3, ptr, tmp, ptr⟩] ++
    loadPointerSpan width dst ptr tmp 0

@[simp] theorem selectFrameSpan_length (width dst ptr tmp : Nat) :
    (selectFrameSpan width dst ptr tmp).length = 4 + 3 * width := by
  simp [selectFrameSpan]; omega

end Gabbro.Stage0.Senke

