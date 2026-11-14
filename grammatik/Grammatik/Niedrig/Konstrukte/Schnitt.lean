module

public import Grammatik.Niedrig.Konstrukte.Basis

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- Half-open value slicing. The endpoint may equal the length; reversed or
    out-of-bounds endpoints are refused by the future constructor premises. -/
def SliceOk (length first last : Nat) : Prop := first ≤ last ∧ last ≤ length

instance (length first last : Nat) : Decidable (SliceOk length first last) :=
  inferInstanceAs (Decidable (_ ∧ _))

def sliceB (length first last : Nat) : Bool := decide (SliceOk length first last)

theorem sliceB_iff (length first last : Nat) :
    sliceB length first last = true ↔ SliceOk length first last := by
  simp only [sliceB, decide_eq_true_eq]

/-- Shared subsequence operation. Values contain no new pointer or authority. -/
def sliceValue {α : Type} (values : List α) (first last : Nat) : List α :=
  (values.drop first).take (last - first)

theorem sliceValue_length {α : Type} (values : List α) (first last : Nat)
    (bounds : SliceOk values.length first last) :
    (sliceValue values first last).length = last - first := by
  unfold sliceValue
  simp only [List.length_take, List.length_drop]
  obtain ⟨ordered, inside⟩ := bounds
  omega

/-- Arrays already have fixed-length function values; selecting the translated
    Fin index gives the exact subsequence without introducing an array heap. -/
def arrSliceValue {α : Type} {length : Nat} (values : Fin length → α)
    (first last : Nat) (bounds : SliceOk length first last) : Fin (last - first) → α :=
  fun index => values ⟨first + index.val, by have := index.isLt; have ordered := bounds.1; have high := bounds.2; omega⟩

def arrSliceStep {τ : Ty} {length : Nat} (values : Wert D (.arr τ length))
    (first last : Nat) (bounds : SliceOk length first last) (world : World D) :
    ValueStep D (Wert D (.arr τ (last - first))) :=
  valueStep (arrSliceValue values first last bounds) world

/-- Strings are byte sequences in the canonical Val model, not Unicode code
    point sequences. Bounds refer to the actual length, not merely its maximum. -/
def strSliceValue {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (_bounds : SliceOk value.1.length first last) :
    Wert D (.str (last - first)) :=
  ⟨sliceValue value.1 first last, by unfold sliceValue; simp only [List.length_take]; omega⟩

def strSliceStep {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (bounds : SliceOk value.1.length first last) (world : World D) :
    ValueStep D (Wert D (.str (last - first))) :=
  valueStep (strSliceValue value first last bounds) world

theorem arrSliceStep_get {τ : Ty} {length : Nat} (values : Wert D (.arr τ length))
    (first last : Nat) (bounds : SliceOk length first last) (world : World D)
    (index : Fin (last - first)) :
    (arrSliceStep values first last bounds world).value index =
      values ⟨first + index.val, by have := index.isLt; have ordered := bounds.1; have high := bounds.2; omega⟩ := rfl

theorem strSliceStep_bytes {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (bounds : SliceOk value.1.length first last) (world : World D) :
    (strSliceStep value first last bounds world).value.1 = sliceValue value.1 first last ∧
    (strSliceStep value first last bounds world).value.1.length = last - first :=
  ⟨rfl, sliceValue_length value.1 first last bounds⟩

theorem arrSliceStep_frame {τ : Ty} {length : Nat} (values : Wert D (.arr τ length))
    (first last : Nat) (bounds : SliceOk length first last) (world : World D) :
    (arrSliceStep values first last bounds world).world = world := rfl

theorem strSliceStep_frame {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (bounds : SliceOk value.1.length first last) (world : World D) :
    (strSliceStep value first last bounds world).world = world := rfl

/-- The slice operation adds no access; combine the base and both endpoint
    expression footprints in the same order as their ordinary G evaluation. -/
def sliceFootprint (base first last : Footprint D) : Footprint D :=
  (base.append first).append last

theorem sliceFootprint_reads (base first last : Footprint D) :
    (sliceFootprint base first last).reads = (base.reads ++ first.reads) ++ last.reads := rfl

end Gabbro.Grammatik.LowLevel.Construct
