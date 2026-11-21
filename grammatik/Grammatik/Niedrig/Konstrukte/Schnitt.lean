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

/-- A slice value has a static capacity and a dynamic length.
    Its observable contents contain exactly `length` elements. -/
structure BoundedSlice (α : Type) (capacity : Nat) where
  length : Nat
  fits : length ≤ capacity
  get : Fin length → α

def BoundedSlice.ofArray {α : Type} {capacity : Nat} (array : Fin capacity → α)
    (first last : Nat) (bounds : SliceOk capacity first last) : BoundedSlice α capacity :=
  ⟨last - first, by have high := bounds.2; omega, arrSliceValue array first last bounds⟩

def BoundedSlice.checkOfArray {α : Type} {capacity : Nat} (array : Fin capacity → α)
    (first last : Nat) : Option (BoundedSlice α capacity) :=
  if bounds : SliceOk capacity first last then some (BoundedSlice.ofArray array first last bounds)
  else none

theorem BoundedSlice.checkOfArray_exact {α : Type} {capacity : Nat} (array : Fin capacity → α)
    (first last : Nat) :
    (BoundedSlice.checkOfArray array first last).isSome = true ↔ SliceOk capacity first last := by
  unfold BoundedSlice.checkOfArray
  split <;> simp_all

def BoundedSlice.subslice {α : Type} {capacity : Nat} (slice : BoundedSlice α capacity)
    (first last : Nat) (bounds : SliceOk slice.length first last) : BoundedSlice α capacity :=
  ⟨last - first, by have high := bounds.2; have fits := slice.fits; omega,
    arrSliceValue slice.get first last bounds⟩

/-- Offset and length suffice to represent a slice of an immutable array
    value. A physical implementation must preserve that backing value. -/
structure ArraySliceView (capacity : Nat) where
  offset : Nat
  length : Nat
  fits : offset + length ≤ capacity

def ArraySliceView.ofEndpoints {capacity : Nat} (first last : Nat)
    (bounds : SliceOk capacity first last) : ArraySliceView capacity :=
  ⟨first, last - first, by have low := bounds.1; have high := bounds.2; omega⟩

def ArraySliceView.read {α : Type} {capacity : Nat} (view : ArraySliceView capacity)
    (array : Fin capacity → α) (index : Fin view.length) : α :=
  array ⟨view.offset + index.val, by have valid := index.isLt; have fits := view.fits; omega⟩

def ArraySliceView.value {α : Type} {capacity : Nat} (view : ArraySliceView capacity)
    (array : Fin capacity → α) : BoundedSlice α capacity :=
  ⟨view.length, by have fits := view.fits; omega, view.read array⟩

def ArraySliceView.subslice {capacity : Nat} (view : ArraySliceView capacity)
    (first last : Nat) (bounds : SliceOk view.length first last) : ArraySliceView capacity :=
  ⟨view.offset + first, last - first,
    by have low := bounds.1; have high := bounds.2; have fits := view.fits; omega⟩

/-- Reading the descriptor denotes exactly the half-open slice value. -/
theorem ArraySliceView.value_ofEndpoints {α : Type} {capacity : Nat} (array : Fin capacity → α)
    (first last : Nat) (bounds : SliceOk capacity first last) :
    (ArraySliceView.ofEndpoints first last bounds).value array =
      BoundedSlice.ofArray array first last bounds := rfl

/-- Nested slices preserve value semantics when their descriptors are
    composed. Both indexing schemes select the same backing element. -/
theorem ArraySliceView.value_subslice {α : Type} {capacity : Nat} (view : ArraySliceView capacity)
    (array : Fin capacity → α) (first last : Nat) (bounds : SliceOk view.length first last) :
    (view.subslice first last bounds).value array = (view.value array).subslice first last bounds := by
  have same : (view.subslice first last bounds).read array =
      arrSliceValue (view.read array) first last bounds := by
    funext index
    apply congrArg array
    apply Fin.ext
    exact Nat.add_assoc _ _ _
  change BoundedSlice.mk (last - first) _ ((view.subslice first last bounds).read array) =
    BoundedSlice.mk (last - first) _ (arrSliceValue (view.read array) first last bounds)
  rw [same]

/-- A candidate backing array can stand for the saved value exactly
    when each observable slice element agrees on its translated index. -/
theorem ArraySliceView.value_eq_iff {α : Type} {capacity : Nat} (view : ArraySliceView capacity)
    (saved current : Fin capacity → α) :
    view.value saved = view.value current ↔ ∀ index, view.read saved index = view.read current index := by
  constructor
  · intro equal index
    have projected := congrArg (fun slice : BoundedSlice α capacity => (⟨slice.length, slice.get⟩ :
      Σ n : Nat, Fin n → α)) equal
    have reads : view.read saved = view.read current := eq_of_heq (Sigma.mk.inj projected).2
    exact congrFun reads index
  · intro slots
    have reads := funext slots
    change BoundedSlice.mk view.length _ (view.read saved) = BoundedSlice.mk view.length _ (view.read current)
    rw [reads]

/-- A full slice gives an admissible runtime length and denotes the
    original contents at every index. -/
theorem runtimeArraySlice_erfuellbar {α : Type} {capacity : Nat} (array : Fin capacity → α) :
    ∃ bounds : SliceOk capacity 0 capacity, ∀ index : Fin (capacity - 0),
      (BoundedSlice.ofArray array 0 capacity bounds).get index = array ⟨index.val, by omega⟩ := by
  refine ⟨⟨Nat.zero_le _, Nat.le_refl _⟩, ?_⟩
  intro index
  apply congrArg array
  exact Fin.ext (Nat.zero_add _)

/-- Strings are byte sequences in the canonical Val model, not Unicode code
    point sequences. Bounds refer to the actual length, not merely its maximum. -/
def strSliceValue {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (_bounds : SliceOk value.1.length first last) :
    Wert D (.str (last - first)) :=
  ⟨sliceValue value.1 first last, by unfold sliceValue; simp only [List.length_take]; omega⟩

/-- A runtime substring can retain the input's static byte capacity.
    Its value uses the actual half-open byte range. -/
def strBoundedSliceValue {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (bounds : SliceOk value.1.length first last) : Wert D (.str maximum) :=
  let sliced := strSliceValue value first last bounds
  ⟨sliced.1, sliced.2.trans (by have high := bounds.2; have capacity := value.2; omega)⟩

theorem strBoundedSliceValue_exact {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (bounds : SliceOk value.1.length first last) :
    (strBoundedSliceValue value first last bounds).1 = sliceValue value.1 first last ∧
      (strBoundedSliceValue value first last bounds).1.length = last - first :=
  ⟨rfl, sliceValue_length value.1 first last bounds⟩

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
