module

public import Grammatik.Niedrig.Konstrukte.Basis
import Grammatik.Kern.Semantik.Evaluation.Aggregates.Values

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

/-- Slice equality observes the actual length and exactly its elements. -/
theorem BoundedSlice.eq_iff {α : Type} {capacity : Nat} (left right : BoundedSlice α capacity) :
    left = right ↔ ∃ length : left.length = right.length,
      ∀ i : Fin left.length, left.get i = right.get (Fin.cast length i) := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩
  · obtain ⟨leftLength, leftFits, leftGet⟩ := left
    obtain ⟨rightLength, rightFits, rightGet⟩ := right
    rintro ⟨length, observed⟩
    dsimp only at length observed
    subst rightLength
    have same : leftGet = rightGet := funext observed
    subst rightGet
    rfl

/-- Offset and length suffice to represent a slice of an immutable array
    value. A physical implementation must preserve that backing value. -/
structure ArraySliceView (capacity : Nat) where
  offset : Nat
  length : Nat
  fits : offset + length ≤ capacity

def ArraySliceView.ofEndpoints {capacity : Nat} (first last : Nat)
    (bounds : SliceOk capacity first last) : ArraySliceView capacity :=
  ⟨first, last - first, by have low := bounds.1; have high := bounds.2; omega⟩

/-- Check signed source endpoints before their conversion to positions. -/
abbrev SignedSliceOk (length : Nat) (first last : Int) : Prop :=
  0 ≤ first ∧ first ≤ last ∧ last ≤ length

def ArraySliceView.check (capacity : Nat) (first last : Int) : Option (ArraySliceView capacity) :=
  if valid : SignedSliceOk capacity first last then
    some (ArraySliceView.ofEndpoints first.toNat last.toNat (by
      obtain ⟨_, _, _⟩ := valid
      exact ⟨by omega, by omega⟩))
  else none

theorem ArraySliceView.check_exact (capacity : Nat) (first last : Int) :
    (ArraySliceView.check capacity first last).isSome = true ↔ SignedSliceOk capacity first last := by
  unfold ArraySliceView.check
  split <;> simp_all

theorem ArraySliceView.check_result {capacity : Nat} {first last : Int} {view : ArraySliceView capacity}
    (checked : ArraySliceView.check capacity first last = some view) :
    ∃ valid : SliceOk capacity first.toNat last.toNat,
      SignedSliceOk capacity first last ∧ view = ArraySliceView.ofEndpoints first.toNat last.toNat valid ∧
      (view.offset : Int) = first ∧ (view.length : Int) = last - first := by
  unfold ArraySliceView.check at checked
  split at checked
  · rename_i valid
    obtain rfl := Option.some.inj checked
    obtain ⟨nonnegative, ordered, within⟩ := valid
    refine ⟨⟨by omega, by omega⟩, ⟨nonnegative, ordered, within⟩, rfl, ?_, ?_⟩
    · change (first.toNat : Int) = first
      omega
    · change ((last.toNat - first.toNat : Nat) : Int) = last - first
      omega
  · cases checked

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

/-- Relocating a slice descriptor preserves the value exactly when its
    runtime length and the translated element reads are preserved. -/
theorem ArraySliceView.relocated_value_eq_iff {α : Type} {capacity : Nat}
    (left right : ArraySliceView capacity) (saved current : Fin capacity → α) :
    left.value saved = right.value current ↔ ∃ length : left.length = right.length,
      ∀ index : Fin left.length, left.read saved index = right.read current (Fin.cast length index) :=
  BoundedSlice.eq_iff _ _

/-- A candidate backing array can stand for the saved value exactly
    when each observable slice element agrees on its translated index. -/
theorem ArraySliceView.value_eq_iff {α : Type} {capacity : Nat} (view : ArraySliceView capacity)
    (saved current : Fin capacity → α) :
    view.value saved = view.value current ↔ ∀ index, view.read saved index = view.read current index := by
  rw [view.relocated_value_eq_iff view saved current]
  exact ⟨fun ⟨_, same⟩ => same, fun same => ⟨rfl, same⟩⟩

/-- An update outside the represented range leaves the saved slice value
    unchanged, even if the same backing allocation is reused. -/
theorem ArraySliceView.value_arrSet_outside {α : Type} {capacity : Nat}
    (view : ArraySliceView capacity) (array : Fin capacity → α) (slot : Fin capacity) (value : α)
    (outside : slot.val < view.offset ∨ view.offset + view.length ≤ slot.val) :
    view.value (arrSetW array slot value) = view.value array := by
  apply (view.value_eq_iff _ _).mpr
  intro index
  unfold ArraySliceView.read
  apply arrSetW_other
  intro same
  have equal := congrArg Fin.val same
  have inside := index.isLt
  simp only at equal
  omega

/-- An update within the represented range permits reuse of the
    allocation exactly when it writes the old element back. -/
theorem ArraySliceView.value_arrSet_inside_iff {α : Type} {capacity : Nat}
    (view : ArraySliceView capacity) (array : Fin capacity → α) (slot : Fin capacity) (value : α)
    (inside : view.offset ≤ slot.val ∧ slot.val < view.offset + view.length) :
    view.value (arrSetW array slot value) = view.value array ↔ value = array slot := by
  constructor
  · intro equal
    obtain ⟨low, high⟩ := inside
    let index : Fin view.length := ⟨slot.val - view.offset, by omega⟩
    have atSlot : (⟨view.offset + index.val, by have bound := view.fits; have := index.isLt; omega⟩ :
        Fin capacity) = slot := Fin.ext (by dsimp [index]; omega)
    have readEqual := (view.value_eq_iff _ _).mp equal index
    simpa only [ArraySliceView.read, atSlot, arrSetW_same] using readEqual
  · rintro rfl
    rw [arrSetW_read]

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
  ⟨sliced.1, Nat.le_trans sliced.2 (by have high := bounds.2; have capacity := value.2; omega)⟩

/-- Check signed source endpoints before projecting them to natural byte
    positions. The upper bound is the actual length of the string. -/
def checkStringSlice {maximum : Nat} (value : Wert D (.str maximum)) (first last : Int) :
    Option (Wert D (.str maximum)) :=
  if valid : SignedSliceOk value.1.length first last then
    some (strBoundedSliceValue value first.toNat last.toNat ⟨by omega, by omega⟩)
  else none

theorem checkStringSlice_exact {maximum : Nat} (value : Wert D (.str maximum)) (first last : Int) :
    (checkStringSlice value first last).isSome = true ↔
      0 ≤ first ∧ first ≤ last ∧ last ≤ value.1.length := by
  unfold checkStringSlice
  split <;> simp_all

theorem strBoundedSliceValue_exact {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (bounds : SliceOk value.1.length first last) :
    (strBoundedSliceValue value first last bounds).1 = sliceValue value.1 first last ∧
      (strBoundedSliceValue value first last bounds).1.length = last - first :=
  ⟨rfl, sliceValue_length value.1 first last bounds⟩

theorem checkStringSlice_result {maximum : Nat} (value result : Wert D (.str maximum)) (first last : Int)
    (checked : checkStringSlice value first last = some result) :
    (0 ≤ first ∧ first ≤ last ∧ last ≤ value.1.length) ∧
      result.1 = sliceValue value.1 first.toNat last.toNat ∧
      (result.1.length : Int) = last - first := by
  unfold checkStringSlice at checked
  split at checked
  · rename_i valid
    obtain rfl := Option.some.inj checked
    have exactValue := strBoundedSliceValue_exact value first.toNat last.toNat ⟨by omega, by omega⟩
    exact ⟨valid, exactValue.1, by rw [exactValue.2]; omega⟩
  · cases checked

/-- A substring descriptor selects the same byte as the canonical
    string value. The index bound is over the actual substring length. -/
theorem strBoundedSliceValue_byte {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (bounds : SliceOk value.1.length first last)
    (index : Fin (last - first)) :
    let result := strBoundedSliceValue value first last bounds
    result.1[index.val]'(by rw [(strBoundedSliceValue_exact value first last bounds).2]; exact index.isLt) =
      value.1[first + index.val]'(by have hi := bounds.2; have valid := index.isLt; omega) := by
  simp only [strBoundedSliceValue, strSliceValue, sliceValue, List.getElem_take, List.getElem_drop]

/-- Composing substring offsets returns the same byte sequence as
    taking both slices, including when either length is zero. -/
theorem strBoundedSliceValue_subslice {maximum : Nat} (value : Wert D (.str maximum))
    (first last : Nat) (outer : SliceOk value.1.length first last)
    (begin finish : Nat)
    (inner : SliceOk (strBoundedSliceValue value first last outer).1.length begin finish)
    (combined : SliceOk value.1.length (first + begin) (first + finish)) :
    strBoundedSliceValue (strBoundedSliceValue value first last outer) begin finish inner =
      strBoundedSliceValue value (first + begin) (first + finish) combined := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [(strBoundedSliceValue_exact _ _ _ inner).2, (strBoundedSliceValue_exact _ _ _ combined).2]
    omega
  · intro i left right
    simp only [strBoundedSliceValue, strSliceValue, sliceValue, List.getElem_take,
      List.getElem_drop, Nat.add_assoc]

/-- A full runtime substring is admissible at every actual byte length. -/
theorem runtimeStringSlice_erfuellbar {maximum : Nat} (value : Wert D (.str maximum)) :
    ∃ bounds : SliceOk value.1.length 0 value.1.length,
      strBoundedSliceValue value 0 value.1.length bounds = value := by
  refine ⟨⟨Nat.zero_le _, Nat.le_refl _⟩, Subtype.ext ?_⟩
  simp only [strBoundedSliceValue, strSliceValue, sliceValue, List.drop_zero, Nat.sub_zero, List.take_length]

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
