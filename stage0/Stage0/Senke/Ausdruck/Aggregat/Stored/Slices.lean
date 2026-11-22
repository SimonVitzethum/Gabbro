module

public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Span
public import Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices
import Stage0.Senke.Welt.Spans.Cell

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg LowLevel.Construct
open Runner.IR

/-- The physical span for a slice represents exactly its visible elements.
    Its base points at the first element in the existing storage. -/
def SliceAt {D : Deklaration} (layout : Lay D) (memory : Runner.Mem) (frame : Runner.W) (base : Nat)
    {τ : Ty} {capacity : Nat} (slice : BoundedSlice (Wert D τ) capacity) : Prop :=
  ∀ index, ValueAt layout memory frame (base + index.val * valueWords τ) τ (slice.get index)

/-- An array's existing representation supplies a zero-copy slice span.
    The result refers to the same memory and Frame pointer. -/
theorem ValueAt.slice_view {D : Deklaration} {layout : Lay D} {memory : Runner.Mem} {frame : Runner.W}
    {base capacity : Nat} {τ : Ty} {value : Wert D (.arr τ capacity)}
    (array : ValueAt layout memory frame base (.arr τ capacity) value)
    (view : ArraySliceView capacity) :
    SliceAt (τ := τ) layout memory frame (base + view.offset * valueWords τ) (view.value value) :=
  fun index => array.slice_element view index

/-- A successful signed endpoint check selects a span of the existing
    array. It represents the exact value and needs no new element storage. -/
theorem ValueAt.checked_slice_view {D : Deklaration} {layout : Lay D} {memory : Runner.Mem}
    {frame : Runner.W} {base capacity : Nat} {τ : Ty} {value : Wert D (.arr τ capacity)}
    (array : ValueAt layout memory frame base (.arr τ capacity) value)
    {first last : Int} {view : ArraySliceView capacity}
    (checked : ArraySliceView.check capacity first last = some view) :
    ∃ valid : SliceOk capacity first.toNat last.toNat,
      (view.length : Int) = last - first ∧
      SliceAt (τ := τ) layout memory frame (base + first.toNat * valueWords τ)
        (BoundedSlice.ofArray value first.toNat last.toNat valid) := by
  obtain ⟨valid, _, _, _, length⟩ := ArraySliceView.check_result checked
  refine ⟨valid, length, ?_⟩
  let selected := ArraySliceView.ofEndpoints first.toNat last.toNat valid
  have stored : SliceAt (τ := τ) layout memory frame (base + selected.offset * valueWords τ)
      (selected.value value) := ValueAt.slice_view array selected
  have same : selected.value value = BoundedSlice.ofArray value first.toNat last.toNat valid :=
    ArraySliceView.value_ofEndpoints (α := Wert D τ) (capacity := capacity) value first.toNat last.toNat valid
  exact same ▸ stored

/-- Encode an array view as offset and length. The array's declared
    storage location is carried separately by the typed lowering. -/
def sliceDescriptorWords {capacity : Nat} (view : ArraySliceView capacity) : List Runner.W :=
  [BitVec.ofNat 64 view.offset, BitVec.ofNat 64 view.length]

/-- Read the saved descriptor through the ordinary frame layout. Bounds
    are re-established before any element address can be formed. -/
def readSliceDescriptor (memory : Runner.Mem) (frame : Runner.W) (storage capacity : Nat) :
    Option (ArraySliceView capacity) := do
  let offset ← memory.rd64 (slot frame (BitVec.ofNat 64 storage))
  let length ← memory.rd64 (slot frame (BitVec.ofNat 64 (storage + 1)))
  if valid : offset.toNat + length.toNat ≤ capacity then
    some ⟨offset.toNat, length.toNat, valid⟩
  else none

theorem readSliceDescriptor_exact {memory : Runner.Mem} {frame : Runner.W} {storage capacity : Nat}
    (view : ArraySliceView capacity) (sized : capacity < 2 ^ 64)
    (stored : WordsAt memory frame storage (sliceDescriptorWords view)) :
    readSliceDescriptor memory frame storage capacity = some view := by
  have offset := stored 0 (by simp [sliceDescriptorWords])
  have length := stored 1 (by simp [sliceDescriptorWords])
  simp only [sliceDescriptorWords, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at offset length
  have offsetFits : view.offset < 2 ^ 64 := (Nat.le_trans (Nat.le_add_right _ _) view.fits).trans_lt sized
  have lengthFits : view.length < 2 ^ 64 := (Nat.le_trans (Nat.le_add_left _ _) view.fits).trans_lt sized
  simp only [readSliceDescriptor, offset, length, Option.bind_eq_bind, Option.bind_some,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetFits, Nat.mod_eq_of_lt lengthFits, dite_eq_left view.fits]

/-- A descriptor loaded from the frame selects the exact value of the
    modeled view in its original allocation. The visible element width
    is inherited from the underlying type, including aggregate types. -/
theorem ValueAt.decode_slice_descriptor {D : Deklaration} {layout : Lay D} {memory : Runner.Mem}
    {frame : Runner.W} {base storage capacity : Nat} {τ : Ty} {value : Wert D (.arr τ capacity)}
    (array : ValueAt layout memory frame base (.arr τ capacity) value)
    (view : ArraySliceView capacity) (sized : capacity < 2 ^ 64)
    (stored : WordsAt memory frame storage (sliceDescriptorWords view)) :
    readSliceDescriptor memory frame storage capacity = some view ∧
      SliceAt (τ := τ) layout memory frame (base + view.offset * valueWords τ) (view.value value) :=
  ⟨readSliceDescriptor_exact view sized stored, array.slice_view view⟩

/-- The internal descriptor is the ordinary product of two bounded
    integers. Building it uses the endpoints and never reads array slots. -/
def sliceDescriptorExpr {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {capacity : Nat} {firstLo firstHi lastLo lastHi : Int}
    (first : Expr D Γ Λ (.int firstLo firstHi)) (last : Expr D Γ Λ (.int lastLo lastHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity ∧ firstHi ≤ capacity) :
    Expr D Γ Λ (.prod 0 [.int 0 capacity, .int 0 capacity]) :=
  .prod 0 (.cons (.widen bounds.1 bounds.2.2.2 first)
    (.cons (.widen (by omega) (by omega) (.sub last first)) .nil))

theorem sliceDescriptorExpr_reads {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {capacity : Nat} {firstLo firstHi lastLo lastHi : Int}
    (first : Expr D Γ Λ (.int firstLo firstHi)) (last : Expr D Γ Λ (.int lastLo lastHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity ∧ firstHi ≤ capacity)
    (localFirst : first.orte = []) :
    (sliceDescriptorExpr first last bounds).orte = first.orte ++ last.orte := by
  simp only [sliceDescriptorExpr, Expr.orte, Args.orte, localFirst, List.nil_append, List.append_nil]

/-- Actual Stage 0 expression code writes the two descriptor words and
    preserves the backing array below its scratch area. -/
theorem lowE_slice_descriptor_ok [Kern] {D : Deklaration} {layout : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {capacity : Nat}
    {firstLo firstHi lastLo lastHi : Int}
    (array : Wert D (.arr τ capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity ∧ firstHi ≤ capacity)
    (sized : (capacity : Int) < 2 ^ 63)
    {world : World D} {env : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K d base top reserved : Nat} {code : List II}
    (worldAt : ∀ m, W m → WeltAt m layout world) (layoutIn : LayIn layout)
    (backing : ValueAt layout m fp base (.arr τ capacity) array) (below : base + valueWords (.arr τ capacity) ≤ d)
    (made : lowE (currentOld := true) layout (reserved := reserved) (sliceDescriptorExpr begin finish bounds) d =
      some (code, top)) (fits : top ≤ K) (pre : Pre layout m pc fp K d code env W reserved) :
    let first := eval world begin world env
    let last := eval world finish world env
    ∃ ordered : SliceOk capacity first.n.toNat last.n.toNat,
      let view := ArraySliceView.ofEndpoints first.n.toNat last.n.toNat ordered
      Executes m pc fp K d code (fun after => readSliceDescriptor after fp d capacity = some view ∧
        SliceAt (τ := τ) layout after fp (base + view.offset * valueWords τ) (view.value array)) := by
  intro first last
  obtain ⟨ordered, actualLength⟩ := eval_localArraySliceLength array begin finish
    ⟨bounds.1, bounds.2.1, bounds.2.2.1⟩ world world env
  let view := ArraySliceView.ofEndpoints first.n.toNat last.n.toNat ordered
  let expression := sliceDescriptorExpr begin finish bounds
  have inFrame : d ≤ K := (lowE_top expression d code top made).le.trans fits
  have width : integerWords 0 capacity = 1 := integerWords_word (by decide) sized
  have capacityFits : capacity < 2 ^ 64 := by omega
  have firstNonnegative : 0 ≤ first.n := bounds.1.trans first.lo_le
  have firstWord : BitVec.ofInt 64 first.n = BitVec.ofNat 64 view.offset := by
    change BitVec.ofInt 64 first.n = BitVec.ofNat 64 first.n.toNat
    simpa only [BitVec.ofInt_natCast] using congrArg (BitVec.ofInt 64) (Int.toNat_of_nonneg firstNonnegative).symm
  have lastWord : BitVec.ofInt 64 (eval world (.sub finish begin) world env).n = BitVec.ofNat 64 view.length := by
    rw [actualLength, BitVec.ofInt_natCast]
    rfl
  have encoding : encodeWords layout _ (eval world expression world env) = sliceDescriptorWords view := by
    simp only [expression, sliceDescriptorExpr, eval, evalProd, encodeWords, encodeProductFields, reduceCtorEq,
      ite_false, ProdVal.hd, ProdVal.tl, width, integerEncoding, List.cons_append, List.nil_append, Zahl.weiter]
    change [BitVec.ofInt 64 first.n, BitVec.ofInt 64 (eval world (.sub finish begin) world env).n] =
      [BitVec.ofNat 64 view.offset, BitVec.ofNat 64 view.length]
    rw [firstWord, lastWord]
  obtain ⟨after, run, confined, stored⟩ :=
    lowE_ok (same := fun _ => rfl) world world worldAt layoutIn expression d code top made fits m pc env pre
  have preserved := backing.agree_low confined pre.frame.room below inFrame
  have descriptor : WordsAt after fp d (sliceDescriptorWords view) := encoding ▸ stored.2
  exact ⟨ordered, after, run, confined, preserved.decode_slice_descriptor view capacityFits descriptor⟩

/-- The representation of an existing slice can be narrowed by moving
    the base. All observed bytes and their layout obligations are inherited. -/
theorem SliceAt.subslice {D : Deklaration} {layout : Lay D} {memory : Runner.Mem} {frame : Runner.W}
    {base capacity : Nat} {τ : Ty} {value : BoundedSlice (Wert D τ) capacity}
    (slice : SliceAt (τ := τ) layout memory frame base value)
    (first last : Nat) (bounds : SliceOk value.length first last) :
    SliceAt (τ := τ) layout memory frame (base + first * valueWords τ) (value.subslice first last bounds) := by
  intro index
  have seen : first + index.val < value.length := by
    have within := index.isLt
    have ordered := bounds.1
    have high := bounds.2
    change index.val < last - first at within
    omega
  have stored := slice ⟨first + index.val, seen⟩
  simpa only [BoundedSlice.subslice, arrSliceValue, Nat.add_mul, Nat.add_assoc] using stored

/-- A write outside the visible span preserves the saved slice in its
    original storage, including every word of aggregate elements. -/
theorem SliceAt.write_slot [Kern] {D : Deklaration} {layout : Lay D}
    {memory : Runner.Mem} {frame : Runner.W} {base capacity slots destination : Nat}
    {τ : Ty} {value : BoundedSlice (Wert D τ) capacity}
    (slice : SliceAt (τ := τ) layout memory frame base value)
    (room : frame.toNat + 8 * slots ≤ 2 ^ 64)
    (fits : base + value.length * valueWords τ ≤ slots)
    (inside : destination < slots)
    (apart : destination < base ∨ base + value.length * valueWords τ ≤ destination)
    (word : Runner.W) :
    SliceAt (τ := τ) layout
      (Runner.Mem.write memory (slot frame (BitVec.ofNat 64 destination)) 8 word.toNat) frame base value := by
  intro index
  have elementEnd : base + index.val * valueWords τ + valueWords τ ≤ base + value.length * valueWords τ := by
    have width := Nat.mul_le_mul_right (valueWords τ) (Nat.succ_le_of_lt index.isLt)
    rw [Nat.succ_mul] at width
    omega
  apply (slice index).write_slot room (elementEnd.trans fits) inside _ word
  rcases apart with before | after
  · exact Or.inl (Nat.lt_of_lt_of_le before (Nat.le_add_right _ _))
  · exact Or.inr (elementEnd.trans after)

/-- A substring of a long string reads its exact byte at the translated
    position in the existing storage, after the source length word. -/
theorem ValueAt.string_slice_byte [Kern] {D : Deklaration} {layout : Lay D} {memory : Runner.Mem} {frame : Runner.W}
    {base capacity : Nat} {value : Wert D (.str capacity)} (long : 2 ≤ capacity)
    (input : ValueAt layout memory frame base (.str capacity) value)
    (first last : Nat) (bounds : SliceOk value.1.length first last) (index : Fin (last - first)) :
    let result := strBoundedSliceValue value first last bounds
    let byte := result.1[index.val]'(by rw [(strBoundedSliceValue_exact value first last bounds).2]; exact index.isLt)
    memory.rd64 (slot frame (BitVec.ofNat 64 (base + 1 + (first + index.val)))) =
      some (BitVec.ofInt 64 byte.n) := by
  have inside : first + index.val < value.1.length := by
    have ordered := bounds.1
    have within := bounds.2
    have valid := index.isLt
    omega
  have within := inside.trans_le value.2
  have span := stringSpan_bytes long (Nat.le_refl capacity) value value.2 input
  have present : first + index.val < (stringBytes capacity value.1).length := by
    rwa [stringBytes_length value.1 value.2]
  have word := stringBytes_get value.1 value.2 (first + index.val) within
  rw [List.getElem?_eq_getElem present, List.getElem?_eq_getElem inside, Option.getD_some] at word
  dsimp only
  rw [span _ present, Option.some.inj word, strBoundedSliceValue_byte value first last bounds index]

/-- The visible bytes of a long runtime substring already occupy one
    contiguous span. The descriptor's length uses the actual byte count. -/
theorem ValueAt.string_slice_view [Kern] {D : Deklaration} {layout : Lay D}
    {memory : Runner.Mem} {frame : Runner.W} {base capacity : Nat}
    {value : Wert D (.str capacity)} (long : 2 ≤ capacity)
    (input : ValueAt layout memory frame base (.str capacity) value)
    (first last : Nat) (bounds : SliceOk value.1.length first last) :
    let slice := strBoundedSliceValue value first last bounds
    WordsAt memory frame (base + 1 + first) (slice.1.map fun byte => BitVec.ofInt 64 byte.n) := by
  intro result i present
  have length := (strBoundedSliceValue_exact value first last bounds).2
  have valid : i < last - first := by simpa only [List.length_map, result, length] using present
  have read := input.string_slice_byte long first last bounds ⟨i, valid⟩
  simpa only [Nat.add_assoc, List.getElem_map, result] using read

/-- The emitted length observation yields the actual length of the
    runtime slice, using the ordinary checked integer subtraction. -/
theorem lowE_runtimeSliceLength_ok [Kern] {D : Deklaration} {L : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {capacity : Nat}
    {firstLo firstHi lastLo lastHi : Int}
    (array : Wert D (.arr τ capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    {world : World D} {env : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat} {code : List II}
    (memory : ∀ m, W m → WeltAt m L world) (layout : LayIn L)
    (made : lowE (currentOld := true) L (reserved := reserved) (.sub finish begin) d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code env W reserved) :
    let first := eval world begin world env
    let last := eval world finish world env
    let result := eval world (.sub finish begin) world env
    ∃ valid : SliceOk capacity first.n.toNat last.n.toNat,
      result.n = ((BoundedSlice.ofArray array first.n.toNat last.n.toNat valid).length : Int) ∧
        ValueOk L m pc fp K d code (.int (lastLo - firstHi) (lastHi - firstLo)) result := by
  obtain ⟨valid, length⟩ := eval_localArraySliceLength array begin finish bounds world world env
  exact ⟨valid, length, lowE_ok (same := fun _ => rfl) world world memory layout _ d code top made fits m pc env pre⟩

/-- Stage 0's actual expression code returns the selected element of the
    runtime slice. The generated term accesses the original array through
    the already verified array indexing path. -/
theorem lowE_runtimeSliceIndex_ok [Kern] {D : Deklaration} {L : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {capacity : Nat}
    {firstLo firstHi lastLo lastHi indexLo indexHi : Int}
    (base : Expr D Γ Λ (.arr τ capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi)) (position : Expr D Γ Λ (.int indexLo indexHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (indexBounds : 0 ≤ indexLo ∧ indexHi < lastLo - firstHi)
    {world : World D} {env : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat} {code : List II}
    (memory : ∀ m, W m → WeltAt m L world) (layout : LayIn L)
    (made : lowE (currentOld := true) L (reserved := reserved)
      (.arrGet base (.widen (by omega) (by
        have low := (eval world finish world env).lo_le
        have high := (eval world finish world env).le_hi
        omega) (.add begin position))) d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code env W reserved) :
    let first := eval world begin world env
    let last := eval world finish world env
    let index := eval world position world env
    ∃ valid : SliceOk capacity first.n.toNat last.n.toNat,
      ∃ inside : index.n.toNat < last.n.toNat - first.n.toNat,
        ValueOk L m pc fp K d code τ
          ((BoundedSlice.ofArray (eval world base world env) first.n.toNat last.n.toNat valid).get
            ⟨index.n.toNat, inside⟩) := by
  obtain ⟨valid, inside, meaning⟩ :=
    eval_localArraySliceIndex base begin finish position bounds indexBounds world world env
  have execution :=
    lowE_ok (same := fun _ => rfl) world world memory layout _ d code top made fits m pc env pre
  exact ⟨valid, inside, meaning ▸ execution⟩

/-- After the signed bounds check the endpoints may still have overlapping
    static intervals. The two output words are the original start and the
    evaluated difference, independent of the backing aggregate type. -/
def runtimeSliceDescriptor {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {firstLo firstHi lastLo lastHi : Int}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi)) :
    Expr D Γ Λ (.prod 0 [.int firstLo firstHi, .int (lastLo - firstHi) (lastHi - firstLo)]) :=
  .prod 0 (.cons (.var first) (.cons (.sub (.var last) (.var first)) .nil))

/-- The ordinary expression emitter writes an exact descriptor even
    when only a runtime check establishes the relation between the
    two endpoint values. The output contains no copied element. -/
theorem runtimeSliceDescriptor_ok [Kern] {D : Deklaration} {layout : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {firstLo firstHi lastLo lastHi : Int} {length : Nat}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (firstFits : -(2 ^ 63) ≤ firstLo ∧ firstHi < 2 ^ 63)
    (differenceFits : -(2 ^ 63) ≤ lastLo - firstHi ∧ lastHi - firstLo < 2 ^ 63)
    {world : World D} {env : Env D Γ}
    (valid : SignedSliceOk length (env.get first).n (env.get last).n)
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K d top reserved : Nat} {code : List II}
    (worldAt : ∀ m, W m → WeltAt m layout world) (layoutIn : LayIn layout)
    (made : lowE (currentOld := true) layout (reserved := reserved)
      (runtimeSliceDescriptor (Λ := Λ) first last) d = some (code, top))
    (fits : top ≤ K) (pre : Pre layout m pc fp K d code env W reserved) :
    ∃ bounds : SliceOk length (env.get first).n.toNat (env.get last).n.toNat,
      let view := ArraySliceView.ofEndpoints (env.get first).n.toNat (env.get last).n.toNat bounds
      Executes m pc fp K d code (fun after => WordsAt after fp d (sliceDescriptorWords view)) := by
  obtain ⟨nonnegative, ordered, within⟩ := valid
  have bounds : SliceOk length (env.get first).n.toNat (env.get last).n.toNat := ⟨by omega, by omega⟩
  let view := ArraySliceView.ofEndpoints (env.get first).n.toNat (env.get last).n.toNat bounds
  let expression := runtimeSliceDescriptor (D := D) (Λ := Λ) first last
  have offset : BitVec.ofInt 64 (env.get first).n = BitVec.ofNat 64 view.offset := by
    change BitVec.ofInt 64 (env.get first).n = BitVec.ofNat 64 (env.get first).n.toNat
    simpa only [BitVec.ofInt_natCast] using
      congrArg (BitVec.ofInt 64) (Int.toNat_of_nonneg nonnegative).symm
  have exactLength : (((env.get last).n.toNat - (env.get first).n.toNat : Nat) : Int) =
      (env.get last).n - (env.get first).n := by omega
  have lengthWord : BitVec.ofInt 64 ((env.get last).n - (env.get first).n) = BitVec.ofNat 64 view.length := by
    rw [← exactLength, BitVec.ofInt_natCast]
    rfl
  have firstWidth := integerWords_word firstFits.1 firstFits.2
  have diffWidth := integerWords_word differenceFits.1 differenceFits.2
  have encoding : encodeWords layout _ (eval world expression world env) = sliceDescriptorWords view := by
    simp only [expression, runtimeSliceDescriptor, eval, evalProd, encodeWords, encodeProductFields,
      reduceCtorEq, ite_false, ProdVal.hd, ProdVal.tl, firstWidth, diffWidth, integerEncoding,
      List.cons_append, List.nil_append, Zahl.sub]
    change [BitVec.ofInt 64 (env.get first).n, BitVec.ofInt 64 ((env.get last).n - (env.get first).n)] =
      [BitVec.ofNat 64 view.offset, BitVec.ofNat 64 view.length]
    rw [offset, lengthWord]
  obtain ⟨after, run, confined, stored⟩ :=
    lowE_ok (same := fun _ => rfl) world world worldAt layoutIn expression d code top made fits m pc env pre
  exact ⟨bounds, after, run, confined, encoding ▸ stored.2⟩

/-- Select one element of a checked runtime view. The address is computed
    from the saved offset and the requested index in the original frame.
    Only the selected element is loaded into the expression result. -/
theorem runtimeSliceElement_ok [Kern] {D : Deklaration} {layout : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {capacity : Nat} {view : ArraySliceView capacity}
    {offsetLo offsetHi indexLo indexHi : Int}
    (offset : Var Γ (.int offsetLo offsetHi)) (index : Var Γ (.int indexLo indexHi))
    {world : World D} {env : Env D Γ}
    (offsetExact : (env.get offset).n = (view.offset : Int))
    (inView : 0 ≤ (env.get index).n ∧ (env.get index).n.toNat < view.length)
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K d base top reserved : Nat} {indexCode : List II} {array : Wert D (.arr τ capacity)}
    (worldAt : ∀ m, W m → WeltAt m layout world) (layoutIn : LayIn layout)
    (backing : ValueAt layout m fp base (.arr τ capacity) array)
    (apart : base + capacity * valueWords τ ≤ d)
    (scratch : d + valueWords τ + 1 < K) (width : 8 * valueWords τ < 2 ^ 31)
    (made : lowE (currentOld := true) layout (reserved := reserved)
      (.add (.var offset) (.var index) : Expr D Γ Λ _) (d + valueWords τ) = some (indexCode, top))
    (fits : top ≤ K) :
    let ptr := d + valueWords τ
    let select := selectFrameSpan (valueWords τ) base d ptr (ptr + 1)
    Pre layout m pc fp K ptr (indexCode ++ select) env W reserved →
      ValueOk layout m pc fp K d (indexCode ++ select) τ
        (view.read array ⟨(env.get index).n.toNat, inView.2⟩) := by
  intro ptr select pre
  let relative : Fin view.length := ⟨(env.get index).n.toNat, inView.2⟩
  let absolute := view.offset + relative.val
  have bound : absolute < capacity := by
    have inside := relative.isLt
    have available := view.fits
    dsimp only [absolute]
    omega
  have within : base + (absolute + 1) * valueWords τ ≤ d := by
    have indexFits : absolute + 1 ≤ capacity := bound
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right (valueWords τ) indexFits) base).trans apart
  have withinWords : base + absolute * valueWords τ + valueWords τ ≤ d := by
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using within
  let value := view.read array relative
  have original : ValueAt layout m fp (base + absolute * valueWords τ) τ value := by
    simpa only [absolute, value, Nat.add_mul, Nat.add_assoc] using backing.slice_element view relative
  let expression : Expr D Γ Λ (.int (offsetLo + indexLo) (offsetHi + indexHi)) := .add (.var offset) (.var index)
  obtain ⟨middle, calculated, preserved, stored⟩ :=
    lowE_ok (same := fun _ => rfl) world world worldAt layoutIn expression ptr indexCode top made fits m pc env pre.left
  obtain ⟨word, readWord, encoded⟩ := stored.word _ _ trivial
  change word = BitVec.ofInt 64 ((env.get offset).n + (env.get index).n) at encoded
  have exactIndex : (absolute : Int) = (env.get offset).n + (env.get index).n := by
    simp only [absolute, relative, Int.natCast_add, offsetExact, Int.toNat_of_nonneg inView.1]
  have indexWord : middle.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 absolute) := by
    rwa [encoded, ← exactIndex, BitVec.ofInt_natCast] at readWord
  have ptrFits : ptr ≤ K := by dsimp only [ptr]; omega
  have source := original.agree_low preserved pre.frame.room (withinWords.trans (Nat.le_add_right _ _)) ptrFits
  have tail := pre.next preserved (Nat.le_refl _) ptrFits
  obtain ⟨final, loaded, changed, selected⟩ :=
    selectFrameSpan_checked_ok (ptr := ptr) (tmp := ptr + 1) (dst := d) (index := absolute)
      (within.trans (Nat.le_add_right _ _)) (.inr within) (Nat.le_refl _) (by omega) scratch width
      indexWord source tail
  refine ⟨final, ?_, (preserved.mono (Nat.le_add_right _ _)).trans changed, selected⟩
  simpa only [List.length_append, pc_add] using calculated.trans loaded

/-- The original encoding determines how to read a byte. The short case
    keeps its packed source word and never addresses an adjacent word. -/
def readStringSliceByte (memory : Runner.Mem) (frame : Runner.W) (base capacity offset index : Nat) :
    Option Runner.W :=
  if capacity ≤ 1 then
    if offset + index = 0 then
      (memory.rd64 (slot frame (BitVec.ofNat 64 base))).map (fun word => word &&& 255)
    else none
  else memory.rd64 (slot frame (BitVec.ofNat 64 (base + 1 + (offset + index))))

/-- The same view semantics apply to both packed and word-per-byte
    backing values. Reading a visible byte never needs a new backing span. -/
theorem ValueAt.string_slice_read [Kern] {D : Deklaration} {layout : Lay D}
    {memory : Runner.Mem} {frame : Runner.W} {base capacity : Nat}
    {value : Wert D (.str capacity)} (backing : ValueAt layout memory frame base (.str capacity) value)
    (first last : Nat) (bounds : SliceOk value.1.length first last)
    (index : Fin (last - first)) :
    let result := strBoundedSliceValue value first last bounds
    let byte := result.1[index.val]'(by rw [(strBoundedSliceValue_exact value first last bounds).2]; exact index.isLt)
    readStringSliceByte memory frame base capacity first index.val = some (BitVec.ofInt 64 byte.n) := by
  intro result byte
  by_cases packed : capacity ≤ 1
  · have inside : first + index.val < value.1.length := by
      have selected := index.isLt
      obtain ⟨ordered, within⟩ := bounds
      omega
    have zero : first + index.val = 0 := by
      have capacityBound := value.2
      omega
    have stored := backing.2 0 (by rw [encodeWords_length]; exact valueWords_pos _)
    simp only [encodeWords, ite_eq_left packed, List.getElem_cons_zero, Nat.add_zero] at stored
    have sourceByte : strGetW value 0 = value.1[first + index.val] := by
      simp only [strGetW, Int.le_refl, ite_true, Int.toNat_zero]
      rw [← zero, List.getElem?_eq_getElem inside, Option.getD_some]
    have same : byte = value.1[first + index.val] :=
      strBoundedSliceValue_byte value first last bounds index
    simp only [readStringSliceByte, ite_eq_left packed, ite_eq_left zero, stored, Option.map_some,
      strN_byte value packed, sourceByte, same]
  · simp only [readStringSliceByte, ite_eq_right packed]
    exact backing.string_slice_byte (by omega) first last bounds index

/-- Runtime descriptor emission preserves and reuses the exact
    backing string, with both physical string encodings. -/
theorem runtimeStringSliceDescriptor_ok [Kern] {D : Deklaration} {layout : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {capacity : Nat}
    {firstLo firstHi lastLo lastHi : Int}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (firstFits : -(2 ^ 63) ≤ firstLo ∧ firstHi < 2 ^ 63)
    (differenceFits : -(2 ^ 63) ≤ lastLo - firstHi ∧ lastHi - firstLo < 2 ^ 63)
    (value : Wert D (.str capacity)) (sized : capacity < 2 ^ 64)
    {world : World D} {env : Env D Γ}
    (valid : SignedSliceOk value.1.length (env.get first).n (env.get last).n)
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K d base top reserved : Nat} {code : List II}
    (worldAt : ∀ m, W m → WeltAt m layout world) (layoutIn : LayIn layout)
    (backing : ValueAt layout m fp base (.str capacity) value) (below : base + valueWords (.str capacity) ≤ d)
    (made : lowE (currentOld := true) layout (reserved := reserved)
      (runtimeSliceDescriptor (Λ := Λ) first last) d = some (code, top))
    (fits : top ≤ K) (pre : Pre layout m pc fp K d code env W reserved) :
    ∃ bounds : SliceOk value.1.length (env.get first).n.toNat (env.get last).n.toNat,
      let view := ArraySliceView.ofEndpoints (env.get first).n.toNat (env.get last).n.toNat bounds
      let result := strBoundedSliceValue value (env.get first).n.toNat (env.get last).n.toNat bounds
      Executes m pc fp K d code (fun after => readSliceDescriptor after fp d value.1.length = some view ∧
        ∀ index : Fin (view.length),
          let byte := result.1[index.val]'(by
            rw [(strBoundedSliceValue_exact _ _ _ bounds).2]
            exact index.isLt)
          readStringSliceByte after fp base capacity view.offset index.val = some (BitVec.ofInt 64 byte.n)) := by
  obtain ⟨bounds, after, run, confined, words⟩ := runtimeSliceDescriptor_ok first last firstFits differenceFits valid
    worldAt layoutIn made fits pre
  let view := ArraySliceView.ofEndpoints (env.get first).n.toNat (env.get last).n.toNat bounds
  have inFrame : d ≤ K := (lowE_top (runtimeSliceDescriptor first last) d code top made).le.trans fits
  have preserved := backing.agree_low confined pre.frame.room below inFrame
  exact ⟨bounds, after, run, confined, readSliceDescriptor_exact view (value.2.trans_lt sized) words,
    preserved.string_slice_read _ _ bounds⟩

end Gabbro.Stage0.Senke
