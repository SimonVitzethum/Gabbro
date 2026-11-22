module

public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Span
public import Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices

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

/-- A substring of a long string reads its exact byte at the translated
    position in the existing storage, after the source length word. -/
theorem ValueAt.string_slice_byte {D : Deklaration} {layout : Lay D} {memory : Runner.Mem} {frame : Runner.W}
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

end Gabbro.Stage0.Senke
