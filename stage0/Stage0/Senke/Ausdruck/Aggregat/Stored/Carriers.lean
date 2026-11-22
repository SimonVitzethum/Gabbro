module

public import Stage0.Senke.Ausdruck.Aggregat.Stored.Slices
public import Grammatik.Niedrig.Konstrukte.SliceCarrier

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.LowLevel.Construct Runner.IR

/-- The generated endpoint computation writes only the two descriptor
    words. The visible value decodes to the same logical G carrier and
    is still represented at the original array address. -/
theorem runtimeArraySliceCarrier_ok [Kern] {D : Deklaration} {layout : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {capacity : Nat}
    {firstLo firstHi lastLo lastHi : Int} (identity : Nat)
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (firstFits : -(2 ^ 63) ≤ firstLo ∧ firstHi < 2 ^ 63)
    (differenceFits : -(2 ^ 63) ≤ lastLo - firstHi ∧ lastHi - firstLo < 2 ^ 63)
    (sized : capacity < 2 ^ 64) {world : World D} {env : Env D Γ}
    (valid : SignedSliceOk capacity (env.get first).n (env.get last).n)
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K d base top reserved : Nat} {code : List II} (array : Wert D (.arr τ capacity))
    (worldAt : ∀ m, W m → WeltAt m layout world) (layoutIn : LayIn layout)
    (backing : ValueAt layout m fp base (.arr τ capacity) array)
    (below : base + valueWords (.arr τ capacity) ≤ d)
    (made : lowE (currentOld := true) layout (reserved := reserved)
      (runtimeSliceDescriptor (Λ := Λ) first last) d = some (code, top))
    (fits : top ≤ K) (pre : Pre layout m pc fp K d code env W reserved) :
    ∃ bounds : SliceOk capacity (env.get first).n.toNat (env.get last).n.toNat,
      let view := ArraySliceView.ofEndpoints (env.get first).n.toNat (env.get last).n.toNat bounds
      Executes m pc fp K d code (fun after =>
        readSliceDescriptor after fp d capacity = some view ∧
        decodeArrayCarrier (D := D) (identity := identity) (τ := τ) (capacity := capacity)
          (packSliceCarrier identity view array) = some (view.value array) ∧
        ValueAt layout after fp base (.arr τ capacity) array ∧
        SliceAt (τ := τ) layout after fp (base + view.offset * valueWords τ) (view.value array)) := by
  obtain ⟨bounds, after, run, confined, words⟩ := runtimeSliceDescriptor_ok first last firstFits differenceFits valid
    worldAt layoutIn made fits pre
  let view := ArraySliceView.ofEndpoints (env.get first).n.toNat (env.get last).n.toNat bounds
  have inFrame : d ≤ K := (lowE_top (runtimeSliceDescriptor first last) d code top made).le.trans fits
  have original := backing.agree_low confined pre.frame.room below inFrame
  obtain ⟨descriptor, elements⟩ := original.decode_slice_descriptor view sized words
  exact ⟨bounds, after, run, confined, descriptor, decodeArrayCarrier_pack identity view array, original, elements⟩

/-- A runtime substring decodes as the same logical G value under its
    declared capacity, while the executed descriptor is checked against
    the actual byte count of the backing string. -/
theorem runtimeStringSliceCarrier_ok [Kern] {D : Deklaration} {layout : Lay D}
    {Γ : Ctx} {Λ : List (Res D)} {capacity : Nat}
    {firstLo firstHi lastLo lastHi : Int} (identity : Nat)
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (firstFits : -(2 ^ 63) ≤ firstLo ∧ firstHi < 2 ^ 63)
    (differenceFits : -(2 ^ 63) ≤ lastLo - firstHi ∧ lastHi - firstLo < 2 ^ 63)
    (sized : capacity < 2 ^ 64) (source : Wert D (.str capacity))
    {world : World D} {env : Env D Γ}
    (valid : SignedSliceOk source.1.length (env.get first).n (env.get last).n)
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K d base top reserved : Nat} {code : List II}
    (worldAt : ∀ m, W m → WeltAt m layout world) (layoutIn : LayIn layout)
    (backing : ValueAt layout m fp base (.str capacity) source)
    (below : base + valueWords (.str capacity) ≤ d)
    (made : lowE (currentOld := true) layout (reserved := reserved)
      (runtimeSliceDescriptor (Λ := Λ) first last) d = some (code, top))
    (fits : top ≤ K) (pre : Pre layout m pc fp K d code env W reserved) :
    ∃ bounds : SliceOk source.1.length (env.get first).n.toNat (env.get last).n.toNat,
      let begin := (env.get first).n.toNat
      let finish := (env.get last).n.toNat
      let view := ArraySliceView.ofEndpoints begin finish bounds
      let carrier := ArraySliceView.ofEndpoints begin finish
        (⟨bounds.1, bounds.2.trans source.2⟩ : SliceOk capacity begin finish)
      let result := strBoundedSliceValue source begin finish bounds
      Executes m pc fp K d code (fun after =>
        readSliceDescriptor after fp d source.1.length = some view ∧
        decodeStringCarrier (D := D) (identity := identity) (capacity := capacity)
          (packSliceCarrier identity carrier source) = some result ∧
        ValueAt layout after fp base (.str capacity) source ∧
        ∀ index : Fin view.length,
          let byte := result.1[index.val]'(by
            rw [(strBoundedSliceValue_exact source begin finish bounds).2]
            exact index.isLt)
          readStringSliceByte after fp base capacity view.offset index.val = some (BitVec.ofInt 64 byte.n)) := by
  obtain ⟨bounds, after, run, confined, descriptor, bytes⟩ :=
    runtimeStringSliceDescriptor_ok first last firstFits differenceFits source sized valid
      worldAt layoutIn backing below made fits pre
  let begin := (env.get first).n.toNat
  let finish := (env.get last).n.toNat
  let carrier := ArraySliceView.ofEndpoints begin finish
    (⟨bounds.1, bounds.2.trans source.2⟩ : SliceOk capacity begin finish)
  have ends : carrier.offset + carrier.length = finish := Nat.add_sub_of_le bounds.1
  have inside : carrier.offset + carrier.length ≤ source.1.length := ends.trans_le bounds.2
  have decoded := decodeStringCarrier_pack identity carrier source inside
  have result : strBoundedSliceValue source carrier.offset (carrier.offset + carrier.length)
      ⟨Nat.le_add_right _ _, inside⟩ = strBoundedSliceValue source begin finish bounds := by
    have sameBytes : (strBoundedSliceValue source carrier.offset (carrier.offset + carrier.length)
        ⟨Nat.le_add_right _ _, inside⟩).1 = (strBoundedSliceValue source begin finish bounds).1 := by
      simp only [strBoundedSliceValue]
      change sliceValue source.1 begin (carrier.offset + carrier.length) = sliceValue source.1 begin finish
      rw [ends]
    exact Subtype.ext sameBytes
  have inFrame : d ≤ K := (lowE_top (runtimeSliceDescriptor first last) d code top made).le.trans fits
  exact ⟨bounds, after, run, confined, descriptor, decoded.trans (congrArg some result),
    backing.agree_low confined pre.frame.room below inFrame, bytes⟩

end Gabbro.Stage0.Senke
