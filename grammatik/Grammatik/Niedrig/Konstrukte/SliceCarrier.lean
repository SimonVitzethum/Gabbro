module

public import Grammatik.Niedrig.Konstrukte.Schnitt
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- The logical G record keeps the original backing value. Its visible
    extent is the checked runtime length; the original capacity bounds
    the descriptor fields. The backend can retain the backing allocation. -/
def sliceCarrierType (identity capacity : Nat) (backing : Ty) : Ty :=
  .prod identity [.int 0 capacity, .int 0 capacity, backing]

def sliceCarrierExpr (identity : Nat) {capacity : Nat} {backing : Ty}
    (offset length : Expr D Γ Λ (.int 0 capacity)) (original : Expr D Γ Λ backing) :
    Expr D Γ Λ (sliceCarrierType identity capacity backing) :=
  .prod identity (.cons offset (.cons length (.cons original .nil)))

theorem sliceCarrierExpr_eval (identity : Nat) {capacity : Nat} {backing : Ty}
    (offset length : Expr D Γ Λ (.int 0 capacity)) (original : Expr D Γ Λ backing)
    (initial world : World D) (env : Env D Γ) :
    eval initial (sliceCarrierExpr identity offset length original) world env =
      (eval initial offset world env, eval initial length world env, eval initial original world env, ()) :=
  rfl

theorem sliceCarrierExpr_reads (identity : Nat) {capacity : Nat} {backing : Ty}
    (offset length : Expr D Γ Λ (.int 0 capacity)) (original : Expr D Γ Λ backing) :
    (sliceCarrierExpr identity offset length original).orte = offset.orte ++ length.orte ++ original.orte := by
  simp only [sliceCarrierExpr, Expr.orte, Args.orte, List.append_nil, List.append_assoc]

/-- Construct the ordinary product from a checked range and the same
    original value. No element beyond the range becomes observable. -/
def packSliceCarrier (identity : Nat) {capacity : Nat} {backing : Ty}
    (view : ArraySliceView capacity) (source : Wert D backing) :
    Wert D (sliceCarrierType identity capacity backing) :=
  (⟨view.offset, Int.natCast_nonneg _, by have fits := view.fits; omega⟩,
    ⟨view.length, Int.natCast_nonneg _, by have fits := view.fits; omega⟩, source, ())

/-- Pack the exact runtime endpoints in the ordinary G product. The
    endpoints are already local and the backing is evaluated once. -/
def rangeCarrierExpr (identity : Nat) {capacity : Nat} {backing : Ty}
    {firstLo firstHi lastLo lastHi : Int}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (source : Expr D Γ Λ backing)
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastLo ≤ lastHi ∧ lastHi ≤ capacity) :
    Expr D Γ Λ (sliceCarrierType identity capacity backing) :=
  sliceCarrierExpr identity
    (.widen bounds.1 (by omega) (.var first))
    (.widen (by omega) (by omega) (.sub (.var last) (.var first))) source

theorem rangeCarrierExpr_reads (identity : Nat) {capacity : Nat} {backing : Ty}
    {firstLo firstHi lastLo lastHi : Int}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (source : Expr D Γ Λ backing)
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastLo ≤ lastHi ∧ lastHi ≤ capacity) :
    (rangeCarrierExpr identity first last source bounds).orte = source.orte := by
  simp only [rangeCarrierExpr, sliceCarrierExpr_reads, Expr.orte, List.nil_append]

theorem rangeCarrierExpr_eval (identity : Nat) {capacity : Nat} {backing : Ty}
    {firstLo firstHi lastLo lastHi : Int}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (source : Expr D Γ Λ backing)
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastLo ≤ lastHi ∧ lastHi ≤ capacity)
    (entry world : World D) (env : Env D Γ) :
    ∃ exact : SliceOk capacity (env.get first).n.toNat (env.get last).n.toNat,
      eval entry (rangeCarrierExpr identity first last source bounds) world env =
        packSliceCarrier identity (ArraySliceView.ofEndpoints _ _ exact) (eval entry source world env) := by
  have firstLow := (env.get first).lo_le
  have firstHigh := (env.get first).le_hi
  have lastLow := (env.get last).lo_le
  have lastHigh := (env.get last).le_hi
  let exactBounds : SliceOk capacity (env.get first).n.toNat (env.get last).n.toNat :=
    ⟨by omega, by omega⟩
  refine ⟨exactBounds, ?_⟩
  rw [rangeCarrierExpr, sliceCarrierExpr_eval]
  apply Prod.ext
  · apply zahl_ext
    change (env.get first).n = ↑(env.get first).n.toNat
    omega
  · apply Prod.ext
    · apply zahl_ext
      change (env.get last).n - (env.get first).n =
        ↑((env.get last).n.toNat - (env.get first).n.toNat)
      omega
    · rfl

def decodeArrayCarrier {identity capacity : Nat} {τ : Ty}
    (stored : Wert D (sliceCarrierType identity capacity (.arr τ capacity))) :
    Option (BoundedSlice (Wert D τ) capacity) :=
  let offset := stored.1.n.toNat
  let length := stored.2.1.n.toNat
  if fits : offset + length ≤ capacity then
    some ((ArraySliceView.mk offset length fits).value stored.2.2.1)
  else none

theorem decodeArrayCarrier_pack (identity : Nat) {capacity : Nat} {τ : Ty}
    (view : ArraySliceView capacity) (source : Wert D (.arr τ capacity)) :
    decodeArrayCarrier (D := D) (identity := identity) (τ := τ) (capacity := capacity)
      (packSliceCarrier identity view source) = some (view.value source) := by
  change (if fits : view.offset + view.length ≤ capacity then
    some ((ArraySliceView.mk view.offset view.length fits).value source) else none) = _
  rw [dite_eq_left view.fits]

/-- The typed G construction decodes directly to the bounded array
    value at the exact two runtime endpoints. -/
theorem rangeArrayCarrierExpr_exact (identity : Nat) {capacity : Nat} {τ : Ty}
    {firstLo firstHi lastLo lastHi : Int}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (array : Expr D Γ Λ (.arr τ capacity))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastLo ≤ lastHi ∧ lastHi ≤ capacity)
    (entry world : World D) (env : Env D Γ) :
    ∃ exact : SliceOk capacity (env.get first).n.toNat (env.get last).n.toNat,
      decodeArrayCarrier (D := D) (identity := identity) (τ := τ) (capacity := capacity)
        (eval entry (rangeCarrierExpr identity first last array bounds) world env) =
      some (BoundedSlice.ofArray (eval entry array world env) _ _ exact) := by
  obtain ⟨valid, packed⟩ := rangeCarrierExpr_eval identity first last array bounds entry world env
  refine ⟨valid, ?_⟩
  rw [packed]
  exact decodeArrayCarrier_pack identity (ArraySliceView.ofEndpoints _ _ valid) _

/-- The typed carrier accepts both endpoint intervals in a single
    context with an arbitrary array and independently varying bounds. -/
theorem rangeArrayCarrierExpr_erfuellbar (identity : Nat) {capacity : Nat} {τ : Ty}
    (enough : 4 ≤ capacity) (array : Wert D (.arr τ capacity))
    (first : Zahl 0 1) (last : Zahl 3 4) (entry world : World D) :
    let context := [Ty.int 0 1, Ty.int 3 4, Ty.arr τ capacity]
    let env : Env D context := .cons first (.cons last (.cons array .nil))
    let source : Expr D context Λ (.arr τ capacity) := .var (.there (.there .here))
    let carrier := rangeCarrierExpr identity .here (.there .here) source
      ⟨by decide, by decide, by decide, by omega⟩
    ∃ valid : SliceOk capacity first.n.toNat last.n.toNat,
      decodeArrayCarrier (D := D) (identity := identity) (τ := τ) (capacity := capacity)
        (eval entry carrier world env) = some (BoundedSlice.ofArray array _ _ valid) := by
  exact rangeArrayCarrierExpr_exact identity (capacity := capacity)
    (firstLo := 0) (firstHi := 1) (lastLo := 3) (lastHi := 4) .here (.there .here) _
    ⟨by decide, by decide, by decide, by omega⟩ entry world _

/-- String offsets use byte coordinates. The actual backing length
    still controls admission even when its capacity is larger. -/
def decodeStringCarrier {identity capacity : Nat}
    (stored : Wert D (sliceCarrierType identity capacity (.str capacity))) :
    Option (Wert D (.str capacity)) :=
  let source := stored.2.2.1
  let offset := stored.1.n.toNat
  let length := stored.2.1.n.toNat
  if fits : offset + length ≤ source.1.length then
    some (strBoundedSliceValue source offset (offset + length) ⟨Nat.le_add_right _ _, fits⟩)
  else none

theorem decodeStringCarrier_pack (identity : Nat) {capacity : Nat}
    (view : ArraySliceView capacity) (source : Wert D (.str capacity))
    (present : view.offset + view.length ≤ source.1.length) :
    decodeStringCarrier (D := D) (identity := identity) (capacity := capacity)
      (packSliceCarrier identity view source) =
        some (strBoundedSliceValue source view.offset (view.offset + view.length)
          ⟨Nat.le_add_right _ _, present⟩) := by
  change (if fits : view.offset + view.length ≤ source.1.length then
    some (strBoundedSliceValue source view.offset (view.offset + view.length)
      ⟨Nat.le_add_right _ _, fits⟩) else none) = _
  rw [dite_eq_left present]

/-- A checked typed string carrier denotes the precise substring of the
    evaluated backing value. Its maximum capacity alone cannot justify
    either endpoint. -/
theorem rangeStringCarrierExpr_exact (identity : Nat) {capacity : Nat}
    {firstLo firstHi lastLo lastHi : Int}
    (first : Var Γ (.int firstLo firstHi)) (last : Var Γ (.int lastLo lastHi))
    (string : Expr D Γ Λ (.str capacity))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastLo ≤ lastHi ∧ lastHi ≤ capacity)
    (entry world : World D) (env : Env D Γ)
    (present : (env.get last).n ≤ (eval entry string world env).1.length) :
    checkStringSlice (eval entry string world env) (env.get first).n (env.get last).n =
      decodeStringCarrier (D := D) (identity := identity) (capacity := capacity)
        (eval entry (rangeCarrierExpr identity first last string bounds) world env) := by
  obtain ⟨valid, packed⟩ := rangeCarrierExpr_eval identity first last string bounds entry world env
  have low := (env.get first).lo_le
  have high := (env.get first).le_hi
  have next := (env.get last).lo_le
  have accepted : SignedSliceOk (eval entry string world env).1.length
      (env.get first).n (env.get last).n := ⟨by omega, by omega, present⟩
  have endPosition : (env.get first).n.toNat +
      ((env.get last).n.toNat - (env.get first).n.toNat) = (env.get last).n.toNat := by
    have ordered := valid.1
    omega
  rw [packed, decodeStringCarrier_pack identity _ _ (by
    change (env.get first).n.toNat + ((env.get last).n.toNat - (env.get first).n.toNat) ≤ _
    rw [endPosition]
    omega)]
  simp only [checkStringSlice, dite_eq_left accepted]
  apply congrArg some
  apply Subtype.ext
  simp only [strBoundedSliceValue, strSliceValue, ArraySliceView.ofEndpoints, endPosition]

theorem decodeStringCarrier_isSome {identity capacity : Nat}
    (stored : Wert D (sliceCarrierType identity capacity (.str capacity))) :
    (decodeStringCarrier (D := D) (identity := identity) (capacity := capacity) stored).isSome = true ↔
      stored.1.n.toNat + stored.2.1.n.toNat ≤ stored.2.2.1.val.length := by
  unfold decodeStringCarrier
  dsimp only
  by_cases fits : stored.1.n.toNat + stored.2.1.n.toNat ≤ stored.2.2.1.val.length
  · rw [dite_eq_left fits, Option.isSome_some]
    exact ⟨fun _ => fits, fun _ => rfl⟩
  · rw [dite_eq_right fits, Option.isSome_none]
    exact Iff.intro (fun impossible => Bool.noConfusion impossible) (fun yes => (fits yes).elim)

/-- The concrete carrier premises hold for every array and every
    half-open range, including an empty range at the end. -/
theorem arraySliceCarrier_erfuellbar (identity : Nat) {τ : Ty} {capacity : Nat}
    (source : Wert D (.arr τ capacity)) (begin finish : Nat) (valid : SliceOk capacity begin finish) :
    let view := ArraySliceView.ofEndpoints begin finish valid
    decodeArrayCarrier (D := D) (identity := identity) (τ := τ) (capacity := capacity)
      (packSliceCarrier identity view source) = some (BoundedSlice.ofArray source begin finish valid) :=
  decodeArrayCarrier_pack identity _ source

end Gabbro.Grammatik.LowLevel.Construct
