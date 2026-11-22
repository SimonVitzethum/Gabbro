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
  simp only [decodeArrayCarrier, packSliceCarrier, Int.toNat_natCast]
  rw [dif_pos view.fits]

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
  simp only [decodeStringCarrier, packSliceCarrier, Int.toNat_natCast]
  rw [dif_pos present]

theorem decodeStringCarrier_isSome {identity capacity : Nat}
    (stored : Wert D (sliceCarrierType identity capacity (.str capacity))) :
    (decodeStringCarrier (D := D) (identity := identity) (capacity := capacity) stored).isSome = true ↔
      stored.1.n.toNat + stored.2.1.n.toNat ≤ stored.2.2.1.val.length := by
  unfold decodeStringCarrier
  dsimp only
  by_cases fits : stored.1.n.toNat + stored.2.1.n.toNat ≤ stored.2.2.1.val.length
  · rw [dif_pos fits, Option.isSome_some]
    exact ⟨fun _ => fits, fun _ => rfl⟩
  · rw [dif_neg fits, Option.isSome_none]
    exact ⟨by decide, fun yes => (fits yes).elim⟩

/-- The concrete carrier premises hold for every array and every
    half-open range, including an empty range at the end. -/
theorem arraySliceCarrier_erfuellbar (identity : Nat) {τ : Ty} {capacity : Nat}
    (source : Wert D (.arr τ capacity)) (begin finish : Nat) (valid : SliceOk capacity begin finish) :
    let view := ArraySliceView.ofEndpoints begin finish valid
    decodeArrayCarrier (D := D) (identity := identity) (τ := τ) (capacity := capacity)
      (packSliceCarrier identity view source) = some (BoundedSlice.ofArray source begin finish valid) :=
  decodeArrayCarrier_pack identity _ source

end Gabbro.Grammatik.LowLevel.Construct
