/- Static encoding decomposition for typed product projection. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Product
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- Static projection uses the shared forward copy, which permits overlapping
    spans when the destination precedes the source. -/
def prodGetL {fs : List Ty} {τ : Ty} (i : FieldAt fs τ) (d : Nat)
    (a : Option (List Runner.IR.II × Nat)) : Option (List Runner.IR.II × Nat) := do
  let ca ← a
  pure (ca.1 ++ copyWords (valueWords τ) d (d + productOffset i), ca.2)

/-- The selected field is a contiguous span at its statically computed offset. -/
theorem encodeProductFields_field_split (L : Lay D) {fs : List Ty} {τ : Ty}
    (i : FieldAt fs τ) (v : ProdVal D.Fn D.passt fs) :
    ∃ before after : List Runner.W,
      encodeProductFields L fs v = before ++ encodeWords L τ (prodGetW i v) ++ after ∧
      before.length = productOffset i := by
  induction i with
  | head =>
    exact ⟨[], encodeProductFields L _ (ProdVal.tl v), rfl, rfl⟩
  | @tail τ σ rest i ih =>
    obtain ⟨before, after, split, offset⟩ := ih (ProdVal.tl v)
    refine ⟨encodeWords L σ (ProdVal.hd v) ++ before, after, ?_, ?_⟩
    · simp only [encodeProductFields_cons, prodGetW]
      rw [split, List.append_assoc, List.append_assoc]
    · simp only [List.length_append, encodeWords_length, productOffset]
      rw [offset]

/-- A typed field guarantees that the empty-product marker is absent. -/
theorem encodeProduct_field_split (L : Lay D) {name : Nat} {fs : List Ty} {τ : Ty}
    (i : FieldAt fs τ) (v : ProdVal D.Fn D.passt fs) :
    ∃ before after : List Runner.W,
      encodeWords L (.prod name fs) v = before ++ encodeWords L τ (prodGetW i v) ++ after ∧
      before.length = productOffset i := by
  have nonempty : fs ≠ [] := by
    cases i <;> simp
  simpa only [encodeWords, encodeProduct, if_neg nonempty] using
    encodeProductFields_field_split L i v

/-- Project only the physical words; validity is a separate obligation.
    Product validity currently does not contain the validity of its fields. -/
theorem wordsAt_product_field {L : Lay D} {name : Nat} {fs : List Ty} {τ : Ty}
    {m : Runner.Mem} {fp : Runner.W} {d : Nat}
    (i : FieldAt fs τ) (v : ProdVal D.Fn D.passt fs)
    (input : WordsAt m fp d (encodeWords L (.prod name fs) v)) :
    WordsAt m fp (d + productOffset i) (encodeWords L τ (prodGetW i v)) := by
  obtain ⟨before, after, split, offset⟩ := encodeProduct_field_split L i v
  rw [split, wordsAt_append] at input
  have selected := (wordsAt_append (encodeWords L τ (prodGetW i v)) after).mp input.2
  simpa only [offset] using selected.1

end Gabbro.Stage0.Senke
