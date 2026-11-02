/- Static encoding decomposition for typed product projection. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Product
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Copy
@[expose] public section

variable {currentOld : Bool}

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

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

/-- Project only the physical words; validity is a separate obligation. -/
theorem wordsAt_product_field {L : Lay D} {name : Nat} {fs : List Ty} {τ : Ty}
    {m : Runner.Mem} {fp : Runner.W} {d : Nat}
    (i : FieldAt fs τ) (v : ProdVal D.Fn D.passt fs)
    (input : WordsAt m fp d (encodeWords L (.prod name fs) v)) :
    WordsAt m fp (d + productOffset i) (encodeWords L τ (prodGetW i v)) := by
  obtain ⟨before, after, split, offset⟩ := encodeProduct_field_split L i v
  rw [split, wordsAt_append] at input
  have selected := (wordsAt_append (encodeWords L τ (prodGetW i v)) after).mp input.2
  simpa only [offset] using selected.1

/-- The field span fits whenever the operand reserves its complete value.
    `lowE_top` currently proves only `d < top`; the full operand bound
    must be established before product projection can be enabled. -/
theorem prodGet_fieldBound {name : Nat} {fs : List Ty} {τ : Ty}
    (i : FieldAt fs τ) {d top K : Nat}
    (operand : d + valueWords (.prod name fs) ≤ top) (hK : top ≤ K) :
    d + productOffset i + valueWords τ ≤ K := by
  have field := productOffset_bound i
  simp only [valueWords] at operand
  have width : productWords fs ≤ max 1 (productWords fs) := Nat.le_max_right _ _
  omega

/-- Static projection transport with a complete product reservation. -/
theorem prodGet_ok [Kern] {L : Lay D} {Γ : Ctx} {Λ : List (Res D)}
    {name : Nat} {fs : List Ty} {τ : Ty} (i : FieldAt fs τ)
    (v : Expr D Γ Λ (.prod name fs))
    {σ₀ σ : World D} {fp pc : Runner.W} {K d top reserved : Nat}
    {W : Runner.Mem → Prop} {ρ : Env D Γ} {c : List Runner.IR.II} {m : Runner.Mem}
    (ih : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) v d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved →
        ValueOk L m pc fp K d ca (.prod name fs) (eval σ₀ v σ ρ))
    (h : prodGetL (name := name) i d (lowE (currentOld := currentOld) L (reserved := reserved) v d) = some (c, top))
    (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c τ (prodGetW i (eval σ₀ v σ ρ)) := by
  simp only [prodGetL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cv, tv⟩, hv, rfl, rfl⟩ := h
  have operand : d + valueWords (.prod name fs) ≤ K :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hK
  have span := prodGet_fieldBound i operand (Nat.le_refl K)
  have htv : tv ≤ K :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hK
  obtain ⟨m1, run1, changed1, valid, words⟩ := ih cv tv hv htv m pc hp.left
  have tail := hp.next changed1 (Nat.le_refl d) (by omega)
  have selected : ValueAt L m1 fp (d + productOffset i) τ
      (prodGetW i (eval σ₀ v σ ρ)) :=
    ⟨ProdValid.field i _ valid, wordsAt_product_field i _ words⟩
  obtain ⟨m2, run2, changed2, result⟩ := copyValue_run tail.frame tail.small
    (by omega) span (Or.inl (Nat.le_add_right _ _)) tail.code
    (by simpa only [copyWords_length] using tail.far) selected
  refine ⟨m2, ?_, changed1.trans (changed2.mono (by omega)), result⟩
  simpa only [List.length_append, copyWords_length, pc_add] using run1.trans run2

end Gabbro.Stage0.Senke
