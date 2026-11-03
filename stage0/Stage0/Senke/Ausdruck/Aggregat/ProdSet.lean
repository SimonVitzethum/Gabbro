/- Representation preservation for typed product replacement. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.ProdGet
@[expose] public section

variable {currentOld : Bool}

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Replacing one field preserves all product representation obligations. -/
theorem ProdValid.set {L : Lay D} {fs : List Ty} {σ : Ty}
    (i : FieldAt fs σ) (v : ProdVal D.Fn D.passt fs) (x : Wert D σ)
    (valid : ProdValid L fs v) (replacement : ValueValid L σ x) :
    ProdValid L fs (prodSetW i v x) := by
  induction i with
  | head => exact ⟨replacement, valid.2⟩
  | tail i ih => exact ⟨valid.1, ih (ProdVal.tl v) x valid.2 replacement⟩

/-- Replacement changes exactly the selected field's contiguous encoding. -/
theorem encodeProductFields_set_split (L : Lay D) {fs : List Ty} {σ : Ty}
    (i : FieldAt fs σ) (v : ProdVal D.Fn D.passt fs) (x : Wert D σ) :
    ∃ before after : List Runner.W,
      encodeProductFields L fs v = before ++ encodeWords L σ (prodGetW i v) ++ after ∧
      encodeProductFields L fs (prodSetW i v x) =
        before ++ encodeWords L σ x ++ after ∧
      before.length = productOffset i := by
  induction i with
  | head =>
    refine ⟨[], encodeProductFields L _ (ProdVal.tl v), ?_, ?_, rfl⟩
    · simp only [encodeProductFields_cons, prodGetW, List.nil_append]
    · simp only [prodSetW, encodeProductFields_cons, ProdVal.hd_pcons,
        ProdVal.tl_pcons, List.nil_append]
  | @tail σ τ rest i ih =>
    obtain ⟨before, after, old, updated, offset⟩ := ih (ProdVal.tl v) x
    refine ⟨encodeWords L τ (ProdVal.hd v) ++ before, after, ?_, ?_, ?_⟩
    · simp only [encodeProductFields_cons, prodGetW]
      rw [old]
      simp only [List.append_assoc]
    · simp only [prodSetW, encodeProductFields_cons, ProdVal.hd_pcons, ProdVal.tl_pcons]
      rw [updated]
      simp only [List.append_assoc]
    · simp only [List.length_append, encodeWords_length, productOffset]
      rw [offset]

/-- Exact field writes and preservation of the surrounding words implement replacement. -/
theorem wordsAt_prodSet {L : Lay D} {name : Nat} {fs : List Ty} {σ : Ty}
    {m3 m4 : Runner.Mem} {fp : Runner.W} {d ptr : Nat}
    (i : FieldAt fs σ) (v : ProdVal D.Fn D.passt fs) (x : Wert D σ)
    (kept : WordsAt m3 fp d (encodeWords L (.prod name fs) v))
    (written : WordsAt m4 fp (d + productOffset i) (encodeWords L σ x))
    (preserved : ∀ s, s < ptr →
      (s < d + productOffset i ∨ d + productOffset i + valueWords σ ≤ s) →
      m4.rd64 (slot fp (BitVec.ofNat 64 s)) = m3.rd64 (slot fp (BitVec.ofNat 64 s)))
    (fits : d + valueWords (.prod name fs) ≤ ptr) :
    WordsAt m4 fp d (encodeWords L (.prod name fs) (prodSetW i v x)) := by
  have nonempty : fs ≠ [] := by cases i <;> simp
  obtain ⟨before, after, old, updated, offset⟩ := encodeProductFields_set_split L i v x
  have old' : encodeWords L (.prod name fs) v =
      before ++ encodeWords L σ (prodGetW i v) ++ after := by
    erw [encodeWords_prod]
    simpa only [encodeProduct.eq_def, if_neg nonempty] using old
  have updated' : encodeWords L (.prod name fs) (prodSetW i v x) =
      before ++ encodeWords L σ x ++ after := by
    erw [encodeWords_prod]
    simpa only [encodeProduct.eq_def, if_neg nonempty] using updated
  have length := encodeWords_length L (.prod name fs) v
  rw [old'] at length
  simp only [List.length_append, encodeWords_length, offset] at length
  rw [old', wordsAt_append, wordsAt_append] at kept
  rw [updated', wordsAt_append, wordsAt_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k hk
    rw [preserved (d + k) (by omega) (Or.inl (by omega))]
    exact kept.1.1 k hk
  · simpa only [offset] using written
  · intro k hk
    have read := kept.2 k hk
    simp only [List.length_append, encodeWords_length, offset] at read ⊢
    rw [preserved (d + (productOffset i + valueWords σ) + k) (by omega) (Or.inr (by omega))]
    exact read

/-- Product replacement preserves the operand below the replacement scratch span. -/
theorem prodSet_ok [Kern] {L : Lay D} {Γ : Ctx} {Λ : List (Res D)}
    {name : Nat} {fs : List Ty} {τ : Ty} (i : FieldAt fs τ)
    (v : Expr D Γ Λ (.prod name fs)) (e : Expr D Γ Λ τ)
    {σ₀ σ : World D} {fp pc : Runner.W} {K d top reserved : Nat}
    {W : Runner.Mem → Prop} {ρ : Env D Γ} {c : List Runner.IR.II} {m : Runner.Mem}
    (ihv : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) v d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved →
        ValueOk L m pc fp K d ca (.prod name fs) (eval σ₀ v σ ρ))
    (ihe : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) e (d + valueWords (.prod name fs)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords (.prod name fs)) ca ρ W reserved →
        ValueOk L m pc fp K (d + valueWords (.prod name fs)) ca τ (eval σ₀ e σ ρ))
    (h : prodSetL (name := name) i d (lowE (currentOld := currentOld) L (reserved := reserved) v d)
      (lowE (currentOld := currentOld) L (reserved := reserved) e (d + valueWords (.prod name fs))) = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.prod name fs)
      (prodSetW i (eval σ₀ v σ ρ) (eval σ₀ e σ ρ)) := by
  simp only [prodSetL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cv, tv⟩, hv, ⟨ce, te⟩, he, rfl, rfl⟩ := h
  let src := d + valueWords (.prod name fs)
  have field := prodGet_fieldBound i (Nat.le_refl (d + valueWords (.prod name fs))) (Nat.le_refl _)
  have hp' : Pre L m pc fp K d
      (cv ++ (ce ++ copyWords (valueWords τ) (d + productOffset i) src)) ρ W reserved := by
    simpa only [src, List.append_assoc] using hp
  obtain ⟨m1, run1, changed1, product⟩ := ihv cv tv hv (by omega) m pc hp'.left
  have next1 := hp'.next changed1 (show d ≤ src by simp only [src]; omega) (show src ≤ K by simp only [src]; omega)
  obtain ⟨m2, run2, changed2, value⟩ := ihe ce te he (by omega) m1 _ next1.left
  have product2 := product.agree changed2 (hp.frame.agree changed1)
    (show d + valueWords (.prod name fs) ≤ src from Nat.le_refl _) (show src ≤ K by simp only [src]; omega)
  have tail := next1.next changed2 (Nat.le_refl src) (show src ≤ K by simp only [src]; omega)
  obtain ⟨m3, run3, changed3, written⟩ := copyValue_run tail.frame tail.small
    (by simp only [src] at *; omega) (by simp only [src] at *; omega)
    (Or.inl (by simp only [src]; omega)) tail.code
    (by simpa only [copyWords_length] using tail.far) value
  refine ⟨m3, ?_, changed1.trans ((changed2.mono (by simp only [src]; omega)).trans
    ((Agree.widen changed3 (by simp only [src] at *; omega)).mono (by omega))),
    ProdValid.set i _ _ product.1 value.1, ?_⟩
  · simpa only [src, List.length_append, copyWords_length, pc_add, List.append_assoc,
      Nat.add_assoc] using run1.trans (run2.trans run3)
  · exact wordsAt_prodSet i _ _ product2.2 written.2 (fun s hs outside => by
      rcases outside with below | above
      · exact agree_rd_low changed3 (by have := tail.frame.room; simp only [src] at *; omega) below (by simp only [src] at *; omega)
      · exact agree_rd_above changed3 tail.frame.room above (by simp only [src] at *; omega)) (Nat.le_refl _)

end Gabbro.Stage0.Senke
