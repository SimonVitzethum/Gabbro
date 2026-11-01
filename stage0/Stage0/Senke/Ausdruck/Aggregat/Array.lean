/- Array values occupy consecutive canonical element spans, including nested shapes. -/
module
public import Stage0.Senke.Ausdruck.Lesen
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
public import Stage0.Senke.Ausdruck.Quant.Selection
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Store
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {τ : Ty}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top reserved : Nat} {W : Runner.Mem → Prop}
variable {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem singleton_index (i : Zahl 0 ((1 : Int) - 1)) : i.fin (n := 1) = ⟨0, by decide⟩ := by
  apply Fin.ext
  have := i.lo_le
  have := i.le_hi
  simp only [Zahl.fin]
  omega

theorem arrNil_ok (h : lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.arrNil (τ := τ)) d = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.arr τ 0) (eval σ₀ (Expr.arrNil (Λ := Λ)) σ ρ) := by
  simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine Ok.value ?_ (by simp [valueWords])
  exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simpa [Enc] using hw

theorem arrCons_ok {n : Nat} (a : Expr D Γ Λ τ) (rest : Expr D Γ Λ (.arr τ n))
    (ih : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca τ (eval σ₀ a σ ρ))
    (iht : ∀ ca ta, lowE L (reserved := reserved) rest (d + valueWords τ) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords τ) ca ρ W reserved →
        ValueOk L m pc fp K (d + valueWords τ) ca (.arr τ n) (eval σ₀ rest σ ρ))
    (h : lowE L (reserved := reserved) (.arrCons a rest) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.arr τ (n + 1)) (eval σ₀ (.arrCons a rest) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    subst n
    obtain ⟨m', run, changed, valid, words⟩ := ih c top h hK m pc hp
    refine ⟨m', run, changed, ValueValid.arrCons valid (fun i => Fin.elim0 i), ?_⟩
    simpa only [eval, encodeWords_arrCons, ite_true, List.append_nil] using words
  · next nonempty =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, rfl, rfl⟩ := h
    have firstTop := lowE_top a d ca ta ha
    have tailTop := lowE_top rest (d + valueWords τ) cb tb hb
    obtain ⟨m1, run1, changed1, head⟩ := ih ca ta ha (by omega) m pc hp.left
    have next := hp.next changed1 (by omega : d ≤ d + valueWords τ) (by omega)
    obtain ⟨m2, run2, changed2, tail⟩ := iht cb tb hb (by omega) m1 _ next
    have head2 := head.agree changed2 (hp.frame.agree changed1) (Nat.le_refl _) (by omega)
    refine ⟨m2, ?_, changed1.trans (changed2.mono (by omega)),
      ValueValid.arrCons head2.1 tail.1, ?_⟩
    · simpa only [List.length_append, pc_add] using run1.trans run2
    · rw [show eval σ₀ (.arrCons a rest) σ ρ = arrConsW (eval σ₀ a σ ρ) (eval σ₀ rest σ ρ) from rfl,
        encodeWords_arrCons, if_neg nonempty, wordsAt_append]
      exact ⟨head2.2, by simpa only [encodeWords_length] using tail.2⟩

theorem arrGet_ok {n : Nat} (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n))
    (ih : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.arr τ n) (eval σ₀ a σ ρ))
    (ihi : ∀ ca ta, lowE L (reserved := reserved) i (d + valueWords (.arr τ n)) = some (ca, ta) →
      ta ≤ K → ∀ m pc, Pre L m pc fp K (d + valueWords (.arr τ n)) ca ρ W reserved →
        ValueOk L m pc fp K (d + valueWords (.arr τ n)) ca (.index n) (eval σ₀ i σ ρ))
    (h : lowE L (reserved := reserved) (.arrGet a i) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c τ (eval σ₀ (.arrGet a i) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    subst n
    obtain ⟨m', run, changed, valid, words⟩ := ih c top h hK m pc hp
    refine ⟨m', run, changed, valid _, ?_⟩
    change WordsAt m' fp d (encodeWords L τ ((eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin))
    rw [singleton_index (eval σ₀ i σ ρ)]
    simpa only [encodeWords, if_neg (by decide : ¬(1 : Nat) = 0),
      elementEncoding, List.append_nil] using words
  · simp only [arrGetL] at h
    split at h
    · next available =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, rfl, rfl⟩ := h
      let ptr := d + valueWords (.arr τ n)
      let j := (eval σ₀ i σ ρ).fin
      have sourceWidth : valueWords (.arr τ n) = n * valueWords τ := by
        have := valueWords_pos τ
        simp only [valueWords]
        rw [Nat.max_eq_right (by have := Nat.mul_pos available.1 (valueWords_pos τ); omega)]
      have sourceSpan : d + (j.val + 1) * valueWords τ ≤ ptr := by
        have bound : (j.val + 1) * valueWords τ ≤ n * valueWords τ :=
          Nat.mul_le_mul_right (valueWords τ) (by have := j.isLt; omega)
        dsimp only [ptr]
        rw [sourceWidth]
        omega
      have hp' : Pre L m pc fp K d
          (ca ++ (cb ++ selectFrameSpan (valueWords τ) d d ptr (ptr + 1))) ρ W reserved := by
        simpa only [ptr, List.append_assoc] using hp
      obtain ⟨m1, run1, changed1, array⟩ := ih ca ta ha (by omega) m pc hp'.left
      have next : Pre L m1 _ fp K ptr (cb ++ selectFrameSpan (valueWords τ) d d ptr (ptr + 1)) ρ W reserved :=
        hp'.next changed1 (by simp only [ptr]; omega) (by omega)
      obtain ⟨m2, run2, changed2, index⟩ := ihi cb tb hb (by omega) m1 _ next.left
      have source := array.agree changed2 (hp.frame.agree changed1) (by first | omega | (dsimp only [ptr]; omega)) (by omega)
      have selected := source.array_element j
      obtain ⟨word, read, encoded⟩ := ValueAt.word (.index n) _ trivial index
      change word = BitVec.ofInt 64 (eval σ₀ i σ ρ).n at encoded
      subst word
      have indexWord : m2.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 j.val) := by
        have nonnegative := (eval σ₀ i σ ρ).lo_le
        simpa only [j, Zahl.fin, BitVec.ofNat_eq_ofNat, ← BitVec.ofInt_natCast,
          Int.toNat_of_nonneg nonnegative] using read
      have tail := next.next changed2 (Nat.le_refl _) (by omega)
      obtain ⟨m3, run3, changed3, result⟩ := selectFrameSpan_ok sourceSpan (Nat.le_add_right _ _) (by omega)
        (by first | omega | (dsimp only [ptr]; omega)) available.2 indexWord selected tail
      refine ⟨m3, ?_, changed1.trans ((changed2.mono (by first | omega | (dsimp only [ptr]; omega))).trans changed3), result⟩
      simpa only [ptr, List.length_append, pc_add, List.append_assoc, Nat.add_assoc] using
        run1.trans (run2.trans run3)
    · cases h

theorem arrSet_ok {n : Nat} (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n)) (v : Expr D Γ Λ τ)
    (ih : ∀ ca ta, lowE L (reserved := reserved) v d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca τ (eval σ₀ v σ ρ))
    (iha : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.arr τ n) (eval σ₀ a σ ρ))
    (ihv : ∀ ca ta, lowE L (reserved := reserved) v (d + valueWords (.arr τ n)) = some (ca, ta) → ta ≤ K →
      ∀ m pc, Pre L m pc fp K (d + valueWords (.arr τ n)) ca ρ W reserved →
        ValueOk L m pc fp K (d + valueWords (.arr τ n)) ca τ (eval σ₀ v σ ρ))
    (ihi : ∀ ca ta, lowE L (reserved := reserved) i (d + valueWords (.arr τ n) + valueWords τ) = some (ca, ta) →
      ta ≤ K → ∀ m pc, Pre L m pc fp K (d + valueWords (.arr τ n) + valueWords τ) ca ρ W reserved →
        ValueOk L m pc fp K (d + valueWords (.arr τ n) + valueWords τ) ca (.index n) (eval σ₀ i σ ρ))
    (h : lowE L (reserved := reserved) (.arrSet a i v) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.arr τ n) (eval σ₀ (.arrSet a i v) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    subst n
    obtain ⟨m', run, changed, valid, words⟩ := ih c top h hK m pc hp
    have index0 : ∀ j : Fin 1, j = ⟨0, by decide⟩ := by
      intro j; apply Fin.ext; have := j.isLt; omega
    refine ⟨m', run, changed, ?_, ?_⟩
    · intro j
      change ValueValid L τ (arrSetW (eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin (eval σ₀ v σ ρ) j)
      rw [singleton_index (eval σ₀ i σ ρ), index0 j]
      exact valid
    · change WordsAt m' fp d (encodeWords L (.arr τ 1)
        (arrSetW (eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin (eval σ₀ v σ ρ)))
      rw [singleton_index (eval σ₀ i σ ρ)]
      simpa only [encodeWords, if_neg (by decide : ¬(1 : Nat) = 0), elementEncoding,
        List.append_nil, arrSetW, ↓reduceIte] using words
  · simp only [arrSetL] at h
    split at h
    · next available =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cv, tv⟩, hv, ⟨ci, ti⟩, hi, rfl, rfl⟩ := h
      let src := d + valueWords (.arr τ n)
      let ptr := src + valueWords τ
      let j := (eval σ₀ i σ ρ).fin
      have positive := valueWords_pos τ
      have sourceWidth : valueWords (.arr τ n) = n * valueWords τ := by
        simp only [valueWords]
        rw [Nat.max_eq_right (by have := Nat.mul_pos available.1 positive; omega)]
      have bound : (j.val + 1) * valueWords τ ≤ n * valueWords τ :=
        Nat.mul_le_mul_right (valueWords τ) (by have := j.isLt; omega)
      have hp' : Pre L m pc fp K d
          (ca ++ (cv ++ (ci ++ storeFrameSpan (valueWords τ) d src ptr (ptr + 1)))) ρ W reserved := by
        simpa only [src, ptr, List.append_assoc] using hp
      obtain ⟨m1, run1, changed1, array⟩ := iha ca ta ha (by omega) m pc hp'.left
      have next1 : Pre L m1 _ fp K src
          (cv ++ (ci ++ storeFrameSpan (valueWords τ) d src ptr (ptr + 1))) ρ W reserved :=
        hp'.next changed1 (by (try simp only [src]); omega) (by omega)
      obtain ⟨m2, run2, changed2, value⟩ := ihv cv tv hv (by omega) m1 _ next1.left
      have next2 : Pre L m2 _ fp K ptr (ci ++ storeFrameSpan (valueWords τ) d src ptr (ptr + 1)) ρ W reserved :=
        next1.next changed2 (by (try simp only [ptr]); omega) (by omega)
      obtain ⟨m3, run3, changed3, index⟩ := ihi ci ti hi (by omega) m2 _ next2.left
      have frame1 := hp.frame.agree changed1
      have frame2 := frame1.agree changed2
      have array2 := array.agree changed2 frame1 (by (try simp only [src]); omega) (by omega)
      have array3 := array2.agree changed3 frame2 (by (try simp only [src, ptr]); omega) (by omega)
      have value3 := value.agree changed3 frame2 (by (try simp only [ptr]); omega) (by omega)
      obtain ⟨word, read, encoded⟩ := ValueAt.word (.index n) _ trivial index
      change word = BitVec.ofInt 64 (eval σ₀ i σ ρ).n at encoded
      subst word
      have indexWord : m3.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 j.val) := by
        have nonnegative := (eval σ₀ i σ ρ).lo_le
        simpa only [j, Zahl.fin, BitVec.ofNat_eq_ofNat, ← BitVec.ofInt_natCast,
          Int.toNat_of_nonneg nonnegative] using read
      have tail := next2.next changed3 (Nat.le_refl _) (by omega)
      obtain ⟨m4, run4, changed4, written, preserved⟩ := storeFrameSpan_ok (base := d) (src := src) (ptr := ptr)
        (tmp := ptr + 1) (index := j.val) (by (try simp only [src]); omega) (by (try simp only [ptr]); omega) (by omega)
        (by omega) available.2 indexWord value3 tail
      refine ⟨m4, ?_, changed1.trans ((changed2.mono (by (try simp only [src]); omega)).trans
        ((changed3.mono (by (try simp only [src, ptr]); omega)).trans changed4)), ?_, ?_⟩
      · simpa only [src, ptr, List.length_append, storeFrameSpan_length, pc_add, List.append_assoc,
          Nat.add_assoc] using run1.trans (run2.trans (run3.trans run4))
      · intro k
        change ValueValid L τ (arrSetW (eval σ₀ a σ ρ) j (eval σ₀ v σ ρ) k)
        simp only [arrSetW]
        split
        · exact value.1
        · exact array.1 k
      · change WordsAt m4 fp d (encodeWords L (.arr τ n) (arrSetW (eval σ₀ a σ ρ) j (eval σ₀ v σ ρ)))
        exact wordsAt_arrSet (eval σ₀ a σ ρ) (eval σ₀ v σ ρ) j array3.2 written preserved
          (by (try simp only [src, ptr]); omega)
    · cases h
end Gabbro.Stage0.Senke
