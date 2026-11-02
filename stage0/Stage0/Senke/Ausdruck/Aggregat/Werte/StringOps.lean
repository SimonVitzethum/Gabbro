/- Subject: Runtime length, byte access and comparisons on short string words. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Werte.String
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
public import Stage0.Senke.Ausdruck.Quant.Selection
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
variable {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem strLen_ok {n : Nat} (s : Expr D Γ Λ (.str n))
    (ih : ∀ ca ta, lowE L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (h : lowE L (reserved := reserved) (.strLen s) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 n) (eval σ₀ (.strLen s) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
    refine wordK_ok h hK (by decide)
      (fun ca ta ha ht m pc hp => (ih ca ta ha ht m pc hp).word hn)
      (g := fun x y => some (x >>> (y.toNat % 64))) ?_ rfl (by decide) hp
    intro wa ha
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval]
    rw [ha.2]
    exact strN_length (eval σ₀ s σ ρ) hn
  · next long =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨cs, ts⟩, hs, out⟩ := h
    cases out
    have capacity : n + 1 ≤ K := by
      simp only [valueWords, if_neg long] at hK
      omega
    have width : valueWords (.int 0 n) = 1 :=
      integerWords_unsigned (by decide) (by have := hp.small; omega)
    obtain ⟨m', run, changed, value⟩ := ih cs ts hs (Nat.le_trans (Nat.le_max_left _ _) hK) m pc hp
    refine ⟨m', run, changed, ValueAt.of_enc width ?_ rfl⟩
    have read := value.2 0 (by rw [encodeWords_length]; exact valueWords_pos (.str n))
    simpa only [encodeWords, if_neg long, List.cons_append, List.getElem_cons_zero,
      Nat.add_zero, eval, strLenW, BitVec.ofInt_natCast] using read

theorem strBytes_word {n : Nat} (w : { bs : List (Zahl 0 255) // bs.length ≤ n }) (j : Nat) (hj : j < n) :
    (BitVec.ofNat 64 w.1.length :: w.1.map (fun b => BitVec.ofInt 64 b.n) ++
      List.replicate (n - w.1.length) (0 : BitVec 64))[j + 1]? = some (BitVec.ofInt 64 (strGetW w (j : Int)).n) := by
  have hlen := w.2
  rw [List.cons_append, List.getElem?_cons_succ]
  by_cases hl : j < w.1.length
  · rw [List.getElem?_append_left (by simpa using hl), List.getElem?_map]
    simp only [strGetW, Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte]
    rw [List.getElem?_eq_getElem hl]
    simp
  · rw [List.getElem?_append_right (by simpa using hl)]
    simp only [List.length_map, List.getElem?_replicate]
    simp only [strGetW, Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
    simp only [Option.getD_none]
    have : j - w.1.length < n - w.1.length := by omega
    simp [this]

/-- Both comparisons share evaluation and the same bounded word representation. -/
theorem strCompare_ok {n q : Nat} (lt : Bool) (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q))
    (ihs : ∀ ca ta, lowE L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (iht : ∀ ca ta, lowE L (reserved := reserved) t (d + 1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) ca ρ W reserved → ValueOk L m pc fp K (d + 1) ca (.str q) (eval σ₀ t σ ρ))
    (h : (if n ≤ 1 ∧ q ≤ 1 then wordL (if lt then 13 else 14) d
      (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1)) else none) = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (if lt then strLtW (eval σ₀ s σ ρ) (eval σ₀ t σ ρ)
      else strEqW (eval σ₀ s σ ρ) (eval σ₀ t σ ρ)) := by
  refine Ok.value ?_ rfl
  split at h
  · next hn =>
    refine wordL_ok h hK
      (fun ca ta ha ht m pc hp => (ihs ca ta ha ht m pc hp).word hn.1)
      (fun ca ta ha ht m pc hp => (iht ca ta ha ht m pc hp).word hn.2)
      (g := fun x y => some (Runner.IR.bool (if lt then x.slt y else x == y))) ?_
      (by cases lt <;> rfl) (by cases lt <;> decide) hp
    intro ws wt hs ht
    refine ⟨_, rfl, ?_⟩
    have hsbound := strN_range (eval σ₀ s σ ρ).1
    have htbound := strN_range (eval σ₀ t σ ρ).1
    simp only [Enc, wahr?]
    rw [hs.2, ht.2, ← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast]
    cases lt with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [beq_in (by omega) (by omega), bool_word]
      rw [short_eq (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) hn.1 hn.2]
      simp only [decide_eq_true_eq]
      split <;> split <;> first | rfl | omega
    | true =>
      simp only [↓reduceIte]
      rw [slt_in (by omega) (by omega), bool_word]
      rw [short_lt (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) hn.1 hn.2]
      simp
  · cases h
end Gabbro.Stage0.Senke
