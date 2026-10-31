/- Subject: Runtime length, byte access and comparisons on short string words. -/
import Stage0.Senke.Ausdruck.Aggregat.String
import Stage0.Senke.Ausdruck.Aggregat.Scalar

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

theorem strGet_ok {n : Nat} {lo hi : Int} (s : Expr D Γ Λ (.str n)) (i : Expr D Γ Λ (.int lo hi))
    (ihs : ∀ ca ta, lowE L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (ihi : ∀ ca ta, lowE L (reserved := reserved) i d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.int lo hi) (eval σ₀ i σ ρ))
    (h : lowE L (reserved := reserved) (.strGet s i) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 255) (eval σ₀ (.strGet s i) σ ρ) := by
  refine Ok.value ?_ (by decide)
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    have hd := strGetL_top h
    refine wennL_ok h hK (by omega) (bc := decide ((eval σ₀ i σ ρ).n = 0)) ?_ ?_ ?_ hp
    · intro cc tc hc htc m pc hp
      refine wordK_ok hc htc (by decide)
        (fun ca ta ha ht m pc hp => (ihi ca ta ha ht m pc hp).word trivial)
        (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) hp
      intro wi hi
      refine ⟨_, rfl, ?_⟩
      rw [hi, beq_in (inW_spec hn.2 (eval σ₀ i σ ρ).lo_le (eval σ₀ i σ ρ).le_hi) (by decide), bool_word]
    · intro he ca ta ha hta m pc hp
      have hz : (eval σ₀ i σ ρ).n = 0 := by simpa using he
      refine wordK_ok ha hta (by decide)
        (fun ca ta ha ht m pc hp => (ihs ca ta ha ht m pc hp).word hn.1)
        (g := fun x y => some (x &&& y)) ?_ rfl (by decide) hp
      intro ws hs
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval]
      rw [hz, hs.2]
      exact strN_byte (eval σ₀ s σ ρ) hn.1
    · intro he cb tb hb htb m pc hp
      have hz : (eval σ₀ i σ ρ).n ≠ 0 := by simpa using he
      cases hb
      exact (const_ok hp (by decide) (by omega)).mono fun w hw => by
        simpa [Enc, eval, short_get_other (eval σ₀ s σ ρ) hn.1 _ hz] using hw
  · cases h

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
