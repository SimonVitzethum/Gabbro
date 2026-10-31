/- Subject: Runtime length, byte access and comparisons on short string words. -/
import Stage0.Senke.Ausdruck.Aggregat.String
import Stage0.Senke.Ausdruck.Aggregat.Scalar
import Stage0.Senke.Ausdruck.Quant.Selection

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

theorem strGet_ok {n : Nat} {lo hi : Int} (s : Expr D Γ Λ (.str n)) (i : Expr D Γ Λ (.int lo hi))
    (ihs : ∀ ca ta, lowE L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (ihi : ∀ ca ta, lowE L (reserved := reserved) i d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.int lo hi) (eval σ₀ i σ ρ))
    (ihl : ∀ ca ta, lowE L (reserved := reserved) i (d + n + 1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + n + 1) ca ρ W reserved →
        ValueOk L m pc fp K (d + n + 1) ca (.int lo hi) (eval σ₀ i σ ρ))
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
  · split at h
    · next hl =>
      obtain ⟨hn2, hlo, hhi⟩ := hl
      simp only [strGetLongL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨cs, ts⟩, hs, ⟨ci, ti⟩, hix, rfl, rfl⟩ := h
      have w1 : valueWords (.int 0 255) = 1 := by decide
      have hp' : Pre L m pc fp K d (cs ++ (ci ++ selectFrameSpan 1 (d + 1) d (d + n + 1) (d + n + 1 + 1)))
          ρ W reserved := by simpa only [List.append_assoc] using hp
      obtain ⟨m1, run1, changed1, string⟩ := ihs cs ts hs (by omega) m pc hp'.left
      have next : Pre L m1 _ fp K (d + n + 1) (ci ++ selectFrameSpan 1 (d + 1) d (d + n + 1) (d + n + 1 + 1))
          ρ W reserved := hp'.next changed1 (by omega) (by omega)
      obtain ⟨m2, run2, changed2, index⟩ := ihl ci ti hix (by omega) m1 _ next.left
      have stringKept := string.agree changed2 (hp.frame.agree changed1)
        (by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]; omega) (by omega)
      obtain ⟨word, read, encoded⟩ := ValueAt.word (.int lo hi) _ trivial index
      change word = BitVec.ofInt 64 (eval σ₀ i σ ρ).n at encoded
      subst word
      have nonneg : 0 ≤ (eval σ₀ i σ ρ).n := by have := (eval σ₀ i σ ρ).lo_le; omega
      have bound := (eval σ₀ i σ ρ).le_hi
      obtain ⟨j, hjdef⟩ : ∃ j : Nat, j = (eval σ₀ i σ ρ).n.toNat := ⟨_, rfl⟩
      have hj : ((j : Nat) : Int) = (eval σ₀ i σ ρ).n := by rw [hjdef]; exact Int.toNat_of_nonneg nonneg
      have jLt : j < n := by omega
      have indexWord : m2.rd64 (slot fp (BitVec.ofNat 64 (d + n + 1))) = some (BitVec.ofNat 64 j) := by
        have r := read
        simp only [BitVec.ofInt_natCast, ← hj] at r
        exact r
      have hget : (encodeWords L (.str n) (eval σ₀ s σ ρ))[j + 1]? =
          some (BitVec.ofInt 64 (strGetW (eval σ₀ s σ ρ : { bs : List (Zahl 0 255) // bs.length ≤ n }) (j : Int)).n) := by
        simp only [encodeWords, if_neg (show ¬ n ≤ 1 by omega)]
        exact strBytes_word (eval σ₀ s σ ρ) j jLt
      have inRange : j + 1 < (encodeWords L (.str n) (eval σ₀ s σ ρ)).length := by
        rw [encodeWords_length]; simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]; omega
      have atWord := stringKept.2 (1 + j) (by rw [Nat.add_comm]; exact inRange)
      have key : ∀ k, k = j + 1 → ∀ (hk : k < (encodeWords L (.str n) (eval σ₀ s σ ρ)).length),
          (encodeWords L (.str n) (eval σ₀ s σ ρ))[k]'hk =
            BitVec.ofInt 64 (strGetW (eval σ₀ s σ ρ : { bs : List (Zahl 0 255) // bs.length ≤ n }) (j : Int)).n := by
        intro k hk hk'
        subst hk
        exact Option.some.inj ((List.getElem?_eq_getElem hk').symm.trans hget)
      have atWord' : m2.rd64 (slot fp (BitVec.ofNat 64 ((d + 1) + j * valueWords (.int 0 255)))) =
          some (BitVec.ofInt 64 (strGetW (eval σ₀ s σ ρ : { bs : List (Zahl 0 255) // bs.length ≤ n }) (j : Int)).n) := by
        rw [show (d + 1) + j * valueWords (.int 0 255) = d + (1 + j) by rw [w1]; omega, atWord,
          key (1 + j) (Nat.add_comm 1 j)]
      have byteWord : ValueAt L m2 fp ((d + 1) + j * valueWords (.int 0 255)) (.int 0 255)
          (strGetW (eval σ₀ s σ ρ : { bs : List (Zahl 0 255) // bs.length ≤ n }) (j : Int)) := ValueAt.of_enc w1 atWord' rfl
      have tail := next.next changed2 (Nat.le_refl _) (by omega)
      obtain ⟨m3, run3, changed3, result⟩ := selectFrameSpan_ok (base := d + 1) (dst := d) (index := j)
        (τ := .int 0 255) (by rw [w1]; omega) (by rw [w1]; omega) (Nat.lt_succ_self _) (by omega)
        (by rw [w1]; decide) indexWord byteWord tail
      have valueOk : ValueOk L m pc fp K d (cs ++ ci ++ selectFrameSpan 1 (d + 1) d (d + n + 1) (d + n + 1 + 1))
          (.int 0 255) (strGetW (eval σ₀ s σ ρ : { bs : List (Zahl 0 255) // bs.length ≤ n }) (j : Int)) := by
        refine ⟨m3, ?_, changed1.trans ((changed2.mono (by omega)).trans changed3), result⟩
        simpa only [w1, Nat.succ_eq_add_one, List.length_append, pc_add, List.append_assoc, Nat.add_assoc] using
          run1.trans (run2.trans run3)
      rw [hj] at valueOk
      exact valueOk.word trivial
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
