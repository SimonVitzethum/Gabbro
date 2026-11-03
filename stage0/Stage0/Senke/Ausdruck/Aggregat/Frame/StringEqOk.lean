/- Subject: Generic correctness of the equality of two strings of capacity at least two. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.CompareOk
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringEq
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringEqMixedOk
@[expose] public section

variable {currentOld : Bool}


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem strEqLong_ok {n q : Nat} (vs : Wert D (.str n))
    (vt : Wert D (.str q)) (s t : Option (List II × Nat))
    (ihs : ∀ ca ta, s = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) vs)
    (iht : ∀ ca ta, t = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + (n + 1)) ca ρ W reserved → ValueOk L m pc fp K (d + (n + 1)) ca (.str q) vt)
    (h : strEqLongL n q d s t = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (strEqW vs vt) := by
  simp only [strEqLongL] at h
  split at h
  · next g =>
    obtain ⟨hn2, hq2, hn31, hq31⟩ := g
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs, ⟨ct, tt⟩, ht, rfl, rfl⟩ := h
    have wn : valueWords (.str n) = n + 1 := by simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]
    have wq : valueWords (.str q) = q + 1 := by simp only [valueWords, if_neg (show ¬ q ≤ 1 by omega)]
    let acc := d + (n + 1) + (q + 1)
    let tmp := acc + 1
    let k0 := min n q + 1
    have hp' : Pre L m pc fp K d (cs ++ (ct ++ ([ci 1 acc 0 0] ++ (xorOrSpan k0 d (d + (n + 1)) acc tmp ++
        ([ci 1 tmp 0 0] ++ [ci 14 d acc tmp]))))) ρ W reserved := by
      have h := hp
      rw [List.append_assoc] at h
      exact h
    obtain ⟨m1, run1, ch1, vs1⟩ := ihs cs ts hs (by omega) m pc hp'.left
    have next1 : Pre L m1 _ fp K (d + (n + 1)) _ ρ W reserved := hp'.next ch1 (by omega) (by omega)
    obtain ⟨m2, run2, ch2, vt2⟩ := iht ct tt ht (by omega) m1 _ next1.left
    have next2 : Pre L m2 _ fp K acc _ ρ W reserved := next1.next ch2 (by omega) (by omega)
    obtain ⟨m3, run3, ch3, z, read3, hz⟩ := const_ok (k := 0) next2.left (by decide) (by omega)
    subst hz
    have next3 : Pre L m3 _ fp K acc _ ρ W reserved := next2.next ch3 (Nat.le_refl _) (by omega)
    have frame1 := hp.frame.agree ch1
    have frame2 := frame1.agree ch2
    have vs3 := (vs1.agree ch2 frame1 (by omega) (by omega)).agree ch3 frame2 (by omega) (by omega)
    have vt3 := vt2.agree ch3 frame2 (by omega) (by omega)
    have lenS : ((encodeWords L (.str n) vs).take k0).length = k0 := by
      simp only [List.length_take, encodeWords_length, wn]; omega
    have lenT : ((encodeWords L (.str q) vt).take k0).length = k0 := by
      simp only [List.length_take, encodeWords_length, wq]; omega
    have wa : WordsAt m3 fp d ((encodeWords L (.str n) vs).take k0) := by
      intro i hi
      have hi' : i < k0 := by rw [lenS] at hi; exact hi
      simp only [List.getElem_take]
      exact vs3.2 i (by simp only [encodeWords_length, wn]; omega)
    have wb : WordsAt m3 fp (d + (n + 1)) ((encodeWords L (.str q) vt).take k0) := by
      intro i hi
      have hi' : i < k0 := by rw [lenT] at hi; exact hi
      simp only [List.getElem_take]
      exact vt3.2 i (by simp only [encodeWords_length, wq]; omega)
    have pre3 := next3.left
    rw [← lenS] at pre3
    obtain ⟨m4, run4, ch4, read4⟩ := xorOrSpan_ok (L := L) _ _ (by rw [lenS, lenT]) pre3
      (by omega) (by omega) (by omega) (by omega) wa wb read3
    rw [lenS] at run4
    have frame3 := frame2.agree ch3
    have next4 : Pre L m4 _ fp K acc _ ρ W reserved := next3.next ch4 (Nat.le_refl _) (by omega)
    obtain ⟨m5, run5, ch5, z5, read5, hz5⟩ := const_ok (k := 0)
      (show Pre L m4 _ fp K tmp [ci 1 tmp 0 0] ρ W reserved from
        { next4.left with ctx := by have := hp.ctx; omega }) (by decide) (by omega)
    subst hz5
    have next5 : Pre L m5 _ fp K acc _ ρ W reserved :=
      next4.next (ch5.mono (by omega : acc ≤ tmp)) (Nat.le_refl _) (by omega)
    have accRead : m5.rd64 (slot fp (BitVec.ofNat 64 acc)) =
        some (((encodeWords L (.str n) vs).take k0).zip ((encodeWords L (.str q) vt).take k0) |>.foldl
          (fun x p => x ||| (p.1 ^^^ p.2)) (BitVec.ofInt 64 0)) := by
      rw [agree_rd_low ch5 hp.frame.room (by omega) (by omega)]; exact read4
    obtain ⟨m6, run6, ch6, z6, read6, hz6⟩ := eng_bin_ok
      (show Pre L m5 _ fp K d [ci 14 d acc tmp] ρ W reserved from
        { next5 with ctx := by have := hp.ctx; omega })
      (by omega) (by omega) (by omega) accRead read5
      (g := fun a b => some (Runner.IR.bool (a == b))) rfl (by decide) rfl
    subst hz6
    have iff₁ := foldl_or_xor_zero ((encodeWords L (.str n) vs).take k0) ((encodeWords L (.str q) vt).take k0)
      (BitVec.ofInt 64 0) (by rw [lenS, lenT])
    have iff₂ := strEq_words_iff (L := L) hn2 hq2 (by omega) (by omega) vs vt
    have zero : BitVec.ofInt 64 0 = (0 : BitVec 64) := by decide
    have hfold : (((encodeWords L (.str n) vs).take k0).zip ((encodeWords L (.str q) vt).take k0) |>.foldl
          (fun x p => x ||| (p.1 ^^^ p.2)) (BitVec.ofInt 64 0)) = 0 ↔ strEqW vs vt = true := by
      rw [iff₁, zero, iff₂]
      simp only [eq_self, true_and, strEqW, beq_iff_eq]
    have encOf : ∀ F : BitVec 64, (F = 0 ↔ strEqW vs vt = true) →
        Enc L .bool (strEqW vs vt) (Runner.IR.bool (F == BitVec.ofInt 64 0)) := by
      intro F hF
      simp only [Enc, wahr?]
      rw [zero]
      by_cases e : F = 0
      · have := hF.mp e
        simp [Runner.IR.bool, e, this]
      · have : ¬ strEqW vs vt = true := fun h => e (hF.mpr h)
        simp [Runner.IR.bool, this]
        exact e
    have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m6 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m6 :=
      fun p q h s => h ▸ s
    refine Ok.value ⟨m6, ?_, ?_, _, read6, encOf _ hfold⟩ (by decide)
    · refine key _ _ ?_ (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_append, List.length_cons,
        List.length_nil, xorOrSpan_length]
      omega
    · exact ch1.trans ((ch2.mono (by omega)).trans ((ch3.mono (by omega)).trans
        ((ch4.mono (by omega)).trans ((ch5.mono (by omega)).trans ch6))))
  · cases h

/-- String equality: the packed one-word comparison for capacities up to one, the branch-free span
    comparison for capacities of at least two. -/
theorem strEq_ok {n q : Nat} (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q)) {σ₀ σ : World D}
    (ihs : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (iht : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t (d + 1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) ca ρ W reserved → ValueOk L m pc fp K (d + 1) ca (.str q) (eval σ₀ t σ ρ))
    (ihl : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t (d + (n + 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + (n + 1)) ca ρ W reserved → ValueOk L m pc fp K (d + (n + 1)) ca (.str q) (eval σ₀ t σ ρ))
    (ihm : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t (d + valueWords (.str n)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords (.str n)) ca ρ W reserved →
        ValueOk L m pc fp K (d + valueWords (.str n)) ca (.str q) (eval σ₀ t σ ρ))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.strEq s t) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (eval σ₀ (.strEq s t) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next short =>
    exact strCompare_ok false s t ihs iht (by rw [if_pos short]; exact h) hK hp
  · split at h
    · exact strEqMixed_ok (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) _ _ ihs ihm h hK hp
    · exact strEqLong_ok (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) _ _ ihs ihl h hK hp

end Gabbro.Stage0.Senke
