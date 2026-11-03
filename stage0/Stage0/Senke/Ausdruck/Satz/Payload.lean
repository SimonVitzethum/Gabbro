/- Compositional sum construction from the actual packed and full payload producers. -/
module
public import Stage0.Senke.Ausdruck.Tag
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Sum.Construct
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {currentOld : Bool}

/-- A bare packed case emits only its tag word. -/
theorem lowN_empty_ok {Λ : List (Res D)} {Γ : Ctx} (tag : Nat) (htag : tag < 256)
    {fp : Runner.W} {K d top : Nat} {c : List II} {W : Runner.Mem → Prop}
    {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W}
    (made : lowN (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) tag .empty d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (fun w => w = BitVec.ofNat 64 tag) := by
  simp only [lowN_empty, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨rfl, rfl⟩ := made
  exact (const_ok pre (lit32_nat (by omega)) (by omega)).mono fun w word => by
    simpa only [BitVec.ofInt_natCast] using word

/-- The absent full payload executes no code and has no ABI marker word. -/
theorem lowPayload_empty_ok {Λ : List (Res D)} {Γ : Ctx}
    {fp : Runner.W} {K d top : Nat} {c : List II} {W : Runner.Mem → Prop}
    {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W}
    (made : lowPayload (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) .empty d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    Executes m pc fp K d c (fun m' => PayloadAt L m' fp d none ()) := by
  simp only [lowPayload_empty, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨rfl, rfl⟩ := made
  exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, Agree.refl _ _ _ _, trivial,
    by simp [WordsAt, payloadEncoding]⟩

/-- Packing an integer payload consumes the complete expression certificate. -/
theorem lowN_int_ok {Λ : List (Res D)} {Γ : Ctx} {lo hi : Int}
    (e : Expr D Γ Λ (.int lo hi)) (tag : Nat) (htag : tag < 256)
    {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {c : List II}
    {W : Runner.Mem → Prop} {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W}
    (ih : ∀ ce te, lowE (currentOld := currentOld) L (reserved := reserved) e d = some (ce, te) →
      te ≤ K → ∀ m pc, Pre L m pc fp K d ce ρ W reserved →
        ValueOk L m pc fp K d ce (.int lo hi) (eval σ₀ e σ ρ))
    (made : lowN (currentOld := currentOld) L (reserved := reserved) tag (.val e) d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (fun w => w = BitVec.ofNat 64
      (tag + 256 * sumOff (some (.int lo hi)) (evalNutz σ₀ (.val e) σ ρ))) := by
  simp only [lowN_val, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at made
  obtain ⟨⟨ce, te⟩, emitted, output⟩ := made
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj output
  exact packSum_ok (K := K) (d := d) (tag := tag) (ce := (ce, te)) (v := eval σ₀ e σ ρ)
    (by simp only [packSum, bin2] at fits; omega) htag
    (by simp only [packSum, bin2] at fits; omega)
    (fun m pc hp => (ih ce te emitted
      (by simp only [packSum, bin2] at fits; omega) m pc hp).word trivial) pre

/-- The selected schema chooses the existing packed or separated constructor;
    both consume certificates for the actual payload, without eliminating its index. -/
theorem case_value_ok {Λ : List (Res D)} {Γ : Ctx} (cs : List (Option Ty))
    (i : Fin cs.length) (nutz : NutzlastExpr D Γ Λ (cs.get i))
    {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {c : List II}
    {W : Runner.Mem → Prop} {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W}
    (packed : i.val < 256 → ∀ ca ta,
      lowN (currentOld := currentOld) L (reserved := reserved) i.val nutz d = some (ca, ta) →
      ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
        Ok m pc fp K d ca (fun w => w = BitVec.ofNat 64
          (i.val + 256 * sumOff (cs.get i) (evalNutz σ₀ nutz σ ρ))))
    (payload : ∀ ca ta,
      lowPayload (currentOld := currentOld) L (reserved := reserved) nutz
        (d + integerWords 0 (cs.length - 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + integerWords 0 (cs.length - 1)) ca ρ W reserved →
      Executes m pc fp K (d + integerWords 0 (cs.length - 1)) ca (fun m' =>
        PayloadAt L m' fp (d + integerWords 0 (cs.length - 1)) (cs.get i) (evalNutz σ₀ nutz σ ρ)))
    (made : lowE (currentOld := currentOld) L (reserved := reserved) (.case cs i nutz) d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.sum cs) (eval σ₀ (.case cs i nutz) σ ρ) := by
  simp only [lowE_case] at made
  split at made
  · next hfit =>
    have count : cs.length ≤ 256 := by
      have schema := hfit
      simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq] at schema
      exact schema.1
    refine Ok.value ?_ (by simp only [valueWords, hfit, ite_true])
    exact (packed (by have := i.isLt; omega) c top made fits m pc pre).mono fun w word => by
      refine ⟨hfit, ?_⟩
      simpa only [eval, sumN, Fall.to_of] using word
  · next separate =>
    exact sumSpan_ok
      (payload := lowPayload (currentOld := currentOld) L (reserved := reserved) nutz
        (d + integerWords 0 (cs.length - 1)))
      i (evalNutz σ₀ nutz σ ρ) (Bool.eq_false_iff.mpr separate)
      payload made fits pre

end Gabbro.Stage0.Senke
