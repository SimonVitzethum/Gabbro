/- The inclusive float range test, using the same integer keys as comparisons. -/
import Stage0.Senke.Ausdruck.Gleit.Bereich
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatConstL_ok {fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (x : GFloat) (hw : Gleitkomma.wf Gleitkomma.f64 x)
    (hd : d+2 ≤ K) {m : Runner.Mem} {pc : Runner.W}
    (hp : Pre L m pc fp K d (floatConstL x d).1 ρ W reserved) :
    Ok m pc fp K d (floatConstL x d).1 (FloatKeyEnc x) := by
  exact (konstWL_ok 4 _ (BitVec.toNat_lt_twoPow_of_le (Nat.le_refl 64)) hd hp).mono
    fun w he => ⟨hw, by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he⟩

theorem floatRangeL_room {d top : Nat} {lo hi : Int × Int} {e : Nat → Option (List II × Nat)} {c : List II}
    (h : floatRangeL d lo hi e = some (c, top)) : d + 7 ≤ top := by
  simp only [floatRangeL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨a, ta⟩, ha, ⟨b, tb⟩, hb, hc⟩ := h
  have := floatKeyL_room hb
  simp only [Prod.mk.injEq, bin2] at hc
  omega

/-- The unordered-bound path is a real emitted rejection, at any reservation.
    Its footprint and frame budget are those of the ordinary constant rule. -/
theorem canonicalFloatRangeL_nan_ok {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K d top reserved : Nat} {c : List II} {lo hi : Int × Int}
    {producer : Nat → Option (List II × Nat)}
    (hn : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) = .nan ∨
      Gleitkomma.klasse Gleitkomma.f64 (bruch hi) = .nan)
    (hc : canonicalFloatRangeL d lo hi producer = some (c, top))
    (ht : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = Runner.IR.bool true) := by
  rw [canonicalFloatRangeL_nan d lo hi producer hn] at hc
  cases hc
  exact const_ok hp (by decide) (by omega)

/-- Evaluate a pure expression and compare its key to both constant endpoint keys. -/
theorem floatRangeL_raw_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {lo hi : Int × Int} (x : GFloat)
    (producer : Nat → Option (List II × Nat))
    (xf : Gleitkomma.klasse Gleitkomma.f64 x ≠ .nan) {c : List II}
    (ih : ∀ d c top, producer d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (fun w => Gleitkomma.wf Gleitkomma.f64 x ∧
        w = BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 x)))
    (hl : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) ≠ .nan)
    (hh : Gleitkomma.klasse Gleitkomma.f64 (bruch hi) ≠ .nan)
    (h : floatRangeL d lo hi (producer) = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = Runner.IR.bool (floatOutside lo hi x)) := by
  have key : ∀ j code ceiling,
      floatKeyL j (producer j) (producer (j+3)) = some (code, ceiling) →
      ceiling ≤ K → ∀ m pc, Pre L m pc fp K j code ρ W reserved →
      Ok m pc fp K j code (FloatKeyEnc x) := by
    intro j code ceiling hc ht m pc hp
    generalize he : producer j = ce at hc
    generalize hf : producer (j+3) = cf at hc
    cases ce with
    | none => cases hc
    | some ce => cases cf with
      | none => cases hc
      | some cf =>
        have bounds := floatKeyL_top hc
        exact floatKeyL_ok hc ht (ih _ _ _ he (by omega))
          (ih _ _ _ hf (by omega)) hp
  have ht := floatRangeL_room h
  simp only [floatRangeL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨a, ta⟩, ha, ⟨b, tb⟩, hb, hc⟩ := h
  cases hc
  have haT : ta ≤ K := by simp only [bin2, floatConstL, konstWL] at hK; omega
  have hbT : tb ≤ K := by simp only [bin2, floatConstL, konstWL] at hK; omega
  apply bin_ok (g := fun x y => some (x ||| y))
    (Pa := fun w => w = Runner.IR.bool (gleitLt x (bruch lo)))
    (Pb := fun w => w = Runner.IR.bool (gleitLt (bruch hi) x)) ?_ ?_ ?_ rfl (by decide) (by omega) hp
  · intro m pc hp
    exact floatCompare_ok false xf hl rfl (by omega)
      (fun m pc hp => key _ _ _ ha haT _ _ hp)
      (fun m pc hp => floatConstL_ok _ (Gleitkomma.rundeBruch_wf _ Gleitkomma.f64_p _) (by omega) hp) hp
  · intro m pc hp
    exact floatCompare_ok false hh xf rfl (by omega)
      (fun m pc hp => floatConstL_ok _ (Gleitkomma.rundeBruch_wf _ Gleitkomma.f64_p _) (by omega) hp)
      (fun m pc hp => key _ _ _ hb hbT _ _ hp) hp
  · intro x y hx hy
    refine ⟨_, rfl, ?_⟩
    rw [hx, hy, bool_word, bool_word, or_word, ← bool_word]
    rfl

/-- Evaluate a pure expression and compare its key to both constant endpoint keys. -/
theorem floatRangeL_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (σ₀ σ : World D) {l1 h1 lo hi : Int × Int}
    (e : Expr D Γ Λ (.fl l1 h1)) {c : List II}
    (ih : ∀ d c top, lowE L e d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W → Ok m pc fp K d c (Enc L (.fl l1 h1) (eval σ₀ e σ ρ)))
    (hl : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) ≠ .nan)
    (hh : Gleitkomma.klasse Gleitkomma.f64 (bruch hi) ≠ .nan)
    (h : floatRangeL d lo hi (lowE L e) = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (· = Runner.IR.bool (floatOutside lo hi (eval σ₀ e σ ρ).x)) := by
  exact floatRangeL_raw_ok (eval σ₀ e σ ρ).x (lowE L e)
    (endlich_nicht_nan (eval σ₀ e σ ρ).endlich) ih hl hh h hK hp

/-- The canonical range template consumes any proved finite binary64 producer.
    Reservations and the complete frame footprint flow through the shared rules. -/
theorem canonicalFloatRangeL_ok {fp : Runner.W} {K d top reserved : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {lo hi : Int × Int} (x : GFloat)
    (hw : Gleitkomma.wf Gleitkomma.f64 x) (hf : gleitEndlich x = true)
    (producer : Nat → Option (List II × Nat)) {c : List II}
    (ih : ∀ d c top, producer d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved →
      Ok m pc fp K d c (fun w => Gleitkomma.wf Gleitkomma.f64 x ∧
        w = BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 x)))
    (hc : canonicalFloatRangeL d lo hi producer = some (c, top))
    (ht : top ≤ K) {m : Runner.Mem} {pc : Runner.W}
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = Runner.IR.bool (floatRangeReject lo hi x)) := by
  by_cases hn : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) = .nan ∨
      Gleitkomma.klasse Gleitkomma.f64 (bruch hi) = .nan
  · simpa only [floatRangeReject, if_pos hn] using
      canonicalFloatRangeL_nan_ok hn hc ht hp
  · have hl : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) ≠ .nan :=
      fun h => hn (Or.inl h)
    have hh : Gleitkomma.klasse Gleitkomma.f64 (bruch hi) ≠ .nan :=
      fun h => hn (Or.inr h)
    have eq : floatRangeReject lo hi x = floatOutside lo hi x := by
      have a := floatRangeReject_none (lo := lo) (hi := hi) hw hf
      have b := floatOutside_none hl hh hf
      cases ha : floatRangeReject lo hi x <;>
        cases hb : floatOutside lo hi x <;> simp_all
    have code : floatRangeL d lo hi producer = some (c, top) := by
      simpa only [canonicalFloatRangeL, if_neg hn] using hc
    simpa only [eq] using floatRangeL_raw_ok x producer
      (endlich_nicht_nan hf) ih hl hh code ht hp

end Gabbro.Stage0.Senke
