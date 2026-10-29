/- The inclusive float range test, using the same integer keys as comparisons. -/
import Stage0.Senke.Ausdruck.Gleit.Bereich
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatConstL_ok {fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (x : GFloat) (hw : Gleitkomma.wf Gleitkomma.f64 x)
    (hd : d+2 ≤ K) {m : Runner.Mem} {pc : Runner.W}
    (hp : Pre L m pc fp K d (floatConstL x d).1 ρ W) :
    Ok m pc fp K d (floatConstL x d).1 (FloatKeyEnc x) := by
  exact (wordL_ok 4 _ (BitVec.toNat_lt_twoPow_of_le (Nat.le_refl 64)) hd hp).mono
    fun w he => ⟨hw, by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he⟩

theorem floatRangeL_room {d top : Nat} {lo hi : Int × Int} {e : Nat → Option (List II × Nat)} {c : List II}
    (h : floatRangeL d lo hi e = some (c, top)) : d + 7 ≤ top := by
  simp only [floatRangeL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨a, ta⟩, ha, ⟨b, tb⟩, hb, hc⟩ := h
  have := floatKeyL_room hb
  simp only [Prod.mk.injEq, bin2] at hc
  omega

/-- Evaluate a pure expression and compare its key to both constant endpoint keys. -/
theorem floatRangeL_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (σ₀ σ : World D) {l1 h1 lo hi : Int × Int}
    (e : Expr D Γ Λ (.fl l1 h1)) {c : List II}
    (ih : ∀ d c top, lowE L e d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W → Ok m pc fp K d c (Enc L (.fl l1 h1) (eval σ₀ e σ ρ)))
    (hl : gleitEndlich (bruch lo) = true) (hh : gleitEndlich (bruch hi) = true)
    (h : floatRangeL d lo hi (lowE L e) = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (· = Runner.IR.bool (floatOutside lo hi (eval σ₀ e σ ρ).x)) := by
  have ht := floatRangeL_room h
  simp only [floatRangeL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨a, ta⟩, ha, ⟨b, tb⟩, hb, hc⟩ := h
  cases hc
  have haT : ta ≤ K := by simp only [bin2, floatConstL, wordL] at hK; omega
  have hbT : tb ≤ K := by simp only [bin2, floatConstL, wordL] at hK; omega
  apply bin_ok (g := fun x y => some (x ||| y))
    (Pa := fun w => w = Runner.IR.bool (gleitLt (eval σ₀ e σ ρ).x (bruch lo)))
    (Pb := fun w => w = Runner.IR.bool (gleitLt (bruch hi) (eval σ₀ e σ ρ).x)) ?_ ?_ ?_ rfl (by decide) (by omega) hp
  · intro m pc hp
    exact floatCompare_ok false (eval σ₀ e σ ρ).endlich hl rfl (by omega)
      (fun m pc hp => floatKeyE_ok σ₀ σ e ih ha haT hp)
      (fun m pc hp => floatConstL_ok _ (Gleitkomma.rundeBruch_wf _ Gleitkomma.f64_p _) (by omega) hp) hp
  · intro m pc hp
    exact floatCompare_ok false hh (eval σ₀ e σ ρ).endlich rfl (by omega)
      (fun m pc hp => floatConstL_ok _ (Gleitkomma.rundeBruch_wf _ Gleitkomma.f64_p _) (by omega) hp)
      (fun m pc hp => floatKeyE_ok σ₀ σ e ih hb hbT hp) hp
  · intro x y hx hy
    refine ⟨_, rfl, ?_⟩
    rw [hx, hy, bool_word, bool_word, or_word, ← bool_word]
    rfl

end Gabbro.Stage0.Senke
