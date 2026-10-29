/- Expression induction is used only for the float operands. -/
import Stage0.Senke.Ausdruck.Gleit.Vergleich

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

abbrev FloatKeyEnc (x : GFloat) (w : Runner.W) : Prop :=
  Gleitkomma.wf Gleitkomma.f64 x ∧ w = BitVec.ofInt 64 (floatKey x)

/-- Turn a lowered pure float operand into its key using the induction hypothesis. -/
theorem floatKeyE_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (σ₀ σ : World D) {lo hi : Int × Int}
    (e : Expr D Γ Λ (.fl lo hi)) {c : List II}
    (ih : ∀ d c top, lowE L e d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W → Ok m pc fp K d c (Enc L (.fl lo hi) (eval σ₀ e σ ρ)))
    (h : floatKeyL d (lowE L e d) (lowE L e (d+3)) = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (FloatKeyEnc (eval σ₀ e σ ρ).x) := by
  generalize ha : lowE L e d = ca at h
  generalize hb : lowE L e (d+3) = cb at h
  cases ca with
  | none => cases h
  | some ca => cases cb with
    | none => cases h
    | some cb =>
      have ht := floatKeyL_top h
      exact floatKeyL_ok h hK (ih _ _ _ ha (by omega)) (ih _ _ _ hb (by omega)) hp

theorem floatCmpL_bounds {le : Bool} {d ta tb top : Nat} {a b c : List II}
    (h : floatCmpL le d (some (a, ta)) (some (b, tb)) = some (c, top)) : ta ≤ top ∧ tb ≤ top := by
  cases le <;> simp only [floatCmpL, bind, Option.bind_some, pure, Bool.false_eq_true,
    ↓reduceIte, Option.some.injEq, Prod.mk.injEq, bin2] at h <;> omega

/-- A comparison retains the well-formedness facts until the two keys meet. -/
theorem floatCompare_ok {fp : Runner.W} {K d ta tb top : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {a b c : List II} {x y : GFloat} (le : Bool)
    (xf : gleitEndlich x = true) (yf : gleitEndlich y = true)
    (h : floatCmpL le d (some (a, ta)) (some (b, tb)) = some (c, top)) (hd : d+2 ≤ K)
    (ha : ∀ m pc, Pre L m pc fp K d a ρ W → Ok m pc fp K d a (FloatKeyEnc x))
    (hb : ∀ m pc, Pre L m pc fp K (d+1) b ρ W → Ok m pc fp K (d+1) b (FloatKeyEnc y))
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (· = Runner.IR.bool (if le then !gleitLt x y else gleitLt x y)) := by
  have hcmp : ∀ {m pc}, Pre L m pc fp K d (bin2 13 d (a, ta) (b, tb)).1 ρ W →
      Ok m pc fp K d (bin2 13 d (a, ta) (b, tb)).1 (· = Runner.IR.bool (gleitLt x y)) := by
    intro m pc hp
    exact bin_ok ha hb (fun a b ha hb => ⟨_, rfl, by
      rw [ha.2, hb.2, slt_in (float_key_range ha.1) (float_key_range hb.1),
        float_lt_key ha.1 hb.1 xf yf]⟩)
      (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) (by omega) hp
  cases le <;> simp only [floatCmpL, bind, Option.bind_some, pure, Bool.false_eq_true,
    ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h ⊢
  · obtain ⟨rfl, rfl⟩ := h
    exact hcmp hp
  · obtain ⟨rfl, rfl⟩ := h
    exact bin_ok (fun _ _ hp => hcmp hp) (fun _ _ hp => const_ok hp (by decide) (by omega))
      (fun a b ha hb => ⟨_, rfl, by rw [ha, hb, bool_word, not_word, ← bool_word]⟩)
      (g := fun a b => some (a ^^^ b)) rfl (by decide) (by omega) hp

/-- Both source comparison forms use the same finite IEEE-order proof. -/
theorem floatExprE_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (σ₀ σ : World D) {l1 h1 l2 h2 : Int × Int}
    (le : Bool) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) {c : List II}
    (iha : ∀ d c top, lowE L a d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W → Ok m pc fp K d c (Enc L (.fl l1 h1) (eval σ₀ a σ ρ)))
    (ihb : ∀ d c top, lowE L b d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W → Ok m pc fp K d c (Enc L (.fl l2 h2) (eval σ₀ b σ ρ)))
    (h : floatExprL le d (lowE L a) (lowE L b) = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (Enc L .bool
      (eval σ₀ (if le then Expr.flle b a else Expr.fllt a b) σ ρ)) := by
  unfold floatExprL at h
  generalize ha : floatKeyL d (lowE L a d) (lowE L a (d+3)) = ca at h
  generalize hb : floatKeyL (d+1) (lowE L b (d+1)) (lowE L b (d+4)) = cb at h
  cases ca with
  | none => cases h
  | some ca => cases cb with
    | none => cases h
    | some cb =>
      have ht := floatCmpL_bounds h
      have hr := floatKeyL_room ha
      exact (floatCompare_ok le (eval σ₀ a σ ρ).endlich (eval σ₀ b σ ρ).endlich h (by omega)
        (fun m pc hp => floatKeyE_ok σ₀ σ a iha ha (by omega) hp)
        (fun m pc hp => floatKeyE_ok σ₀ σ b ihb hb (by omega) hp) hp).mono fun w hw => by
          cases le
          · change Enc L .bool (gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x) w
            change w = Runner.IR.bool (gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x) at hw
            rw [hw]
            cases gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x <;> rfl
          · change Enc L .bool (gleitLe (eval σ₀ b σ ρ).x (eval σ₀ a σ ρ).x) w
            have hf := fle_flt (endlich_nicht_nan (eval σ₀ b σ ρ).endlich)
                (endlich_nicht_nan (eval σ₀ a σ ρ).endlich)
            change gleitLe (eval σ₀ b σ ρ).x (eval σ₀ a σ ρ).x =
              !gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x at hf
            rw [hf]
            change w = Runner.IR.bool (!gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x) at hw
            rw [hw]
            cases gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x <;> rfl

end Gabbro.Stage0.Senke
