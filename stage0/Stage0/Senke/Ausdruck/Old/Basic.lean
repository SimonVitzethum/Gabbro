/- The immutable entry word and bounds of postcondition expression code. -/
import Stage0.Senke.Ausdruck.Old.Code

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxRecDepth 4096
variable [Kern]
variable {D : Deklaration} {L : Lay D}

def intValue : {τ : Ty} → Wert D τ → Option Int
  | .int _ _, v => some v.n
  | _, _ => none

theorem entryIndex_ok {Γ : Ctx} {Λ : List (Res D)} (σ0 σ : World D) (ρ : Env D Γ) :
    {τ : Ty} → (i : Expr D Γ Λ τ) → {k : Int} →
    entryIndex i = some k → intValue (eval σ0 i σ ρ) = some k
  | _, .lit _, _, h => by simp only [entryIndex] at h; exact h
  | _, .widen _ _ e, _, h => by
    simp only [entryIndex] at h
    exact entryIndex_ok σ0 σ ρ e h
  | _, e@(.tru ..), _, h
  | _, e@(.fls ..), _, h
  | _, e@(.var ..), _, h
  | _, e@(.glob ..), _, h
  | _, e@(.slot ..), _, h
  | _, e@(.thru ..), _, h
  | _, e@(.ptrOf ..), _, h
  | _, e@(.fnref ..), _, h
  | _, e@(.oldG ..), _, h
  | _, e@(.oldS ..), _, h
  | _, e@(.add ..), _, h
  | _, e@(.sub ..), _, h
  | _, e@(.neg ..), _, h
  | _, e@(.mul ..), _, h
  | _, e@(.div ..), _, h
  | _, e@(.rem ..), _, h
  | _, e@(.sdiv ..), _, h
  | _, e@(.srem ..), _, h
  | _, e@(.getBytes ..), _, h
  | _, e@(.band ..), _, h
  | _, e@(.bor ..), _, h
  | _, e@(.bxor ..), _, h
  | _, e@(.shl ..), _, h
  | _, e@(.shr ..), _, h
  | _, e@(.lt ..), _, h
  | _, e@(.le ..), _, h
  | _, e@(.eq ..), _, h
  | _, e@(.fllt ..), _, h
  | _, e@(.flle ..), _, h
  | _, e@(.and ..), _, h
  | _, e@(.or ..), _, h
  | _, e@(.not ..), _, h
  | _, e@(.none ..), _, h
  | _, e@(.some ..), _, h
  | _, e@(.istSome ..), _, h
  | _, e@(.case ..), _, h
  | _, e@(.why ..), _, h
  | _, e@(.forallSlots ..), _, h
  | _, e@(.existsSlots ..), _, h
  | _, e@(.reaches ..), _, h
  | _, e@(.refEq ..), _, h
  | _, e@(.slotRef ..), _, h
  | _, e@(.arrNil ..), _, h
  | _, e@(.arrCons ..), _, h
  | _, e@(.arrGet ..), _, h
  | _, e@(.arrSet ..), _, h
  | _, e@(.strLit ..), _, h
  | _, e@(.strLen ..), _, h
  | _, e@(.strCat ..), _, h
  | _, e@(.strGet ..), _, h
  | _, e@(.strEq ..), _, h
  | _, e@(.strLt ..), _, h
  | _, e@(.strWeit ..), _, h
  | _, e@(.wenn ..), _, h
  | _, e@(.eng ..), _, h => by subst e; simp only [entryIndex] at h; cases h

theorem SnapAt.agree {cs : List (Zelle D)} {σ0 : World D} {m m' : Runner.Mem}
    {fp : Runner.W} {K lo : Nat} (h : SnapAt L cs σ0 m fp) (hf : FrameOK m fp K)
    (ha : Agree fp lo K m m') (hl : 3 < lo) (hk : lo ≤ K) : SnapAt L cs σ0 m' fp := by
  intro c hc
  obtain ⟨w, hw, he⟩ := h c hc
  exact ⟨w, by rw [agree_rd_low ha hf.room hl hk]; exact hw, he⟩

theorem SnapAt.left {a b : List (Zelle D)} {σ0 : World D} {m : Runner.Mem} {fp : Runner.W}
    (h : SnapAt L (a ++ b) σ0 m fp) : SnapAt L a σ0 m fp :=
  fun c hc => h c (List.mem_append_left _ hc)

theorem SnapAt.right {a b : List (Zelle D)} {σ0 : World D} {m : Runner.Mem} {fp : Runner.W}
    (h : SnapAt L (a ++ b) σ0 m fp) : SnapAt L b σ0 m fp :=
  fun c hc => h c (List.mem_append_right _ hc)

theorem lowEns_top {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) → (top : Nat) →
    lowEns L e d = some (c, top) → d < top
  | _, .oldG .., d, c, top, h => by simp only [lowEns, Option.some.injEq, Prod.mk.injEq] at h; omega
  | _, .oldS _ _ i _, d, c, top, h => by
    simp only [lowEns, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _⟩ := h
    omega
  | _, .widen _ _ e, d, c, top, h => lowEns_top e d c top h
  | _, .add a b, d, c, top, h => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    have := lowEns_top a d ca ta ha
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .sub a b, d, c, top, h => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    have := lowEns_top a d ca ta ha
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .mul a b, d, c, top, h => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    have := lowEns_top a d ca ta ha
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .and a b, d, c, top, h => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    have := lowEns_top a d ca ta ha
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .or a b, d, c, top, h => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    have := lowEns_top a d ca ta ha
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .eq a b, d, c, top, h => by
    simp only [lowEns] at h
    split at h
    · next hw =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
      have := lowEns_top a d ca ta ha
      simp only [bin2, Prod.mk.injEq] at he
      omega
    · cases h
  | _, .lt a b, d, c, top, h => by
    simp only [lowEns] at h
    split at h
    · next hw =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
      have := lowEns_top a d ca ta ha
      simp only [bin2, Prod.mk.injEq] at he
      omega
    · cases h
  | _, e@(.lit ..), d, c, top, h
  | _, e@(.tru ..), d, c, top, h
  | _, e@(.fls ..), d, c, top, h
  | _, e@(.var ..), d, c, top, h
  | _, e@(.glob ..), d, c, top, h
  | _, e@(.slot ..), d, c, top, h
  | _, e@(.thru ..), d, c, top, h
  | _, e@(.ptrOf ..), d, c, top, h
  | _, e@(.fnref ..), d, c, top, h
  | _, e@(.neg ..), d, c, top, h
  | _, e@(.div ..), d, c, top, h
  | _, e@(.rem ..), d, c, top, h
  | _, e@(.sdiv ..), d, c, top, h
  | _, e@(.srem ..), d, c, top, h
  | _, e@(.getBytes ..), d, c, top, h
  | _, e@(.band ..), d, c, top, h
  | _, e@(.bor ..), d, c, top, h
  | _, e@(.bxor ..), d, c, top, h
  | _, e@(.shl ..), d, c, top, h
  | _, e@(.shr ..), d, c, top, h
  | _, e@(.le ..), d, c, top, h
  | _, e@(.fllt ..), d, c, top, h
  | _, e@(.flle ..), d, c, top, h
  | _, e@(.not ..), d, c, top, h
  | _, e@(.none ..), d, c, top, h
  | _, e@(.some ..), d, c, top, h
  | _, e@(.istSome ..), d, c, top, h
  | _, e@(.case ..), d, c, top, h
  | _, e@(.why ..), d, c, top, h
  | _, e@(.forallSlots ..), d, c, top, h
  | _, e@(.existsSlots ..), d, c, top, h
  | _, e@(.reaches ..), d, c, top, h
  | _, e@(.refEq ..), d, c, top, h
  | _, e@(.slotRef ..), d, c, top, h
  | _, e@(.arrNil ..), d, c, top, h
  | _, e@(.arrCons ..), d, c, top, h
  | _, e@(.arrGet ..), d, c, top, h
  | _, e@(.arrSet ..), d, c, top, h
  | _, e@(.strLit ..), d, c, top, h
  | _, e@(.strLen ..), d, c, top, h
  | _, e@(.strCat ..), d, c, top, h
  | _, e@(.strGet ..), d, c, top, h
  | _, e@(.strEq ..), d, c, top, h
  | _, e@(.strLt ..), d, c, top, h
  | _, e@(.strWeit ..), d, c, top, h
  | _, e@(.wenn ..), d, c, top, h
  | _, e@(.eng ..), d, c, top, h => by subst e; exact lowE_top _ d c top h

end Gabbro.Stage0.Senke
