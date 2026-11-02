/- Bounds for complete snapshot-aware postcondition expression code. -/
module
public import Stage0.Senke.Ausdruck.Old.Code
@[expose] public section


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
  | _, .add a b, _, h => by
    obtain ⟨x, hx, y, hy, rfl⟩ := (show ∃ x, entryIndex a = some x ∧ ∃ y, entryIndex b = some y ∧ x + y = _ by simpa [entryIndex, Option.bind_eq_some_iff] using h)
    have ha := entryIndex_ok σ0 σ ρ a hx
    have hb := entryIndex_ok σ0 σ ρ b hy
    simp only [intValue] at ha hb
    simp only [intValue, eval, Zahl.add]
    rw [Option.some.inj ha, Option.some.inj hb]
  | _, .sub a b, _, h => by
    obtain ⟨x, hx, y, hy, rfl⟩ := (show ∃ x, entryIndex a = some x ∧ ∃ y, entryIndex b = some y ∧ x - y = _ by simpa [entryIndex, Option.bind_eq_some_iff] using h)
    have ha := entryIndex_ok σ0 σ ρ a hx
    have hb := entryIndex_ok σ0 σ ρ b hy
    simp only [intValue] at ha hb
    simp only [intValue, eval, Zahl.sub]
    rw [Option.some.inj ha, Option.some.inj hb]
  | _, .mul a b, _, h => by
    obtain ⟨x, hx, y, hy, rfl⟩ := (show ∃ x, entryIndex a = some x ∧ ∃ y, entryIndex b = some y ∧ x * y = _ by simpa [entryIndex, Option.bind_eq_some_iff] using h)
    have ha := entryIndex_ok σ0 σ ρ a hx
    have hb := entryIndex_ok σ0 σ ρ b hy
    simp only [intValue] at ha hb
    simp only [intValue, eval, Zahl.mul]
    rw [Option.some.inj ha, Option.some.inj hb]
  | _, .neg a, _, h => by
    obtain ⟨x, hx, rfl⟩ := (show ∃ x, entryIndex a = some x ∧ -x = _ by simpa [entryIndex, Option.bind_eq_some_iff] using h)
    have ha := entryIndex_ok σ0 σ ρ a hx
    simpa [intValue, eval, Zahl.neg] using congrArg (fun x : Int => some (-x)) (Option.some.inj ha)
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
  | _, e@(.intBuiltin1 ..), _, h
  | _, e@(.intBuiltin2 ..), _, h
  | _, e@(.count ..), _, h
  | _, e@(.prod ..), _, h
  | _, e@(.prodGet ..), _, h
  | _, e@(.prodSet ..), _, h
  | _, e@(.eng ..), _, h => by subst e; simp only [entryIndex] at h; cases h

theorem lowEnsAt_top (layout : FrameLayout) (start : Nat) {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) → (top : Nat) →
    lowEnsAt L layout start e d = some (c, top) → d < top
  | _, .oldG g _, d, c, top, h => by
    have := valueWords_pos (D.gtyp g)
    simp only [lowEnsAt, Option.some.injEq, Prod.mk.injEq] at h
    omega
  | _, .oldS t f i _, d, c, top, h => by
    cases index : entryIndex i with
    | some k =>
      have := valueWords_pos (D.typ t f)
      simp only [lowEnsAt, index, Option.some.injEq, Prod.mk.injEq] at h
      omega
    | none =>
      simp only [lowEnsAt, index] at h
      split at h
      · exact entryColumnL_top h
      · cases h
  | _, .widen _ _ e, d, c, top, h =>
    resizeIntegerL_top h (fun cc tt hc => lowEnsAt_top layout start e d cc tt hc)
  | _, .not a, d, c, top, h => by
    simp only [lowEnsAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, _, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .add a b, d, c, top, h =>
      wideBinaryL_top (by simpa only [lowEnsAt, wideAddL] using h)
  | _, .sub a b, d, c, top, h =>
      wideBinaryL_top (by simpa only [lowEnsAt, wideSubL] using h)
  | _, .mul a b, d, c, top, h =>
      wideBinaryL_top (by simpa only [lowEnsAt, wideMulL] using h)
  | _, .neg a, d, c, top, h =>
      wideUnaryL_top (by simpa only [lowEnsAt, wideNegL] using h)
  | _, .and a b, d, c, top, h => by
    simp only [lowEnsAt] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    have := lowEnsAt_top layout start a d ca ta ha
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .or a b, d, c, top, h => by
    simp only [lowEnsAt] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    have := lowEnsAt_top layout start a d ca ta ha
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, .eq a b, d, c, top, h =>
      wideBinaryL_top (by simpa only [lowEnsAt, wideEqL] using h)
  | _, .lt a b, d, c, top, h =>
      wideBinaryL_top (by simpa only [lowEnsAt, wideLtL] using h)
  | _, .le a b, d, c, top, h =>
      wideBinaryL_top (by simpa only [lowEnsAt, wideLeL] using h)
  | _, .intBuiltin1 op a, d, c, top, h => BitBuiltin.unary_top op h
  | _, .intBuiltin2 op a b, d, c, top, h => intBuiltin2L_top op h
  | _, e@(.lit ..), d, c, top, h
  | _, e@(.tru ..), d, c, top, h
  | _, e@(.fls ..), d, c, top, h
  | _, e@(.var ..), d, c, top, h
  | _, e@(.glob ..), d, c, top, h
  | _, e@(.slot ..), d, c, top, h
  | _, e@(.thru ..), d, c, top, h
  | _, e@(.ptrOf ..), d, c, top, h
  | _, e@(.fnref ..), d, c, top, h
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
  | _, e@(.fllt ..), d, c, top, h
  | _, e@(.flle ..), d, c, top, h
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
  | _, e@(.count ..), d, c, top, h
  | _, e@(.prod ..), d, c, top, h
  | _, e@(.prodGet ..), d, c, top, h
  | _, e@(.prodSet ..), d, c, top, h
  | _, e@(.eng ..), d, c, top, h => by subst e; exact lowE_top (reserved := layout.ensReserved) _ d c top h


theorem lowEns_top (layout : FrameLayout) {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (e : Expr D Γ Λ τ) (d : Nat) (code : List II) (top : Nat)
    (emitted : lowEns L layout e d = some (code, top)) : d < top :=
    lowEnsAt_top layout layout.snapshotBase e d code top emitted

end Gabbro.Stage0.Senke
