/- Postcondition expressions compute G's value with the captured entry word. -/
import Stage0.Senke.Ausdruck.Old.Basic

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxRecDepth 4096
variable [Kern]
variable {D : Deklaration} {L : Lay D}

theorem lowEns_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop}
    (σ0 σ : World D) (hWL : ∀ m, W m → WeltAt m L σ) :
    {Γ : Ctx} → {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) → (top : Nat) →
    lowEns L e d = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre L m pc fp K d c ρ W → SnapAt L (oldCells e) σ0 m fp →
    Ok m pc fp K d c (Enc L τ (eval σ0 e σ ρ))
  | _, _, .oldG g _, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, hw, he⟩ := hs (.glob g) (by simp [oldCells])
    have hctx := hp.ctx
    simp only [frei] at hctx
    have : FB = 4 := rfl
    exact (mov_ok (s := 3) hp (by omega) (by omega) hw).mono fun _ h => h ▸ he
  | _, _, .oldS t f i _, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨k, hk, rfl, rfl⟩ := h
    obtain ⟨w, hw, he⟩ := hs (.elem t f k.toNat) (by simp [oldCells, hk])
    have heval := entryIndex_ok σ0 σ ρ i hk
    simp only [intValue, Option.some.injEq] at heval
    have hk0 : 0 ≤ k := by have := (eval σ0 i σ ρ).lo_le; change 0 ≤ _ at this; omega
    have hctx := hp.ctx
    simp only [frei] at hctx
    have : FB = 4 := rfl
    refine (mov_ok (s := 3) hp (by omega) (by omega) hw).mono fun _ h => ?_
    subst h
    simpa only [eval, heval, Zelle.ty, Zelle.val, Int.toNat_of_nonneg hk0] using he
  | _, _, .widen _ _ e, d, c, top, h, hK, m, pc, ρ, hp, hs => lowEns_ok σ0 σ hWL e d c top h hK m pc ρ hp hs
  | _, _, .add a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowEns_top b (d + 1) cb tb hb
    have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
    have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
    refine bin_ok_keep (lowEns_ok σ0 σ hWL a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left)
      (fun m' pc' hag hp' => lowEns_ok σ0 σ hWL b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
        ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right))
      (g := fun x y => some (x + y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_add]; rfl⟩
  | _, _, .sub a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowEns_top b (d + 1) cb tb hb
    have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
    have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
    refine bin_ok_keep (lowEns_ok σ0 σ hWL a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left)
      (fun m' pc' hag hp' => lowEns_ok σ0 σ hWL b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
        ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right))
      (g := fun x y => some (x - y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← ofInt_sub']; rfl⟩
  | _, _, .mul a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowEns_top b (d + 1) cb tb hb
    have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
    have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
    refine bin_ok_keep (lowEns_ok σ0 σ hWL a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left)
      (fun m' pc' hag hp' => lowEns_ok σ0 σ hWL b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
        ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right))
      (g := fun x y => some (x * y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_mul]; rfl⟩
  | _, _, .and a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowEns_top b (d + 1) cb tb hb
    have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
    have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
    refine bin_ok_keep (lowEns_ok σ0 σ hWL a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left)
      (fun m' pc' hag hp' => lowEns_ok σ0 σ hWL b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
        ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right))
      (g := fun x y => some (x &&& y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact and_word _ _
  | _, _, .or a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowEns_top b (d + 1) cb tb hb
    have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
    have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
    refine bin_ok_keep (lowEns_ok σ0 σ hWL a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left)
      (fun m' pc' hag hp' => lowEns_ok σ0 σ hWL b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
        ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right))
      (g := fun x y => some (x ||| y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact or_word _ _
  | _, _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true] at hw
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := lowEns_top b (d + 1) cb tb hb
      have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
      have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
      refine bin_ok_keep (lowEns_ok σ0 σ hWL a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left)
        (fun m' pc' hag hp' => lowEns_ok σ0 σ hWL b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
          ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right))
        (g := fun x y => some (Runner.IR.bool (x.slt y))) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at pa pb ⊢
      rw [pa, pb, slt_in (inW_spec hw.1 (eval σ0 a σ ρ).lo_le (eval σ0 a σ ρ).le_hi)
        (inW_spec hw.2 (eval σ0 b σ ρ).lo_le (eval σ0 b σ ρ).le_hi), bool_word]
      rfl
    · cases h
  | _, _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true] at hw
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := lowEns_top b (d + 1) cb tb hb
      have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
      have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
      refine bin_ok_keep (lowEns_ok σ0 σ hWL a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left)
        (fun m' pc' hag hp' => lowEns_ok σ0 σ hWL b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
          ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right))
        (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at pa pb ⊢
      rw [pa, pb, beq_in (inW_spec hw.1 (eval σ0 a σ ρ).lo_le (eval σ0 a σ ρ).le_hi)
        (inW_spec hw.2 (eval σ0 b σ ρ).lo_le (eval σ0 b σ ρ).le_hi), bool_word]
      rfl
    · cases h
  | _, _, e@(.lit ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.tru ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.fls ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.var ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.glob ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.slot ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.thru ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.ptrOf ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.fnref ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.neg ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.div ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.rem ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.sdiv ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.srem ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.getBytes ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.band ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.bor ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.bxor ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.shl ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.shr ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.le ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.fllt ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.flle ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.not ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.none ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.some ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.istSome ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.case ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.why ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.forallSlots ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.existsSlots ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.reaches ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.refEq ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.slotRef ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.arrNil ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.arrCons ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.arrGet ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.arrSet ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.strLit ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.strLen ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.strCat ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.strGet ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.strEq ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.strLt ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.strWeit ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.wenn ..), d, c, top, h, hK, m, pc, ρ, hp, _
  | _, _, e@(.eng ..), d, c, top, h, hK, m, pc, ρ, hp, _ => by subst e; exact lowE_ok σ0 σ hWL _ d c top h hK m pc ρ hp

end Gabbro.Stage0.Senke
