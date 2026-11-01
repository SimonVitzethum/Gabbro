/- Postcondition expressions compute G's value with the captured entry word. -/
import Stage0.Senke.Ausdruck.Old.Basic

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxRecDepth 4096
variable [Kern]
variable {D : Deklaration} {L : Lay D}

/-- The one-word snapshot profile copies a complete canonical value. -/
theorem snapshot_move {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {τ : Ty} {v : Wert D τ} {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    (pre : Pre L m pc fp K d [ci 2 d 3 0] ρ W)
    (width : valueWords τ = 1) (value : ValueAt L m fp 3 τ v) (fits : d + 1 ≤ K) :
    ValueOk L m pc fp K d [ci 2 d 3 0] τ v := by
  have ctx := pre.ctx
  have low : 4 ≤ d := by unfold frei FB at ctx; omega
  have code : CodeAt m pc (copyWords (valueWords τ) d 3) := by
    simpa [width, copyWords, ci] using pre.code
  have far : CodeFar pc (valueWords τ) fp K := by simpa [width] using pre.far
  obtain ⟨m', run, changed, output⟩ := copyValue_run pre.frame pre.small
    (by omega) (by omega) (Or.inr (by omega)) code far value
  refine ⟨m', ?_, ?_, output⟩
  · simpa [width] using run
  · exact ⟨changed.rd, changed.wr, fun a ha => changed.b a (by
      intro ⟨lower, upper⟩
      apply ha
      exact ⟨lower, by unfold inSlots at *; omega⟩)⟩

theorem lowEns_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop}
    (σ0 σ : World D) (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L) :
    {Γ : Ctx} → {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) → (top : Nat) →
    lowEns L e d = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre L m pc fp K d c ρ W → SnapAt L (oldCells e) σ0 m fp →
    ValueOk L m pc fp K d c τ (eval σ0 e σ ρ)
  | _, _, .oldG g _, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    split at h
    · next width =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      have value := (hs (.glob g) (by simp [oldCells])).2
      exact snapshot_move hp width value (by omega)
    · cases h
  | _, _, .oldS t f i _, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    split at h
    · next width =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨k, hk, rfl, rfl⟩ := h
      have value := (hs (.elem t f k.toNat) (by simp [oldCells, hk])).2
      have heval := entryIndex_ok σ0 σ ρ i hk
      simp only [intValue, Option.some.injEq] at heval
      have hk0 : 0 ≤ k := by have := (eval σ0 i σ ρ).lo_le; change 0 ≤ _ at this; omega
      have run := snapshot_move hp width value (by omega)
      simpa only [eval, heval, Zelle.ty, Zelle.val, Int.toNat_of_nonneg hk0] using run
    · cases h
  | _, _, .widen lower upper e, d, c, top, h, hK, m, pc, ρ, hp, hs =>
    resizeIntegerL_ok (eval σ0 e σ ρ) (Zahl.weiter lower upper (eval σ0 e σ ρ)) rfl
      (fun cc tt hc ht hp => lowEns_ok σ0 σ hWL hLay e d cc tt hc ht m pc ρ hp hs) h hK hp
  | _, _, .add a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    split at h
    · next width =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := lowEns_top b (d + 1) cb tb hb
      have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
      have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
      refine Ok.value (width := width) ?_
      refine bin_ok_keep ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left).word trivial)
        (fun m' pc' hag hp' => (lowEns_ok σ0 σ hWL hLay b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
          ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right)).word trivial)
        (g := fun x y => some (x + y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_add]; rfl⟩
    · cases h
  | _, _, .sub a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    split at h
    · next width =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := lowEns_top b (d + 1) cb tb hb
      have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
      have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
      refine Ok.value (width := width) ?_
      refine bin_ok_keep ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left).word trivial)
        (fun m' pc' hag hp' => (lowEns_ok σ0 σ hWL hLay b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
          ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right)).word trivial)
        (g := fun x y => some (x - y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← ofInt_sub']; rfl⟩
    · cases h
  | _, _, .mul a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    split at h
    · next width =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := lowEns_top b (d + 1) cb tb hb
      have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
      have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
      refine Ok.value (width := width) ?_
      refine bin_ok_keep ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left).word trivial)
        (fun m' pc' hag hp' => (lowEns_ok σ0 σ hWL hLay b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
          ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right)).word trivial)
        (g := fun x y => some (x * y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_mul]; rfl⟩
    · cases h
  | _, _, .and a b, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowEns_top b (d + 1) cb tb hb
    have hctx : FB ≤ d := by have := hp.ctx; simp only [frei] at this; omega
    have hsp : SnapAt L (oldCells a ++ oldCells b) σ0 m fp := hs
    refine Ok.value (width := rfl) ?_
    refine bin_ok_keep ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left).word trivial)
      (fun m' pc' hag hp' => (lowEns_ok σ0 σ hWL hLay b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
        ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right)).word trivial)
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
    refine Ok.value (width := rfl) ?_
    refine bin_ok_keep ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left).word trivial)
      (fun m' pc' hag hp' => (lowEns_ok σ0 σ hWL hLay b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
        ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right)).word trivial)
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
      refine Ok.value (width := rfl) ?_
      refine bin_ok_keep ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left).word trivial)
        (fun m' pc' hag hp' => (lowEns_ok σ0 σ hWL hLay b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
          ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right)).word trivial)
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
      refine Ok.value (width := rfl) ?_
      refine bin_ok_keep ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hsp.left).word trivial)
        (fun m' pc' hag hp' => (lowEns_ok σ0 σ hWL hLay b (d + 1) cb tb hb (by omega) m' pc' ρ hp'
          ((hsp.agree hp.frame hag (by unfold FB at hctx; omega) (by omega)).right)).word trivial)
        (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at pa pb ⊢
      rw [pa, pb, beq_in (inW_spec hw.1 (eval σ0 a σ ρ).lo_le (eval σ0 a σ ρ).le_hi)
        (inW_spec hw.2 (eval σ0 b σ ρ).lo_le (eval σ0 b σ ρ).le_hi), bool_word]
      rfl
    · cases h
  | _, _, .not a, d, c, top, h, hK, m, pc, ρ, hp, hs => by
    simp only [lowEns, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowEns_top a d ca ta ha
    refine Ok.value (width := rfl) ?_
    refine bin_ok_keep (cb := [ci 1 (d + 1) 1 0])
      ((lowEns_ok σ0 σ hWL hLay a d ca ta ha (by omega) m pc ρ hp.left.left hs).word trivial)
      (fun _ _ _ hp' => const_ok hp' (by decide) (by omega))
      (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact not_word _
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
  | _, _, e@(.eng ..), d, c, top, h, hK, m, pc, ρ, hp, _ => by subst e; exact lowE_ok σ0 σ hWL hLay _ d c top h hK m pc ρ hp

end Gabbro.Stage0.Senke
