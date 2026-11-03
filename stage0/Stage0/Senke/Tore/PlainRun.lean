/- The actual nonfallible foreign prefix preserves the complete value ABI. -/
module
public import Stage0.Senke.Tore.ForeignCode
public import Stage0.Senke.Tore.AreaReceive
public import Stage0.Senke.Anweisung.Bindung.TorBind
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem plainForeignC_ok {O : Orakel D} [TorOK L O] {Γ : Ctx} {Λ : List (Res D)}
    {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ)
    {reserved top : Nat} {code rest : List II}
    (emitted : plainForeignC L a args τ (frei Γ reserved) reserved = some (code, top))
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (capacity : top ≤ Ks) (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) (code ++ rest) ρ reserved)
    (world : WeltAt m L σ) :
    (∃ value m', axiomAntwort O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some value) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧
      ValueAt L m' fp (frei Γ reserved) τ (ergWert he value) ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (axiomAntwort O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, none) ∧
      Stops ⟨pc, fp⟩ m 110) := by
  simp only [plainForeignC] at emitted
  split at emitted
  · split at emitted
    · next noReasons =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at emitted
      obtain ⟨⟨request, requestTop⟩, requestMade, rfl, rfl⟩ := emitted
      have pre0 : PreS L m pc fp K (frei Γ reserved)
          (request ++ (areaReceive τ (frei Γ reserved) ++ rest)) ρ reserved := by
        simpa only [List.append_assoc] using pre
      obtain ⟨binding, bound, m1, tag, run1, change1, input, world1, reply⟩ :=
        areaC_ok he requestMade capacity layout pre0.left world
      have next := pre0.nextW layout change1 (by have := pre.ctx; omega) (Nat.le_refl _) (by omega)
      have span := Nat.le_trans (areaC_top requestMade) capacity
      rcases reply with ⟨value, decoded, success, payload⟩ | ⟨reason, errno, decoded, found⟩ |
          ⟨decoded, nonzero, missing⟩
      · have source : einpassenErg O.zeiger (D.aerg a)
            (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 = some value := by
          cases result : einpassenErg O.zeiger (D.aerg a)
              (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 with
          | none => simp only [foreignDecode, noReasons, ↓reduceIte, result, Option.map_none] at decoded; cases decoded
          | some value' =>
            simp only [foreignDecode, noReasons, ↓reduceIte, result, Option.map_some,
              Option.some.injEq, Sum.inl.injEq] at decoded
            cases decoded
            exact result
        obtain ⟨m2, run2, change2, value2⟩ :=
          (areaReceive_ok layout span next.left input).1 success payload
        refine .inl ⟨value, m2, ?_, ?_, change1.trans (agreeW_of (Agree.widen change2 layout.ks)), value2, ?_⟩
        · rw [axiomAntwort_eq, source]
        · exact run1.trans (by rw [List.length_append, ← pc_add]; exact run2)
        · exact weltAt_stab layout.lay (by have := layout.lo; omega) m1 m2 world1
            (change2.mono (Nat.zero_le _))
      · have impossible := reason.isLt
        rw [noReasons] at impossible
        omega
      · have source : einpassenErg O.zeiger (D.aerg a)
            (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 = none := by
          cases result : einpassenErg O.zeiger (D.aerg a)
              (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 with
          | none => exact result
          | some value =>
            simp only [foreignDecode, noReasons, ↓reduceIte, result, Option.map_some] at decoded
            cases decoded
        exact .inr ⟨by rw [axiomAntwort_eq, source],
          Stops.prefix run1 (areaReceive_nonzero layout span next.left input nonzero)⟩
    · cases emitted
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at emitted
    obtain ⟨⟨request, requestTop⟩, requestMade, check, checkMade, rfl, rfl⟩ := emitted
    exact torBind_ok he requestMade checkMade (by omega) (by omega) layout pre world

theorem plainForeignC_top {Γ : Ctx} {Λ : List (Res D)} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ)
    {s reserved top : Nat} {code : List II}
    (emitted : plainForeignC L a args τ s reserved = some (code, top)) :
    s + valueWords τ ≤ top := by
  simp only [plainForeignC] at emitted
  split at emitted
  · split at emitted
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at emitted
      obtain ⟨request, made, _, rfl⟩ := emitted
      have span := areaC_top made
      unfold foreignResultBase at span
      omega
    · cases emitted
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at emitted
    obtain ⟨request, made, check, checked, _, rfl⟩ := emitted
    have width := chkC_width (τ := τ) (by simpa only [he] using checked)
    omega

end Gabbro.Stage0.Senke
