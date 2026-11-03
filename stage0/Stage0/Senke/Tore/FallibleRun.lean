/- One connected fallible foreign theorem for complete values and nominal errors. -/
module
public import Stage0.Senke.Tore.Code
public import Stage0.Senke.Tore.AreaElse
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem fallibleForeignC_ok {O : Orakel D} [TorOK L O] {Γ : Ctx} {Λ : List (Res D)}
    {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ)
    {reserved top : Nat} {code success error : List II}
    (emitted : fallibleForeignC L a args τ (frei Γ reserved) success.length reserved = some (code, top))
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (capacity : top ≤ Ks) (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) (code ++ success ++ error) ρ reserved)
    (world : WeltAt m L σ) :
    (∃ value m', axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inl value)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧
      ValueAt L m' fp (frei Γ reserved) τ (ergWert he value) ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (∃ reason m', axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inr reason)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (code.length + success.length)), fp⟩ m' ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 reason.val) ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, none) ∧
      Stops ⟨pc, fp⟩ m 110) := by
  simp only [fallibleForeignC, bind, Option.bind_eq_some_iff] at emitted
  obtain ⟨binding, bound, emitted⟩ := emitted
  split at emitted
  · next accepted =>
    obtain ⟨errors, reasons, reasonWidth⟩ := accepted
    simp only [bind, Option.bind_eq_some_iff] at emitted
    obtain ⟨⟨⟨request, requestTop⟩, check⟩, selected, emitted⟩ := emitted
    split at emitted
    · next jump =>
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at emitted
      obtain ⟨rfl, rfl⟩ := emitted
      split at selected
      · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at selected
        obtain ⟨⟨request', requestTop'⟩, requestMade, same, rfl⟩ := selected
        cases same
        have run := areaElse_ok (O := O) he bound errors reasons requestMade jump
          (by omega) layout (by simpa only [List.append_assoc] using pre) world
        simpa only [List.length_append, fehlC_len] using run
      · split at selected
        · next scalar =>
          simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at selected
          obtain ⟨⟨request', requestTop'⟩, requestMade, check', checkMade, same, rfl⟩ := selected
          cases same
          have run := torElse_ok (O := O) he he bound errors scalar reasons requestMade checkMade jump
            (by omega) (by omega) layout (by simpa only [List.append_assoc] using pre) world
          rcases run with ⟨value, m', word, decoded, steps, changed, read, encoded, world'⟩ |
              ⟨reason, m', decoded, steps, changed, read, world'⟩ | invalid
          · exact .inl ⟨value, m', decoded, by simpa only [List.length_append, fehlC_len] using steps,
              changed, ValueAt.of_enc (chkC_width checkMade) read encoded, world'⟩
          · exact .inr (.inl ⟨reason, m', decoded, by simpa only [List.length_append, fehlC_len] using steps,
              changed, read, world'⟩)
          · exact .inr (.inr invalid)
        · cases selected
    · cases emitted
  · cases emitted

/-- All consumers reserve the full normal value, plus one word for the exact
    reason channel. This is independent of the selected transport profile. -/
theorem fallibleForeignC_top {Γ : Ctx} {Λ : List (Res D)} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {τ : Ty} {s skip reserved top : Nat} {code : List II}
    (emitted : fallibleForeignC L a args τ s skip reserved = some (code, top)) :
    s + valueWords τ ≤ top ∧ s + 10 ≤ top ∧ valueWords (.why (D.agruende a)) = 1 := by
  simp only [fallibleForeignC, bind, Option.bind_eq_some_iff] at emitted
  obtain ⟨binding, bound, emitted⟩ := emitted
  split at emitted
  · next accepted =>
    obtain ⟨errors, reasons, reasonWidth⟩ := accepted
    simp only [bind, Option.bind_eq_some_iff] at emitted
    obtain ⟨⟨⟨request, requestTop⟩, check⟩, selected, emitted⟩ := emitted
    split at emitted
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at emitted
      obtain ⟨rfl, rfl⟩ := emitted
      refine ⟨?_, by omega, reasonWidth⟩
      split at selected
      · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at selected
        obtain ⟨⟨request', requestTop'⟩, requestMade, same, rfl⟩ := selected
        cases same
        have span := areaC_top requestMade
        unfold foreignResultBase at span
        omega
      · split at selected
        · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at selected
          obtain ⟨⟨request', requestTop'⟩, requestMade, check', checkMade, same, rfl⟩ := selected
          have width := chkC_width checkMade
          omega
        · cases selected
    · cases emitted
  · cases emitted

end Gabbro.Stage0.Senke
