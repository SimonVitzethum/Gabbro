/- Foreign bindings use one canonical checked answer transport. -/
module
public import Stage0.Senke.Anweisung.Bindung.Answer
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- **A gate bound in a block** (`bindAxiom`): the call, then the test of its answer. Inside the range the value is in
    slot `frei Γ` and the oracle's world in memory; outside it, G has no answer and the code stops with 110. -/
theorem torBind_ok {reserved : Nat} {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ) {ct ck cr : List II} {tt : Nat}
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (ht : torC0 L a args (frei Γ reserved) reserved = some (ct, tt)) (hck : chkC (D.aerg a) (frei Γ reserved) = some ck)
    (htt : tt ≤ Ks) (htk : frei Γ reserved + 10 ≤ Ks) (hW : WIn L fp Ks K) (hp : PreS L m pc fp K (frei Γ reserved) (ct ++ ck ++ cr) ρ reserved)
    (hWa : WeltAt m L σ) :
    (∃ v m2, axiomAntwort O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some v) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ct ++ ck).length), fp⟩ m2 ∧ AgreeW L fp (frei Γ reserved) K m m2 ∧
      ValueAt L m2 fp (frei Γ reserved) τ (ergWert he v) ∧
      WeltAt m2 L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (axiomAntwort O a σ (evalArgs σ args σ ρ) = ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, none) ∧
      Stops ⟨pc, fp⟩ m 110) := by
  have hks := hW.ks
  have hck' : chkC (some τ) (frei Γ reserved) = some ck := by simpa only [he] using hck
  have width := chkC_width hck'
  have hp' : PreS L m pc fp K (frei Γ reserved) (ct ++ (ck ++ cr)) ρ reserved :=
    (List.append_assoc ct ck cr) ▸ hp
  obtain ⟨m1, w, run, changed, input, world, raw⟩ := torC0_ok (O := O) ht htt hW hp'.left hWa
  have next := hp'.nextW hW changed (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
  have pre : PreS L m1 _ fp Ks (frei Γ reserved) ck ρ reserved :=
    ⟨hp.ctx, by have := hp.small; omega, frameOK_sub next.frame hks, next.left.code,
      codeFar_sub2 next.left.far hks, next.env, trivial, wstab_true _ _⟩
  have bound : L.tor a ≠ none := by
    simp only [torC0] at ht
    split at ht
    · exact torC_bound ht
    · cases ht
  have noReasons : D.agruende a = 0 := by
    simp only [torC0] at ht
    split at ht
    · assumption
    · cases ht
  have valid : ∀ n, τ = .ref n → 0 ≤ w.toInt →
      ValueValid L (.ref n) (Val.vonZelle w.toInt.toNat) := by
    intro n type nonnegative
    exact TorOK.ref_answer a n (he.trans (congrArg some type)) bound
      (σ.fragt (.inl a)) (evalArgs σ args σ ρ) w.toInt (.inl ⟨noReasons, raw.symm⟩) nonnegative
  have checked := chkAnswer_ok (z := O.zeiger) he hck' pre htk input valid
  rw [axiomAntwort_eq, raw]
  cases result : einpassenErg O.zeiger (D.aerg a) w.toInt with
  | some v =>
    rw [result] at checked
    obtain ⟨m2, w2, run2, changed2, output, encoded⟩ := checked
    refine .inl ⟨v, m2, rfl, ?_, changed.trans (agreeW_of (Agree.widen changed2 hks)),
      ValueAt.of_enc width output encoded, ?_⟩
    · exact run.trans (by rw [List.length_append, ← pc_add]; exact run2)
    · exact weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 world
        (changed2.mono (Nat.zero_le _))
  | none =>
    rw [result] at checked
    exact .inr ⟨rfl, Stops.prefix run checked⟩

end Gabbro.Stage0.Senke
