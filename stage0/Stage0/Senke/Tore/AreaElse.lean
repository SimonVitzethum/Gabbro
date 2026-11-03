/- A fallible result-area call: tag dispatch before complete payload transport. -/
module
public import Stage0.Senke.Tore.AreaReceive
public import Stage0.Senke.Anweisung.FehlerLauf
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem areaElse_ok {O : Orakel D} [TorOK L O] {Γ : Ctx} {Λ : List (Res D)}
    {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ)
    {binding : TorB} (bound : L.tor a = some binding)
    (errors : fehlGut (D.agruende a) binding.fehler = true) (reasons : 0 < D.agruende a)
    {reserved top : Nat} {request success error : List II}
    (emitted : areaC L a args τ (frei Γ reserved) reserved = some (request, top))
    (jump : 16 + 16 * (6 * binding.fehler.length) +
      16 * ((areaReceive τ (frei Γ reserved)).length + success.length) < 2 ^ 31)
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (capacity : top ≤ Ks) (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (request ++ fehlC (frei Γ reserved) binding.fehler
        (16 * ((areaReceive τ (frei Γ reserved)).length + success.length)) ++
        areaReceive τ (frei Γ reserved) ++ success ++ error) ρ reserved)
    (world : WeltAt m L σ) :
    (∃ value m', axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inl value)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 *
        (request.length + 6 * binding.fehler.length + (areaReceive τ (frei Γ reserved)).length)), fp⟩ m' ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧
      ValueAt L m' fp (frei Γ reserved) τ (ergWert he value) ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (∃ reason m', axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inr reason)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 *
        (request.length + 6 * binding.fehler.length + (areaReceive τ (frei Γ reserved)).length + success.length)), fp⟩ m' ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 reason.val) ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, none) ∧
      Stops ⟨pc, fp⟩ m 110) := by
  have ks := layout.ks
  have span := Nat.le_trans (areaC_top emitted) capacity
  have positive := valueWords_pos τ
  have enough : frei Γ reserved + 10 ≤ Ks := by unfold foreignResultBase at span; omega
  have pre0 : PreS L m pc fp K (frei Γ reserved)
      (request ++ (fehlC (frei Γ reserved) binding.fehler
        (16 * ((areaReceive τ (frei Γ reserved)).length + success.length)) ++
          (areaReceive τ (frei Γ reserved) ++ (success ++ error)))) ρ reserved := by
    simpa only [List.append_assoc] using pre
  obtain ⟨binding', bound', m1, tag, run1, change1, input, world1, reply⟩ :=
    areaC_ok he emitted capacity layout pre0.left world
  have same : binding' = binding := Option.some.inj (bound'.symm.trans bound)
  subst binding'
  have next1 := pre0.nextW layout change1 (by have := pre.ctx; omega) (Nat.le_refl _) (by omega)
  have short : PreS L m1 _ fp (frei Γ reserved + 10) (frei Γ reserved + 1)
      (fehlC (frei Γ reserved) binding.fehler
        (16 * ((areaReceive τ (frei Γ reserved)).length + success.length))) ρ reserved :=
    ⟨by have := pre.ctx; omega, by have := pre.small; omega,
      frameOK_sub next1.frame (by omega), next1.left.code,
      codeFar_sub2 next1.left.far (by omega), next1.env, trivial, wstab_true _ _⟩
  have dispatch := fehlC_ok binding.fehler
    (16 * ((areaReceive τ (frei Γ reserved)).length + success.length)) m1 _ short errors
      (by omega) (by simp only [Int.natCast_add, Int.natCast_mul]; omega) (by omega) input
  have decode : ∀ result, foreignDecode O a
      (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 = result →
      axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, result) := by
    intro result decoded
    rw [foreignDecode_positive reasons] at decoded
    rw [axiomAntwortSonst_eq, decoded]
  rcases reply with ⟨value, decoded, zero, payload⟩ | ⟨reason, errno, decoded, found⟩ |
      ⟨decoded, nonzero, missing⟩
  · have missing : binding.fehler.find? (fun entry => entry.1 == tag.toInt) = none := by
      rw [zero]
      apply List.find?_eq_none.mpr
      intro entry member
      simp only [fehlGut, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at errors
      have valid := errors entry member
      change (entry.1 == (0 : Int)) = false
      simp only [beq_eq_false_iff_ne]
      omega
    rw [missing] at dispatch
    obtain ⟨m2, run2, change2⟩ := dispatch
    have next2 := next1.next (Agree.widen (change2.mono (Nat.le_succ _)) (by omega))
      (Nat.le_refl _) (by omega)
    simp only [fehlC_len] at next2
    have payload2 : ValueAt L m2 fp (foreignResultBase (frei Γ reserved)) τ (ergWert he value) := by
      refine ⟨payload.1, ?_⟩
      intro i hi
      have length := encodeWords_length L τ (ergWert he value)
      rw [agree_rd_high change2 (frameOK_sub next1.frame ks).room
        (by unfold foreignResultBase; omega) (by omega)]
      exact payload.2 i hi
    have input2 : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some tag := by
      rw [agree_rd_low change2 short.frame.room (by omega) (by omega)]
      exact input
    obtain ⟨m3, run3, change3, output⟩ := (areaReceive_ok layout span next2.left input2).1 zero payload2
    refine .inl ⟨value, m3, decode _ decoded, ?_, ?_, output, ?_⟩
    · have run12 := run1.trans run2
      simpa only [fehlC_len, pc_add] using run12.trans run3
    · exact change1.trans (agreeW_of (((Agree.widen change2 (by omega)).mono (Nat.le_succ _)).trans
        (Agree.widen change3 ks)))
    · exact weltAt_stab layout.lay (by have := layout.lo; omega) m1 m3 world1
        (((Agree.widen change2 enough).mono (Nat.le_succ _)).trans change3 |>.mono (Nat.zero_le _))
  · rw [found] at dispatch
    obtain ⟨m2, run2, change2, output⟩ := dispatch
    refine .inr (.inl ⟨reason, m2, decode _ decoded, run1.trans (star_cast run2 rfl ?_),
      change1.trans (agreeW_of (Agree.widen change2 (by omega))), output,
      weltAt_stab layout.lay (by have := layout.lo; omega) m1 m2 world1
        ((Agree.widen change2 enough).mono (Nat.zero_le _))⟩)
    rw [adr_int, show ((16 * request.length : Nat) : Int) +
      (16 * (6 * (binding.fehler.length : Int)) +
        ((16 * ((areaReceive τ (frei Γ reserved)).length + success.length) : Nat) : Int)) =
      ((16 * (request.length + 6 * binding.fehler.length +
        (areaReceive τ (frei Γ reserved)).length + success.length) : Nat) : Int) by
        simp only [Int.natCast_add, Int.natCast_mul]; omega, BitVec.ofInt_natCast]
  · rw [missing] at dispatch
    obtain ⟨m2, run2, change2⟩ := dispatch
    have next2 := next1.next (Agree.widen (change2.mono (Nat.le_succ _)) (by omega))
      (Nat.le_refl _) (by omega)
    simp only [fehlC_len] at next2
    have input2 : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some tag := by
      rw [agree_rd_low change2 short.frame.room (by omega) (by omega)]
      exact input
    exact .inr (.inr ⟨decode _ decoded, Stops.prefix (run1.trans run2)
      (areaReceive_nonzero layout span next2.left input2 nonzero)⟩)

end Gabbro.Stage0.Senke
