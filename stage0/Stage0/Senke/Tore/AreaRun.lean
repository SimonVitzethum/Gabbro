/- Execution of a foreign request with one explicit hidden result argument. -/
module
public import Stage0.Senke.Anweisung.Bindung.Tor
public import Stage0.Senke.Anweisung.Puffer.Lauf
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Request preparation retains every source argument and zeros every unused
    register except the explicitly selected result-area register. -/
theorem areaRequest_run {O : Orakel D} [TorOK L O] {Γ : Ctx} {Λ : List (Res D)}
    {a : D.Ax} {b : TorB} {args : Args D Γ Λ (D.aparams a)}
    {τ : Ty} (he : D.aerg a = some τ)
    {j s reserved : Nat} {ca : List II} {ta : Nat}
    (bound : L.tor a = some b) (accepted : areaGut b (D.aparams a).length j = true)
    (arguments : lowR L args (s + 1) reserved = some (ca, ta))
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (capacity : max ta (foreignResultBase s + valueWords τ) ≤ Ks) (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K s (areaRequest b s (D.aparams a).length j ca) ρ reserved)
    (world : WeltAt m L σ) :
    ∃ m' tag, Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (areaRequest b s (D.aparams a).length j ca).length), fp⟩ m' ∧
      AgreeW L fp s K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some tag ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1 ∧
      AreaReply L O a b τ he (σ.fragt (.inl a)) (evalArgs σ args σ ρ)
        m' fp (foreignResultBase s) tag := by
  have ks := layout.ks
  have small : Ks < 2 ^ 31 := Nat.lt_of_le_of_lt ks pre.small
  have positive := valueWords_pos τ
  have enough : s + 10 ≤ Ks := by unfold foreignResultBase at capacity; omega
  have accepted' := accepted
  simp only [areaGut, Bool.and_eq_true, decide_eq_true_eq] at accepted'
  obtain ⟨⟨⟨⟨nj, j6⟩, registers⟩, number⟩, area⟩ := accepted'
  have pre0 : PreS L m pc fp K s
      (ca ++ (zeroC (s + 1 + (D.aparams a).length) (6 - (D.aparams a).length) ++
        ([ci 17 (s + 1 + j) (foreignResultBase s) 0] ++
          ([ci 1 s b.nr 0] ++ [ci 23 s s 0])))) ρ reserved := by
    simpa only [areaRequest, List.append_assoc, List.cons_append, List.nil_append] using pre
  have frame := frameOK_sub pre.frame ks
  have room := frame.room
  obtain ⟨m1, run1, change1, values⟩ := lowR_ok (same := rfl) σ σ (fun _ h => h) layout.lay
    args (s + 1) ca ta arguments (by omega) (by omega) m pc ρ
    (PreS.welt (pre0.left.up (by omega)) ks world layout.lay (by have := layout.lo; omega))
  have next1 := pre0.next (Agree.widen (change1.mono (Nat.le_succ s)) ks) (Nat.le_refl _) (by omega)
  obtain ⟨m2, run2, change2, zeros⟩ := zero_ok (K := Ks) small
    (6 - (D.aparams a).length) (s + 1 + (D.aparams a).length) m1 _ next1.left.code
    (by simpa only [zeroC_len] using codeFar_sub2 next1.left.far ks)
    (frame.agree change1) (by omega)
  have next2 := next1.next (Agree.widen (change2.mono (by omega)) ks) (Nat.le_refl _) (by omega)
  have run3 := lea_step (d := s + 1 + j) (a := foreignResultBase s) next2.left.code
    ((frame.agree change1).agree change2) (by omega) (by omega) small
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (s + 1 + j))) 8
    (slot fp (BitVec.ofNat 64 (foreignResultBase s))).toNat
  have change3 : Agree fp (s + 1 + j) Ks m2 m3 := agree_write room (Nat.le_refl _) (by omega) _
  have next3 := next2.next (Agree.widen (change3.mono (by omega)) ks) (Nat.le_refl _) (by omega)
  have frame3 := ((frame.agree change1).agree change2).agree change3
  have run4 := const_step (k := (b.nr : Int)) next3.left.code frame3 (by omega)
    (by have := pre.small; omega) number
  rw [BitVec.ofInt_natCast] at run4
  let m4 := write m3 (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofNat 64 b.nr).toNat
  have change4 : Agree fp s Ks m3 m4 := agree_write room (Nat.le_refl _) (by omega) _
  have frame4 := frame3.agree change4
  have next4 := next3.next (Agree.widen change4 ks) (Nat.le_refl _) (by omega)
  let values4 := fun i => rdW m4 fp (s + 1 + i)
  let request : Runner.Req := ⟨BitVec.ofNat 64 b.nr, values4 0, values4 1, values4 2,
    values4 3, values4 4, values4 5⟩
  have reads : ∀ i, i < 6 → m4.rd64 (slot fp (BitVec.ofNat 64 (s + 1 + i))) =
      some (reqArg request i) := by
    intro i hi
    rw [reqArg_mk _ values4 i hi]
    exact rd64_rdW frame4 (by omega)
  have kept4 : ∀ i, i < 6 → rdW m4 fp (s + 1 + i) = rdW m3 fp (s + 1 + i) := by
    intro i hi
    simp only [rdW, m4]
    rw [rd64_write_far (slot_far room (by omega) (by omega) (by omega))]
  have kept3 : ∀ i, i < 6 → i ≠ j → rdW m3 fp (s + 1 + i) = rdW m2 fp (s + 1 + i) := by
    intro i hi different
    simp only [rdW, m3]
    rw [rd64_write_far (slot_far room (by omega) (by omega) (by omega))]
  have sourceValues : ArgsW L (reqArg request) (evalArgs σ args σ ρ) := by
    refine argsW_congr (f := fun i => rdW m1 fp (s + 1 + i)) (g := reqArg request)
      (evalArgs σ args σ ρ) ?_ values
    intro i hi
    rw [reqArg_mk _ values4 i (by omega)]
    dsimp only [values4]
    rw [kept4 i (by omega), kept3 i (by omega) (by omega)]
    simp only [rdW]
    rw [agree_rd_low (i := s + 1 + i) change2 room (by omega) (by omega)]
  have hidden : reqArg request j = slot fp (BitVec.ofNat 64 (foreignResultBase s)) := by
    rw [reqArg_mk _ values4 j j6]
    dsimp only [values4]
    rw [kept4 j j6]
    exact rdW_of (rd64_write_same (((frame.agree change1).agree change2).rd _ (by omega)))
  have unused : ∀ i, (D.aparams a).length ≤ i → i < 6 → i ≠ j → reqArg request i = 0 := by
    intro i ni hi different
    rw [reqArg_mk _ values4 i hi]
    dsimp only [values4]
    rw [kept4 i hi, kept3 i hi different]
    have zero := zeros (i - (D.aparams a).length) (by omega)
    rw [show s + 1 + (D.aparams a).length + (i - (D.aparams a).length) = s + 1 + i by omega] at zero
    exact rdW_of zero
  have change14 : Agree fp s Ks m m4 := (change1.mono (Nat.le_succ s)).trans
    ((change2.mono (by omega)).trans ((change3.mono (by omega)).trans change4))
  have world4 := weltAt_stab layout.lay (by have := layout.lo; omega) m m4 world
    (change14.mono (Nat.zero_le _))
  obtain ⟨tag, extra, m5, service, changed5, world5, reply5⟩ :=
    TorOK.area a b τ he j bound accepted (σ.fragt (.inl a)) (evalArgs σ args σ ρ)
      request m4 fp (foreignResultBase s) Ks frame4 (by omega) layout.lay layout.lo rfl sourceValues hidden unused world4
  have numberRead : m4.rd64 (slot fp (BitVec.ofNat 64 s)) = some request.nr :=
    rd64_write_same (frame3.rd s (by omega))
  have run5 := sys_step next4.code frame4 (by omega) (by have := pre.small; omega)
    numberRead reads service changed5.wr
  let m6 := write m5 (slot fp (BitVec.ofNat 64 s)) 8 tag.toNat
  have change6 : Agree fp s Ks m5 m6 := agree_write room (Nat.le_refl _) (by omega) _
  have valueKept {v : Wert D τ} (value : ValueAt L m5 fp (foreignResultBase s) τ v) :
      ValueAt L m6 fp (foreignResultBase s) τ v := by
    refine ⟨value.1, ?_⟩
    intro i hi
    have length := encodeWords_length L τ v
    simp only [m6]
    rw [rd64_write_far (slot_far room (by omega) (by unfold foreignResultBase at *; omega)
      (by unfold foreignResultBase; omega))]
    exact value.2 i hi
  refine ⟨m6, tag, ?_, ?_, rd64_write_same (by rw [changed5.rd]; exact frame4.rd s (by omega)),
    weltAt_stab layout.lay (by have := layout.lo; omega) m5 m6 world5
      (change6.mono (Nat.zero_le _)), ?_⟩
  · have run2' : Star ⟨pc + BitVec.ofNat 64 (16 * ca.length), fp⟩ m1
        ⟨pc + BitVec.ofNat 64 (16 * ca.length) +
          BitVec.ofNat 64 (16 * (zeroC (s + 1 + (D.aparams a).length)
            (6 - (D.aparams a).length)).length), fp⟩ m2 := by
      simpa only [zeroC_len] using run2
    have combined := run1.trans (run2'.trans (run3.trans (run4.trans run5)))
    simpa only [areaRequest, List.length_append, List.length_cons, List.length_nil,
      List.length_singleton, zeroC_len, BitVec.ofInt_natCast, pc_add, addr_norm,
      Nat.mul_add, Nat.add_assoc] using combined
  · exact (agreeW_of (Agree.widen change14 ks)).trans
      (((changed5.widen (by omega)).mono (by unfold foreignResultBase; omega)).trans
        (agreeW_of (Agree.widen change6 ks)))
  · rcases reply5 with ⟨v, decoded, success, value⟩ | reason | invalid
    · exact .inl ⟨v, decoded, success, valueKept value⟩
    · exact .inr (.inl reason)
    · exact .inr (.inr invalid)

/-- The actual checked area emitter executes the request proved above. -/
theorem areaC_ok {O : Orakel D} [TorOK L O] {Γ : Ctx} {Λ : List (Res D)}
    {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ)
    {s reserved top : Nat} {code : List II}
    (emitted : areaC L a args τ s reserved = some (code, top))
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (capacity : top ≤ Ks) (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K s code ρ reserved) (world : WeltAt m L σ) :
    ∃ b, L.tor a = some b ∧ ∃ m' tag,
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      AgreeW L fp s K m m' ∧ m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some tag ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1 ∧
      AreaReply L O a b τ he (σ.fragt (.inl a)) (evalArgs σ args σ ρ)
        m' fp (foreignResultBase s) tag := by
  simp only [areaC, bind, Option.bind_eq_some_iff] at emitted
  obtain ⟨b, bound, j, register, emitted⟩ := emitted
  split at emitted
  · next accepted =>
    simp only [Bool.and_eq_true] at accepted
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at emitted
    obtain ⟨⟨ca, ta⟩, arguments, rfl, rfl⟩ := emitted
    exact ⟨b, bound, areaRequest_run he bound accepted.1 arguments capacity layout pre world⟩
  · cases emitted

end Gabbro.Stage0.Senke
