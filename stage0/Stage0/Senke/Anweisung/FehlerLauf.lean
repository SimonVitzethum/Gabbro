/-
  File:      stage0/Stage0/Senke/Anweisung/FehlerLauf.lean
  Subject:   **A fallible gate** (`bindAxiomElse`, `torElse_ok`): the call, the errno tests, the range test. G's three
             answers each meet the code: a value runs on to the rest, a reason jumps to the `else` block with the case
             in slot `frei Γ`, no answer stops with 110.
-/
import Stage0.Senke.Anweisung.Fehler

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem axiomAntwortSonst_eq (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwortSonst O a σ ρ = ((O.wirkt a (σ.fragt (.inl a)) ρ).1,
      sonstPasst O.zeiger (D.aerg a) (D.agruende a) (O.wirkt a (σ.fragt (.inl a)) ρ).2) := rfl

theorem torElse_ok {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ) {lo' hi' : Int}
    (hτ : D.aerg a = some (.int lo' hi')) {b : TorB} (hb : L.tor a = some b)
    (hf : fehlGut (D.agruende a) b.fehler = true) (hlo : 0 ≤ lo') (hn : 0 < D.agruende a)
    {reserved : Nat} {ct ck cr ce : List II} {tt : Nat} (ht : torC L a args (frei Γ reserved) reserved = some (ct, tt))
    (hck : chkC (some (.int lo' hi')) (frei Γ reserved) = some ck)
    (hJ : 16 + 16 * (6 * b.fehler.length) + 16 * (ck.length + cr.length) < 2 ^ 31)
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (htt : tt ≤ Ks) (htk : frei Γ reserved + 10 ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K (frei Γ reserved)
      (ct ++ fehlC (frei Γ reserved) b.fehler ((16 * (ck.length + cr.length) : Nat) : Int) ++ ck ++ cr ++ ce) ρ reserved)
    (hWa : WeltAt m L σ) :
    (∃ v m2 w, axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inl v)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ct.length + 6 * b.fehler.length + ck.length)), fp⟩ m2 ∧
      AgreeW L fp (frei Γ reserved) K m m2 ∧ m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some w ∧ Enc L τ (ergWert he v) w ∧
      WeltAt m2 L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (∃ r m2, axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inr r)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ct.length + 6 * b.fehler.length + ck.length + cr.length)), fp⟩
        m2 ∧
      AgreeW L fp (frei Γ reserved) K m m2 ∧ m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 r.val) ∧
      WeltAt m2 L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, none) ∧ Stops ⟨pc, fp⟩ m 110) := by
  have hks := hW.ks
  have hlo2 := hW.lo
  have hτ' : τ = .int lo' hi' := by rw [he] at hτ; exact Option.some.inj hτ
  have e : ct ++ fehlC (frei Γ reserved) b.fehler ((16 * (ck.length + cr.length) : Nat) : Int) ++ ck ++ cr ++ ce =
      ct ++ (fehlC (frei Γ reserved) b.fehler ((16 * (ck.length + cr.length) : Nat) : Int) ++ (ck ++ (cr ++ ce))) := by
    simp only [List.append_assoc]
  have hp' := e ▸ hp
  have h7 := torC_top1 ht
  obtain ⟨b', hb', m1, w, s1, a1, hw1, hW1, hroh⟩ := torC_ok (O := O) ht htt hW hp'.left hWa
  rw [hb] at hb'
  cases hb'
  have hsmall := hp.small
  have hFs := frameOK_sub hp.frame hks
  have hroom := hFs.room
  have hn1 := hp'.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
  have hpF : PreS L m1 (pc + BitVec.ofNat 64 (16 * ct.length)) fp Ks (frei Γ reserved + 1)
      (fehlC (frei Γ reserved) b.fehler ((16 * (ck.length + cr.length) : Nat) : Int)) ρ reserved :=
    mkPreS (by omega) (by omega) (frameOK_sub hn1.frame hks) hn1.left.code (codeFar_sub2 hn1.left.far hks) hn1.env
  have hfc := fehlC_ok b.fehler ((16 * (ck.length + cr.length) : Nat) : Int) m1 _ hpF hf (by omega) (by push_cast; omega)
    (by omega) hw1
  have hdec := sonst_dec (L := L) (z := O.zeiger) he hτ' hlo hn hf w
  rw [axiomAntwortSonst_eq, hroh]
  revert hfc hdec
  cases b.fehler.find? (fun x => x.1 == w.toInt) with
  | some x =>
    intro ⟨m2, s2, a2, hw2⟩ ⟨hx, hs⟩
    refine .inr (.inl ⟨⟨x.2, hx⟩, m2, by rw [hs], s1.trans (star_cast s2 rfl ?_),
      a1.trans (agreeW_of (Agree.widen a2 hks)), hw2, weltAt_stab hW.lay hlo2 m1 m2 hW1 (a2.mono (Nat.zero_le _))⟩)
    rw [adr_int, show ((16 * ct.length : Nat) : Int) + (16 * (6 * (b.fehler.length : Int)) +
      ((16 * (ck.length + cr.length) : Nat) : Int)) =
      ((16 * (ct.length + 6 * b.fehler.length + ck.length + cr.length) : Nat) : Int) by push_cast; omega,
      BitVec.ofInt_natCast]
  | none =>
    intro ⟨m2, s2, a2⟩ ⟨din, dout⟩
    have hw2 : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some w := by
      rw [agree_rd_low a2 hroom (by omega) (by omega)]; exact hw1
    have hnF := hn1.next ((Agree.widen a2 hks).mono (Nat.le_succ _)) (a := fehlC (frei Γ reserved) b.fehler ((16 * (ck.length + cr.length) : Nat) : Int))
      (Nat.le_refl _) (by omega)
    have hpk : PreS L m2 _ fp Ks (frei Γ reserved + 1) ck ρ reserved :=
      mkPreS (by omega) (by omega) (frameOK_sub hnF.frame hks) hnF.left.code (codeFar_sub2 hnF.left.far hks) hnF.env
    obtain ⟨hin, hout⟩ := chkC_ok hck hpk htk hw2
    have s12 := s1.trans s2
    rw [pc_add] at s12
    rw [fehlC_len, pc_add] at hin hout
    by_cases hr : lo' ≤ w.toInt ∧ w.toInt ≤ hi'
    · obtain ⟨v, hv, hen⟩ := din hr
      obtain ⟨m3, s3, a3⟩ := hin hr
      refine .inl ⟨v, m3, w, by rw [hv], s12.trans (by rw [pc_add] at s3; exact s3), ?_, ?_, hen, ?_⟩
      · exact a1.trans (agreeW_of ((Agree.widen a2 hks).mono (Nat.le_succ _) |>.trans
          ((Agree.widen a3 hks).mono (Nat.le_succ _))))
      · rw [agree_rd_low a3 hroom (by omega) (by omega)]; exact hw2
      · exact weltAt_stab hW.lay hlo2 m1 m3 hW1 ((a2.trans a3).mono (Nat.zero_le _))
    · exact .inr (.inr ⟨by rw [dout hr], Stops.prefix s12 (hout hr)⟩)

end Gabbro.Stage0.Senke
