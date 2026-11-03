module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStart
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Every rule, classified by what it does to holdings and held locks -/

set_option hygiene false in
/-- A head-local step that keeps the held locks and the held holdings. -/
macro "rangA1" : tactic => `(tactic| (
  refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
  · first
      | (simp only [rufUpdateG_self]; done)
      | (simp only [rufUpdateG_self]; subst_vars; first | rfl | exact lese_offen _ _ _)
  · intro K hK
    dsimp only; rw [rufUpdateG_self]
    rw [‹(M.faeden f).kopf.rest = _›] at hK
    exact hK))

set_option hygiene false in
/-- A head-local step that keeps the held locks; the held holdings pass a
    block or statement. -/
macro "rangA1h" t:term : tactic => `(tactic| (
  refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
  · first
      | (simp only [rufUpdateG_self]; done)
      | (simp only [rufUpdateG_self]; subst_vars; first | rfl | exact lese_offen _ _ _)
  · intro K hK
    dsimp only; rw [rufUpdateG_self]
    rw [‹(M.faeden f).kopf.rest = _›] at hK
    exact $t K hK))

set_option hygiene false in
/-- A push. -/
macro "rangB" g:term "," c:term : tactic => `(tactic| (
  refine Or.inr (Or.inl ⟨$g, $c, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩)
  · dsimp only; rw [rufUpdateG_self]
  · dsimp only; rw [rufUpdateG_self]
  · dsimp only; rw [rufUpdateG_self]
  · intro K hK
    rw [‹(M.faeden f).kopf.rest = _›] at hK
    exact (held_nachSig_iff _ _ K).mpr hK
  · simp only [rufUpdateG_self]
    rw [hs0]
    exact lese_offen _ _ _
  · rw [‹(M.faeden f).kopf.rest = _›]
    first
      | exact ‹RufPasst _ _ _ _›
      | (subst_vars; exact ‹RufPasst _ _ _ _›)))

set_option maxHeartbeats 4000000 in
/-- **Every rule of G, classified by what it does to the head's holdings
    and the thread's held locks**: (A) a head-local step keeps the stack and
    the function, and either keeps the held locks while the held holdings
    grow, or takes a lock `L` (not held, free, admitted by the residue's
    features, now named), or releases a lock `L` (the other held holdings
    stay); (B) a push, with the call site's typing `RufPasst`; (C) a pop of
    a frame whose holdings are its end holdings. -/
theorem schrittRang (hO : GutO O) {P : Programm D} {pa : Nat} {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O pa M f M') (A : Merkmal D)
    (hR : (M.faeden f).kopf.rest.2.2.2.2.mR A) :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧ (M'.faeden f).kopf.f = (M.faeden f).kopf.f ∧
      ((offen (M'.faeden f).spur = offen (M.faeden f).spur ∧
          ∀ K, Res.held K ∈ (M.faeden f).kopf.rest.2.2.1 → Res.held K ∈ (M'.faeden f).kopf.rest.2.2.1) ∨
        (∃ L, L ∉ offen (M.faeden f).spur ∧ RufFreiG M f L ∧ A.sperre L = true ∧
          offen (M'.faeden f).spur = L :: offen (M.faeden f).spur ∧
          (M'.faeden f).kopf.rest.2.2.1 = Res.held L :: (M.faeden f).kopf.rest.2.2.1) ∨
        (∃ L, offen (M'.faeden f).spur = (offen (M.faeden f).spur).erase L ∧
          ∀ K, K ≠ L → Res.held K ∈ (M.faeden f).kopf.rest.2.2.1 →
            Res.held K ∈ (M'.faeden f).kopf.rest.2.2.1))) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧ caller'.f = (M.faeden f).kopf.f ∧
      (M'.faeden f).kopf.f = g ∧ (M'.faeden f).kopf.rest.2.2.1 = Signatur.anfang D (D.signatur g) ∧
      (∀ K, Res.held K ∈ (M.faeden f).kopf.rest.2.2.1 → Res.held K ∈ caller'.rest.2.2.1) ∧
      offen (M'.faeden f).spur = offen (M.faeden f).spur ∧
      RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) (M.faeden f).kopf.rest.2.2.1) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      (M'.faeden f).kopf.f = caller.f ∧ (M'.faeden f).kopf.rest.2.2.1 = caller.rest.2.2.1 ∧
      offen (M'.faeden f).spur = offen (M.faeden f).spur ∧
      (M.faeden f).kopf.rest.2.2.1.Perm (vertragVon D (M.faeden f).kopf.f).ende) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        exact blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Stmt.held_iff s K).mpr hK
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        exact blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Stmt.held_iff s K).mpr hK
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact hK
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], ?_, ?_⟩)
      · simp only [rufUpdateG_self]; rw [hs1]; exact lese_offen _ _ _
      · rw [hhead]; exact hperm
    | _ => rangA1
  | g2 hs =>
    cases hs with
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self],
        Or.inr (Or.inl ⟨L, hself, hfrei, ?_, by simp only [rufUpdateG_self]; rfl, ?_⟩)⟩
      · rw [hhead] at hR
        simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hR
        exact hR.1.1.1
      · dsimp only; rw [rufUpdateG_self]
        rw [hhead]
    | freiGib l Γ Λ L k ρ hhead =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self],
        Or.inr (Or.inr ⟨L, by simp only [rufUpdateG_self]; rfl, fun K hKL hK => ?_⟩)⟩
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hK
      rcases List.mem_cons.mp hK with h | h
      · cases h; exact absurd rfl hKL
      · exact h
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩
    | _ => rangA1
  | g3 hs =>
    cases hs with
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
        neu₁ hneu₁ hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [hs₁, lese_offen, leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Block.held_iff rest K).mpr hK
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Block.held_iff rest K).mpr hK
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Block.held_iff rest K).mpr hK
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Block.held_iff rest K).mpr hK
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Block.held_iff rest K).mpr hK
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
        hneu =>
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err .nil (.dann rest k)⟩⟩
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
        s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], ?_, ?_, ?_⟩)
      · dsimp only; rw [rufUpdateG_self]; dsimp only
        rcases hcaller with hc | ⟨_, _, hc⟩ <;> rw [hc]
      · simp only [rufUpdateG_self]; rw [hs1]; exact lese_offen _ _ _
      · rw [hhead]; exact hperm
  | g4 hs =>
    cases hs with
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self],
        Or.inr (Or.inr ⟨L, by simp only [rufUpdateG_self]; rfl, fun K hKL hK => ?_⟩)⟩
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hK
      rcases List.mem_cons.mp ((Block.held_iff rest K).mpr hK) with h | h
      · cases h; exact absurd rfl hKL
      · exact h
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self],
        Or.inr (Or.inr ⟨L, by simp only [rufUpdateG_self]; rfl, fun K hKL hK => ?_⟩)⟩
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hK
      rcases List.mem_cons.mp ((Block.held_iff rest K).mpr hK) with h | h
      · cases h; exact absurd rfl hKL
      · exact h
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      rangA1h (fun K hK => (Block.held_iff b K).mpr ((Block.held_iff rest K).mpr hK))
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      rangA1h (fun K hK => (Block.held_iff b K).mpr ((Block.held_iff rest K).mpr hK))
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      rangA1h (fun K hK => (Block.held_iff rest K).mpr hK)
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      rangA1h (fun K hK => (Block.held_iff rest K).mpr hK)
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      have hR' := hR
      rw [hhead] at hR'
      simp only [GRest.mR] at hR'
      rangA1h (fun K hK => (hR'.2.1 K).mpr ((Block.held_iff rest K).mpr hK))
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      have hR' := hR
      rw [hhead] at hR'
      simp only [GRest.mR] at hR'
      rangA1h (fun K hK => (hR'.2.1 K).mpr ((Block.held_iff rest K).mpr hK))
    | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact (Block.held_iff rest K).mpr hK
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
        hneu hnw =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], ?_, ?_⟩)
      · simp only [rufUpdateG_self]; rw [hs1]; exact lese_offen _ _ _
      · rw [hhead]; exact hperm
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
        neu hneu hnw =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], ?_, ?_⟩)
      · simp only [rufUpdateG_self]; rw [hs1]; exact lese_offen _ _ _
      · rw [hhead]; exact hperm
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], ?_, ?_, ?_⟩)
      · dsimp only; rw [rufUpdateG_self]; dsimp only
        rcases hcaller with hc | ⟨_, _, hc⟩ <;> rw [hc]
      · simp only [rufUpdateG_self]; rw [hs1]; exact lese_offen _ _ _
      · rw [hhead]; exact hperm
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller
        hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], ?_, ?_, ?_⟩)
      · dsimp only; rw [rufUpdateG_self]; dsimp only
        rcases hcaller with hc | ⟨_, _, hc⟩ <;> rw [hc]
      · simp only [rufUpdateG_self]; rw [hs1]; exact lese_offen _ _ _
      · rw [hhead]; exact hperm
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], ?_, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      · dsimp only; rw [rufUpdateG_self]; dsimp only; rw [hcaller]
      · rw [hhead]; exact hperm
  | g5 hs =>
    cases hs with
    | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [hs₂, hs₁]
        exact lese_offen _ _ _
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact hK
    | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact hK
    | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact hK
    | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact hK
    | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], ?_, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      · dsimp only; rw [rufUpdateG_self]; dsimp only; rw [hcaller]
      · rw [hhead]; exact hperm
    | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], ?_, by dsimp only; rw [rufUpdateG_self], ?_⟩)
      · dsimp only; rw [rufUpdateG_self]; dsimp only; rw [hcaller]
      · rw [hhead]; exact hperm
    | _ => rangA1
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact hK
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
      · simp only [rufUpdateG_self]
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
      · intro K hK
        dsimp only; rw [rufUpdateG_self]
        rw [hhead] at hK
        exact hK
  | g7 hs =>
    cases hs with
    | _ => rangA1

#print axioms Gabbro.Grammatik.schrittRang


end Gabbro.Grammatik
