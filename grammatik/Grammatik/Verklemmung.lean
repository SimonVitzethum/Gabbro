/-
  File:      Grammatik/Verklemmung.lean
  Subject:   DEADLOCK FREEDOM FROM LOCK RANKS on machine G (SATZKARTE §13.5
             progress item 1, §16.3).

  The checker enforces the rank order (`H006`: a `locks L` ranks above every
  lock its holdings name, in the syntax `Stmt.locks … hr`) and forbids
  re-taking (`H003`); across calls the lock floors (`Signatur.boden`,
  `RufPasst.hx`/`hb`, `StufenOk`) carry the order to locks a caller holds
  and the callee does not name. G's `dannLocks` fires only if the lock is
  not held by the thread (`hself`), ranks above EVERY lock the thread holds
  (`hrang`, a check on the machine's held set, not on the syntax), and no
  other thread holds it (`RufFreiG`). Nothing proved that the first two
  side conditions ever hold; a thread at a `locks` head could be stuck for
  a reason no scheduler resolves.

  **The thread invariant** `RangInvG` (on every reachable machine,
  `rangInvG_erreichbar`): the held locks are duplicate-free, and down the
  stack every held lock is NAMED by a frame, or ranks below that frame's
  floor, or ranks at least the floor of the frame directly above (it was
  taken by a callee); every frame's signature locks are named by the frame
  below it, floors rise towards the head, and every `locks` still ahead of
  a frame ranks at least that frame's floor (`bodenM`, the residue form of
  `StufenOk`). The stack's bottom frame is the start function's.

  **The consequences.**
  * `sperre_rang`: at a `locks L` head every lock the thread holds ranks
    below `L` -- `hself` and `hrang` hold; `schritt_an_sperre`: the step
    fires unless another thread holds `L`.
  * `keine_verklemmungG`: on no reachable machine is every unfinished thread
    waiting for a lock another thread holds (given that start functions hold
    no lock by signature, and a complete list of locks): the waited-for lock
    of a waiting thread ranks strictly below the lock its holder waits for,
    and ranks are bounded on finitely many locks.
-/
import Grammatik.ZielOrtStart
import Grammatik.ZielOrtEinfaden

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
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
    · simp only [rufUpdateG_self]
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
    · intro K hK
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hK
      exact (Block.held_iff rest K).mpr hK
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
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hg
    rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr (D.sig g)) Λ, ρ, .dann rest k⟩⟩
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hg
    rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr (D.sig g)) Λ, ρ, .ende rest⟩⟩
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
    subst hg
    rangB g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0, ⟨l, Γ, nachSig D (D.sigNr (D.sig g)) Λ, ρ, .wartet rest k⟩⟩
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], ?_, ?_⟩)
    · simp only [rufUpdateG_self]; rw [hs1]; exact lese_offen _ _ _
    · rw [hhead]; exact hperm
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
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], ?_, ?_, ?_⟩)
    · dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨_, _, hc⟩ <;> rw [hc]
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

#print axioms Gabbro.Grammatik.schrittRang

/-! ## 2. The rank invariant -/

/-- The floor of a function. -/
def bodenF (f : D.Fn) : Option Int := (D.signatur f).boden

/-- `K` ranks below the floor `b`. -/
def UnterB (b : Option Int) (K : D.Lock) : Prop := ∃ c, b = some c ∧ D.rang K < c

/-- `K` ranks at least the floor `b` (vacuous without a floor). -/
def UeberB (b : Option Int) (K : D.Lock) : Prop := ∀ c, b = some c → c ≤ D.rang K

/-- The floor `b` is at most `b'` (a floor below forces a floor above). -/
def BodenLe (b b' : Option Int) : Prop := ∀ c, b = some c → ∃ c', b' = some c' ∧ c ≤ c'

theorem bodenLe_trans {a b c : Option Int} (h1 : BodenLe a b) (h2 : BodenLe b c) :
    BodenLe a c := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h1 x hx
  obtain ⟨z, hz, hyz⟩ := h2 y hy
  exact ⟨z, hz, Int.le_trans hxy hyz⟩

theorem ueberB_of_le {b b' : Option Int} {K : D.Lock} (h : UeberB b' K) (hle : BodenLe b b') :
    UeberB b K := by
  intro c hc
  obtain ⟨c', hc', hle'⟩ := hle c hc
  exact Int.le_trans hle' (h c' hc')

theorem unter_ueber {b : Option Int} {K : D.Lock} (h1 : UnterB b K) (h2 : UeberB b K) : False := by
  obtain ⟨c, hc, hlt⟩ := h1
  have := h2 c hc
  omega

/-- **The rank chain of a stack** (head first). Every held lock `K ∈ o` is,
    at each frame: named by it, or below its floor (an extra lock of its
    callers), or at least the floor of the frame directly above it (`oben`:
    taken by a callee; nothing above the head); at the bottom frame the
    middle case is absent (a start frame has no caller). Every frame's
    signature locks are named by the frame below it, and floors rise
    towards the head. -/
def RangKette (o : List D.Lock) : (D.Lock → Prop) → RufRahmenG D → List (RufRahmenG D) → Prop
  | oben, F, [] => ∀ K ∈ o, Res.held K ∈ F.rest.2.2.1 ∨ oben K
  | oben, F, c :: rest =>
      (∀ K ∈ o, Res.held K ∈ F.rest.2.2.1 ∨ UnterB (bodenF F.f) K ∨ oben K) ∧
      (∀ L ∈ D.haelt F.f, Res.held L ∈ c.rest.2.2.1) ∧ BodenLe (bodenF c.f) (bodenF F.f) ∧
      RangKette o (UeberB (bodenF F.f)) c rest

theorem rangKette_boden {o : List D.Lock} :
    ∀ {oben : D.Lock → Prop} {F : RufRahmenG D} {S : List (RufRahmenG D)},
      RangKette o oben F S → ∀ G ∈ S, BodenLe (bodenF G.f) (bodenF F.f)
  | _, _, [], _, G, hG => absurd hG List.not_mem_nil
  | _, _, c :: rest, h, G, hG => by
      obtain ⟨_, _, h3, h4⟩ := h
      rcases List.mem_cons.mp hG with rfl | hG
      · exact h3
      · exact bodenLe_trans (rangKette_boden h4 G hG) h3

/-- The head's clause, whatever the stack below. -/
theorem rangKette_kopfK {o : List D.Lock} {F : RufRahmenG D} {S : List (RufRahmenG D)}
    (h : RangKette o (fun _ => False) F S) :
    ∀ K ∈ o, Res.held K ∈ F.rest.2.2.1 ∨ UnterB (bodenF F.f) K := by
  cases S with
  | nil => exact fun K hK => (h K hK).imp id False.elim
  | cons c rest =>
      intro K hK
      rcases h.1 K hK with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact h1.elim

theorem rangKette_tail {o o' : List D.Lock} :
    ∀ {oben : D.Lock → Prop} {F : RufRahmenG D} {S : List (RufRahmenG D)},
      RangKette o oben F S →
      (∀ K ∈ o', K ∈ o ∨ (oben K ∧ ∀ G ∈ F :: S, UeberB (bodenF G.f) K)) →
      RangKette o' oben F S
  | _, _, [], h, hK => fun K hk => by
      rcases hK K hk with h1 | ⟨h1, _⟩
      · exact h K h1
      · exact Or.inr h1
  | _, F, c :: rest, h, hK => by
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨fun K hk => ?_, h2, h3, rangKette_tail h4 fun K hk => ?_⟩
      · rcases hK K hk with h5 | ⟨h5, _⟩
        · exact h1 K h5
        · exact Or.inr (Or.inr h5)
      · rcases hK K hk with h5 | ⟨_, h5⟩
        · exact Or.inl h5
        · exact Or.inr ⟨h5 F List.mem_cons_self, fun G hG => h5 G (List.mem_cons_of_mem _ hG)⟩

/-- **A head-local step**: a new head of the same function, held locks `o'`
    each named by the new head or old and carried, or ranking at least
    every floor of the stack. -/
theorem rangKette_kopf {o o' : List D.Lock} {F F' : RufRahmenG D} (hf : F'.f = F.f) :
    ∀ {S : List (RufRahmenG D)}, RangKette o (fun _ => False) F S →
    (∀ K ∈ o', Res.held K ∈ F'.rest.2.2.1 ∨
      (K ∈ o ∧ (Res.held K ∈ F.rest.2.2.1 → Res.held K ∈ F'.rest.2.2.1))) →
    (∀ K ∈ o', K ∈ o ∨ ∀ G ∈ F :: S, UeberB (bodenF G.f) K) →
    RangKette o' (fun _ => False) F' S
  | [], h, hK, _ => fun K hk => by
      rcases hK K hk with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · rcases h K h1 with h3 | h3
        · exact Or.inl (h2 h3)
        · exact h3.elim
  | c :: rest, h, hK, hU => by
      obtain ⟨h1, h2, h3, h4⟩ := h
      have eb : bodenF F'.f = bodenF F.f := congrArg bodenF hf
      have eh : D.haelt F'.f = D.haelt F.f := congrArg D.haelt hf
      refine ⟨fun K hk => ?_, ?_, ?_, ?_⟩
      · rcases hK K hk with h5 | ⟨h5, h6⟩
        · exact Or.inl h5
        · rcases h1 K h5 with h7 | h7 | h7
          · exact Or.inl (h6 h7)
          · exact Or.inr (Or.inl (by rw [eb]; exact h7))
          · exact h7.elim
      · rw [eh]; exact h2
      · rw [eb]; exact h3
      · rw [eb]
        exact rangKette_tail h4 fun K hk => by
          rcases hU K hk with h5 | h5
          · exact Or.inl h5
          · exact Or.inr ⟨h5 F List.mem_cons_self, fun G hG => h5 G (List.mem_cons_of_mem _ hG)⟩

/-- **A push**: the callee's typing at the call site (`RufPasst`: its
    signature locks are named by the caller, every extra lock ranks below
    its floor, floors rise) gives the chain one frame higher. -/
theorem rangKette_push {o : List D.Lock} {F C G : RufRahmenG D} {S : List (RufRahmenG D)}
    {g : D.Fn} (h : RangKette o (fun _ => False) F S) (hCf : C.f = F.f) (hGf : G.f = g)
    (hGΛ : G.rest.2.2.1 = Signatur.anfang D (D.signatur g))
    (hCΛ : ∀ K, Res.held K ∈ F.rest.2.2.1 → Res.held K ∈ C.rest.2.2.1)
    (hp : RufPasst D (vertragVon D F.f) (D.signatur g) F.rest.2.2.1) :
    RangKette o (fun _ => False) G (C :: S) := by
  have hk0 := rangKette_kopfK h
  have ebG : bodenF G.f = (D.signatur g).boden := by rw [hGf]; rfl
  have ehG : D.haelt G.f = (D.signatur g).haelt := by rw [hGf]; rfl
  have ebC : bodenF C.f = bodenF F.f := congrArg bodenF hCf
  have ehC : D.haelt C.f = D.haelt F.f := congrArg D.haelt hCf
  have hb : BodenLe (bodenF F.f) (bodenF G.f) := by
    rw [ebG]; exact fun c hc => hp.hb c hc
  refine ⟨fun K hK => ?_, ?_, by rw [ebC]; exact hb, ?_⟩
  · rcases hk0 K hK with h1 | h1
    · by_cases hKg : K ∈ (D.signatur g).haelt
      · exact Or.inl (by rw [hGΛ]; exact (held_anfang _ K).mpr hKg)
      · obtain ⟨c, hc, hlt⟩ := hp.hx K h1 hKg
        exact Or.inr (Or.inl ⟨c, by rw [ebG]; exact hc, hlt⟩)
    · obtain ⟨c, hc, hlt⟩ := h1
      obtain ⟨c', hc', hle⟩ := hb c hc
      exact Or.inr (Or.inl ⟨c', hc', by omega⟩)
  · rw [ehG]
    exact fun L hL => hCΛ L (hp.hh L hL)
  · cases S with
    | nil =>
        intro K hK
        rcases h K hK with h1 | h1
        · exact Or.inl (hCΛ K h1)
        · exact h1.elim
    | cons c rest =>
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨fun K hK => ?_, by rw [ehC]; exact h2, by rw [ebC]; exact h3, by rw [ebC]; exact h4⟩
        rcases h1 K hK with h5 | h5 | h5
        · exact Or.inl (hCΛ K h5)
        · exact Or.inr (Or.inl (by rw [ebC]; exact h5))
        · exact h5.elim

/-- **A pop**: a frame at its end holdings names only its signature locks,
    which its caller names; a lock below its floor was held before the call
    (it is not at least the floor), so the caller names it or it is below
    the caller's floor. -/
theorem rangKette_pop {o : List D.Lock} {H caller N : RufRahmenG D} {rst : List (RufRahmenG D)}
    (h : RangKette o (fun _ => False) H (caller :: rst))
    (hperm : H.rest.2.2.1.Perm (vertragVon D H.f).ende)
    (hNf : N.f = caller.f) (hNΛ : N.rest.2.2.1 = caller.rest.2.2.1) :
    RangKette o (fun _ => False) N rst := by
  obtain ⟨h1, h2, _, h4⟩ := h
  have ebN : bodenF N.f = bodenF caller.f := congrArg bodenF hNf
  have ehN : D.haelt N.f = D.haelt caller.f := congrArg D.haelt hNf
  have hnamed : ∀ K, Res.held K ∈ H.rest.2.2.1 → Res.held K ∈ caller.rest.2.2.1 := fun K hK =>
    h2 K ((held_ende _ K).mp (hperm.mem_iff.mp hK))
  cases rst with
  | nil =>
      intro K hK
      rw [hNΛ]
      rcases h1 K hK with h5 | h5 | h5
      · exact Or.inl (hnamed K h5)
      · rcases h4 K hK with h6 | h6
        · exact Or.inl h6
        · exact (unter_ueber h5 h6).elim
      · exact h5.elim
  | cons c rest =>
      obtain ⟨g1, g2, g3, g4⟩ := h4
      refine ⟨fun K hK => ?_, by rw [ehN]; exact g2, by rw [ebN]; exact g3, by rw [ebN]; exact g4⟩
      rw [hNΛ, ebN]
      rcases h1 K hK with h5 | h5 | h5
      · exact Or.inl (hnamed K h5)
      · rcases g1 K hK with h6 | h6 | h6
        · exact Or.inl h6
        · exact Or.inr (Or.inl h6)
        · exact (unter_ueber h5 h6).elim
      · exact h5.elim

/-- The feature set of the floors: every `locks L` still ahead of a frame of
    `f` ranks at least `f`'s floor. -/
def bodenM (f : D.Fn) : Merkmal D :=
  ⟨fun _ => true, fun _ => true, fun L => match bodenF f with
    | none => true
    | some c => decide (c ≤ D.rang L)⟩

theorem bodenM_ueber {f : D.Fn} {L : D.Lock} (h : (bodenM f).sperre L = true) :
    UeberB (bodenF f) L := by
  intro c hc
  simp only [bodenM, hc, decide_eq_true_eq] at h
  exact h

/-- The floors of a program, read on its bodies (the residue form of
    `StufenOk`), decided per function. -/
def StufenM (P : Programm D) : Prop := ∀ f, mE (bodenM f) (P.rumpf f) = true

/-- The bottom frame's function. -/
def unten (z : RufFadenG D) : D.Fn := (z.stapel.getLast?.getD z.kopf).f

/-- **The rank invariant of a thread** whose start function is `w`. -/
def RangInvG (w : D.Fn) (z : RufFadenG D) : Prop :=
  (offen z.spur).Nodup ∧ RangKette (offen z.spur) (fun _ => False) z.kopf z.stapel ∧
  MerkInvG (fun _ => True) bodenM z ∧ unten z = w

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem rangInvG_schritt (hO : GutO O) (hSt : StufenM P) {w : D.Fn} {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O passes M u M') (h : RangInvG w (M.faeden u)) :
    RangInvG w (M'.faeden u) := by
  obtain ⟨hnd, hk, hm, hu⟩ := h
  have hm' := merkInvG_schritt (fun f _ => ⟨hSt f, fun _ _ => trivial⟩) hs hm
  have hR := (hm _ List.mem_cons_self).2
  rcases schrittRang hO hs _ hR with
    ⟨hst, hf, ⟨ho, hΛ⟩ | ⟨L, hL, _, hsp, ho, hΛ⟩ | ⟨L, ho, hΛ⟩⟩ |
    ⟨g, c', hst, hcf, hgf, hgΛ, hcΛ, ho, hp⟩ | ⟨caller, rst, hpop, hst, hf, hΛ, ho, hperm⟩
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      exact rangKette_kopf hf hk (fun K hK => Or.inr ⟨hK, hΛ K⟩) (fun K hK => Or.inl hK)
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact List.nodup_cons.mpr ⟨hL, hnd⟩, ?_, hm', ?_⟩
    · rw [hst, ho]
      refine rangKette_kopf hf hk (fun K hK => ?_) (fun K hK => ?_)
      · rcases List.mem_cons.mp hK with rfl | hK
        · exact Or.inl (by rw [hΛ]; exact List.mem_cons_self)
        · exact Or.inr ⟨hK, fun h => by rw [hΛ]; exact List.mem_cons_of_mem _ h⟩
      · rcases List.mem_cons.mp hK with rfl | hK
        · refine Or.inr fun G hG => ?_
          rcases List.mem_cons.mp hG with rfl | hG
          · exact bodenM_ueber hsp
          · exact ueberB_of_le (bodenM_ueber hsp) (rangKette_boden hk G hG)
        · exact Or.inl hK
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd.erase L, ?_, hm', ?_⟩
    · rw [hst, ho]
      refine rangKette_kopf hf hk (fun K hK => ?_) (fun K hK => Or.inl (List.mem_of_mem_erase hK))
      obtain ⟨hne, hK'⟩ := (List.Nodup.mem_erase_iff hnd).mp hK
      exact Or.inr ⟨hK', hΛ K hne⟩
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      exact rangKette_push hk hcf hgf hgΛ hcΛ hp
    · rw [← hu]; unfold unten; rw [hst, List.getLast?_cons]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hcf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      rw [hpop] at hk
      exact rangKette_pop hk hperm hf hΛ
    · rw [← hu]; unfold unten; rw [hst, hpop, List.getLast?_cons]
      cases rst.getLast? with
      | none => exact hf
      | some F => rfl

/-- **The rank invariant on every reachable machine**, given the floors on
    the bodies and duplicate-free start locks. -/
theorem rangInvG_erreichbar (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ t, RangInvG (init t).1 (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      rw [start_faden]
      refine ⟨hND t, fun K hK => Or.inl ((held_anfang _ K).mpr ((offen_startSpur _ K).mp hK)), ?_, rfl⟩
      intro F hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact ⟨trivial, hSt _⟩
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact rangInvG_schritt hO hSt hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Inv

/-! ## 3. At a `locks` head only another thread can stop the step -/

/-- Thread `t` stands at `locks L { … }`. -/
def AnSperre (M : RufMaschineG D) (t : Faden) (L : D.Lock) : Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (ρ : Env D Γ)
    (hr : ∀ K, Res.held K ∈ Λ → D.rang K < D.rang L)
    (body : Block D (vertragVon D (M.faeden t).kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩

section Folgen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **At a `locks L` head every lock the thread holds ranks below `L`**, and
    `L` is not held by the thread: `hself` and `hrang` of `dannLocks` hold
    on every reachable machine. -/
theorem sperre_rang {w : D.Fn} {M : RufMaschineG D} {t : Faden} (h : RangInvG w (M.faeden t))
    {L : D.Lock} (hA : AnSperre M t L) :
    L ∉ offen (M.faeden t).spur ∧ ∀ K ∈ offen (M.faeden t).spur, D.rang K < D.rang L := by
  obtain ⟨l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩ := hA
  have hk := rangKette_kopfK h.2.1
  have hR := (h.2.2.1 _ List.mem_cons_self).2
  rw [hhead] at hR
  simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hR
  have hU := bodenM_ueber hR.1.1.1
  have hlt : ∀ K ∈ offen (M.faeden t).spur, D.rang K < D.rang L := by
    intro K hK
    rcases hk K hK with h1 | ⟨c, hc, hlt⟩
    · rw [hhead] at h1
      exact hr K h1
    · have := hU c hc
      omega
  exact ⟨fun hL => by have := hlt L hL; omega, hlt⟩

/-- **The `locks` step fires as soon as no other thread holds the lock**:
    on every reachable machine, at a `locks L` head, `RufFreiG` is the only
    side condition that can fail. -/
theorem schritt_an_sperre {w : D.Fn} {M : RufMaschineG D} {t : Faden}
    (h : RangInvG w (M.faeden t)) {L : D.Lock} (hA : AnSperre M t L) (hfrei : RufFreiG M t L) :
    ∃ M', RufSchrittG P O passes M t M' := by
  obtain ⟨hself, hrang⟩ := sperre_rang h hA
  obtain ⟨l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩ := hA
  exact ⟨_, .dannLocks M t l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei⟩

end Folgen

/-! ## 4. No wait cycle -/

/-- A statement returns (a value or a reason). -/
def Stmt.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ret .. => true
  | .retGrund .. => true
  | _ => false

def Endblock.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .cons s _ => s.istRueck
  | _ => false

def Block.istRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .cons s _ => s.istRueck
  | _ => false

/-- The residue stands at a return (the shapes a pop fires on). -/
def GRest.anRueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende e => e.istRueck
  | .dann b _ => b.istRueck
  | _ => false

theorem Stmt.istRueck_perm {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : s.istRueck = true) : Λ.Perm V.ende := by
  cases s <;> simp_all [Stmt.istRueck]

theorem GRest.anRueck_perm {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) (h : r.anRueck = true) : Λ.Perm V.ende := by
  cases r with
  | ende e =>
      cases e with
      | ret _ hp => exact hp
      | retGrund _ hp => exact hp
      | cons s _ => exact s.istRueck_perm h
      | _ => simp [GRest.anRueck, Endblock.istRueck] at h
  | dann b _ =>
      cases b with
      | cons s _ => exact s.istRueck_perm h
      | _ => simp [GRest.anRueck, Block.istRueck] at h
  | _ => simp [GRest.anRueck] at h

/-- **Thread `t` is finished**: its stack is empty and its head stands at a
    return. -/
def FertigG (M : RufMaschineG D) (t : Faden) : Prop :=
  (M.faeden t).stapel = [] ∧ (M.faeden t).kopf.rest.2.2.2.2.anRueck = true

/-- **Thread `t` waits for a lock**: it stands at a `locks L` head, and
    every lock it stands at is held by another thread. -/
def WartetG (M : RufMaschineG D) (t : Faden) : Prop :=
  (∃ L, AnSperre M t L) ∧ ∀ L, AnSperre M t L → ∃ u, u ≠ t ∧ L ∈ offen (M.faeden u).spur

/-- A finished thread whose start function holds no lock holds none. -/
theorem fertig_leer {M : RufMaschineG D} {t : Faden} {w : D.Fn} (h : RangInvG w (M.faeden t))
    (hw : D.haelt w = []) (hF : FertigG M t) : offen (M.faeden t).spur = [] := by
  obtain ⟨_, hk, _, hu⟩ := h
  obtain ⟨hst, hret⟩ := hF
  have hperm := GRest.anRueck_perm _ hret
  rw [hst] at hk
  have hkf : (M.faeden t).kopf.f = w := by
    rw [← hu]; unfold unten; rw [hst]; rfl
  refine List.eq_nil_iff_forall_not_mem.mpr fun K hK => ?_
  rcases hk K hK with h1 | h1
  · have := (held_ende _ K).mp (hperm.mem_iff.mp h1)
    have e : D.haelt (M.faeden t).kopf.f = [] := by rw [hkf]; exact hw
    change K ∈ D.haelt (M.faeden t).kopf.f at this
    rw [e] at this
    exact List.not_mem_nil this
  · exact h1

/-- A nonempty list of locks has one of maximal rank. -/
theorem rang_max : ∀ (ls : List D.Lock), ls ≠ [] → ∃ L ∈ ls, ∀ K ∈ ls, D.rang K ≤ D.rang L
  | [], h => absurd rfl h
  | [L], _ => ⟨L, List.mem_singleton_self L, fun K hK => by
      rw [List.mem_singleton.mp hK]; exact Int.le_refl _⟩
  | L :: L' :: rest, _ => by
      obtain ⟨M, hM, hmax⟩ := rang_max (L' :: rest) (List.cons_ne_nil _ _)
      by_cases hLM : D.rang M ≤ D.rang L
      · refine ⟨L, List.mem_cons_self, fun K hK => ?_⟩
        rcases List.mem_cons.mp hK with rfl | hK
        · exact Int.le_refl _
        · exact Int.le_trans (hmax K hK) hLM
      · refine ⟨M, List.mem_cons_of_mem _ hM, fun K hK => ?_⟩
        rcases List.mem_cons.mp hK with rfl | hK
        · omega
        · exact hmax K hK

section Verklemmung

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **NO DEADLOCK FROM LOCK RANKS.** On every reachable machine, if every
    unfinished thread waits for a lock another thread holds, then every
    thread is finished -- i.e. no reachable machine has an unfinished thread
    while all unfinished threads wait for locks. Premises: the declared
    floors hold on the bodies (`StufenM`), start functions hold no lock by
    signature (a finished thread then holds none), and the locks are
    finitely many (`ls`). The waited-for lock of a waiting thread ranks
    strictly below the lock its holder waits for (`sperre_rang`), so the
    waiting thread whose lock ranks highest waits for a lock held by a
    thread that waits for none higher -- a contradiction. -/
theorem keine_verklemmungG (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hLeer : ∀ t, D.haelt (init t).1 = []) (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hW : ∀ t, ¬ FertigG M t → WartetG M t) : ∀ t, FertigG M t := by
  have hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup := fun t => by
    rw [startSpur, hLeer t]; exact List.nodup_nil
  have hI := rangInvG_erreichbar hO hSt sp init hND hr
  intro t0
  refine Classical.byContradiction fun h0 => ?_
  let W := ls.filter fun L => @decide (∃ t, ¬ FertigG M t ∧ AnSperre M t L)
    (Classical.propDecidable _)
  have hWmem : ∀ L, L ∈ W ↔ ∃ t, ¬ FertigG M t ∧ AnSperre M t L := by
    intro L
    simp only [W, List.mem_filter, hls L, true_and]
    exact ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
      fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩
  obtain ⟨L0, hL0⟩ := (hW t0 h0).1
  have hne : W ≠ [] := fun he => by
    have := (hWmem L0).mpr ⟨t0, h0, hL0⟩
    rw [he] at this
    exact List.not_mem_nil this
  obtain ⟨Lm, hLm, hmax⟩ := rang_max W hne
  obtain ⟨tm, htm, hAm⟩ := (hWmem Lm).mp hLm
  obtain ⟨u, hu, hLu⟩ := (hW tm htm).2 Lm hAm
  by_cases hFu : FertigG M u
  · rw [fertig_leer (hI u) (hLeer u) hFu] at hLu
    exact List.not_mem_nil hLu
  · obtain ⟨Lu, hAu⟩ := (hW u hFu).1
    have hlt := (sperre_rang (hI u) hAu).2 Lm hLu
    have hle := hmax Lu ((hWmem Lu).mpr ⟨u, hFu, hAu⟩)
    omega

/-- The same, as "no reachable machine has all its unfinished threads
    waiting while one is unfinished". -/
theorem keine_verklemmungG' (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hLeer : ∀ t, D.haelt (init t).1 = []) (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ¬ ((∃ t, ¬ FertigG M t) ∧ ∀ t, ¬ FertigG M t → WartetG M t) :=
  fun ⟨⟨t, ht⟩, hW⟩ => ht (keine_verklemmungG hO hSt sp init hLeer ls hls hr hW t)

end Verklemmung


/-! ## 5. `StufenOk` gives the floors on the residues -/

section Stufen

variable (A : Merkmal D) (hr : ∀ g, A.ruf g = true) (hi : ∀ n, A.ind n = true)
  (b : Option Int) (hs : ∀ L, UeberB b L → A.sperre L = true)

include hr hi hs in
mutual

theorem mS_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → Stmt.BodenOk b s → mS A s = true
  | .ite _ t e, h => by
      simp only [mS, Bool.and_eq_true]
      exact ⟨mB_boden t fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden],
        mB_boden e fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]⟩
  | .onOption _ p a, h => by
      simp only [mS, Bool.and_eq_true]
      exact ⟨mB_boden p fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden],
        mB_boden a fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]⟩
  | .onTag _ arms, h => by
      simp only [mS]
      exact mArms_boden arms fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .onGrund _ arms, h => by
      simp only [mS]
      exact mGArms_boden arms fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .call g _ _ _, _ => by simp only [mS]; exact hr g
  | .callInd (n := n) _ _ _ _, _ => by simp only [mS]; exact hi n
  | .locks L _ body, h => by
      simp only [mS, Bool.and_eq_true]
      refine ⟨hs L fun c hc => ?_, mB_boden body fun c hc => ?_⟩
      · have := h c hc; simp only [Stmt.ueberBoden, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1
      · have := h c hc; simp only [Stmt.ueberBoden, Bool.and_eq_true] at this
        exact this.2
  | .breaking _ body, h => by
      simp only [mS]
      exact mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .traverse _ _ body, h => by
      simp only [mS]
      exact mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .retry _ _ body ueber, h => by
      simp only [mS, Bool.and_eq_true]
      exact ⟨mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden],
        mB_boden ueber fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]⟩
  | .forever _ _ body, h => by
      simp only [mS]
      exact mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .assignSlot .., _ => rfl
  | .assignDurch .., _ => rfl
  | .assignGlob .., _ => rfl
  | .schreibBytes .., _ => rfl
  | .assignVar .., _ => rfl
  | .uebergang .., _ => rfl
  | .axiomCall .., _ => rfl
  | .regSchreib .., _ => rfl
  | .transition .., _ => rfl
  | .publish .., _ => rfl
  | .advances .., _ => rfl
  | .retires .., _ => rfl
  | .ret .., _ => rfl
  | .retGrund .., _ => rfl
  | .leave _, _ => rfl
  | .next _, _ => rfl

theorem mB_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (bl : Block D V l Γ Λ Λ') → Block.BodenOk b bl → mB A bl = true
  | .nil, _ => rfl
  | .cons s rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mS_boden s fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bind _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .bindCall g _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨hr g, mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bindCallInd (n := n) _ _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨hi n, mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨⟨hr g, mE_boden err fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩,
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .regLies _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .regLiesElse _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .awaits _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .exchange _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .narrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .pruefung _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .gleit _ _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .gleitLit _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .gleitVon _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .gleitNarrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩

theorem mArms_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → Arms.BodenOk b a → mArms A a = true
  | .nil, _ => rfl
  | .cons bl rest, h => by
      simp only [mArms, Bool.and_eq_true]
      exact ⟨mB_boden bl fun c hc => by have := h c hc; simp_all [Arms.ueberBoden],
        mArms_boden rest fun c hc => by have := h c hc; simp_all [Arms.ueberBoden]⟩

theorem mGArms_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → GrundArms.BodenOk b a → mGArms A a = true
  | .nil, _ => rfl
  | .cons bl rest, h => by
      simp only [mGArms, Bool.and_eq_true]
      exact ⟨mB_boden bl fun c hc => by have := h c hc; simp_all [GrundArms.ueberBoden],
        mGArms_boden rest fun c hc => by have := h c hc; simp_all [GrundArms.ueberBoden]⟩

theorem mE_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → Endblock.BodenOk b e → mE A e = true
  | .ret .., _ => rfl
  | .retGrund .., _ => rfl
  | .leave _, _ => rfl
  | .next _, _ => rfl
  | .cons s rest, h => by
      simp only [mE, Bool.and_eq_true]
      exact ⟨mS_boden s fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden],
        mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]⟩
  | .bind _ rest, h => by
      simp only [mE]
      exact mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]

end

end Stufen

/-- **The model's floor discipline `StufenOk` gives the residue form**: the
    floors on the bodies. -/
theorem stufenM_of_ok {P : Programm D} (h : StufenOk P) : StufenM P := by
  intro f
  refine mE_boden (bodenM f) (fun _ => rfl) (fun _ => rfl) (bodenF f) (fun L hL => ?_) _
    (fun c hc => h f c hc)
  unfold bodenM
  cases hb : bodenF f with
  | none => rfl
  | some c => exact decide_eq_true (hL c hb)

#print axioms Gabbro.Grammatik.stufenM_of_ok
#print axioms Gabbro.Grammatik.rangInvG_erreichbar
#print axioms Gabbro.Grammatik.sperre_rang
#print axioms Gabbro.Grammatik.schritt_an_sperre
#print axioms Gabbro.Grammatik.keine_verklemmungG
#print axioms Gabbro.Grammatik.keine_verklemmungG'

end Gabbro.Grammatik
