/-
  File:      Grammatik/Verklemmung.lean
  Subject:   DEADLOCK FREEDOM FROM LOCK RANKS on machine G (THEOREM-MAP §13.5
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
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtStart
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden

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
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
    · simp only [rufUpdateG_self]
      rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
    · intro K hK
      dsimp only; rw [rufUpdateG_self]
      rw [hhead] at hK
      exact hK
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


end Gabbro.Grammatik
