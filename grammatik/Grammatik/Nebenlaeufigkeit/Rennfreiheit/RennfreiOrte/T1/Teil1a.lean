/-
  File:      Grammatik/RennfreiOrte.lean
  Subject:   RACE FREEDOM ON UNGUARDED CARRIERS -- what a thread can touch
             is bounded by its call graph, so an unguarded carrier that one
             thread's graph may write and no other thread's graph may read
             or write is never part of a cross-thread pair.

  `rennfrei_g_voll` (RennfreiVoll.lean) orders every cross-thread pair on a
  LOCK-GUARDED carrier. For an unguarded carrier there is no lock to order
  anything, so the claim there is that such a pair does not exist. That
  needs two static bounds per step, both new:

  * **Reads.** Every read event a step records lies on a carrier of the
    footprint `fussOrteG P f` of the function `f` of the acting frame. The
    residue predicate `GRest.oR P C` ("every expression still to run reads
    only carriers in `C`", over the existing `blockOrteP`/`endblockOrteP`)
    is kept by every rule (`schrittOrte`, the twin of `schrittMerk`); the
    frame invariant `OrteInvG` holds on every reachable machine
    (`orteInvG_erreichbar`) with `C` the footprint of each frame's function.
  * **Writes.** Every write event a step records is on a carrier the acting
    frame's function may write by signature (`TraegerSchreibt`): every write
    form carries its permission `hw` in the syntax; axioms write only their
    declared frame, which the call's `hw` bounds. Memory changes are
    `schritt_traeger`.

  `schritt_zugriffe` joins both per step. With the call-graph invariant
  `merkInvG_erreichbar` every acting function lies in its thread's call
  graph, which gives `zugriff_im_graph`, and from it the theorem
  `rennfrei_ungeschuetzt`: a carrier that is SEPARATED over the call graphs
  (`SchreibGetrenntK`: one graph may write it => no other graph may write it
  or have it in a footprint) has no cross-thread access pair with a write.
  `rennfrei_alle` combines both halves into the full race-freedom statement
  for every carrier that is not atomic and not a publish payload.
-/
module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. What a residue still reads -/

/-- **The residue reads only carriers in `C`**: every block, end block,
    loop condition and loop body still to run has its read carriers
    (`blockOrteP`, `endblockOrteP`, `Expr.orte`) in `C`. -/
def GRest.oR (P : Programm D) (C : D.Tab ⊕ D.Glob → Bool) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => (endblockOrteP P e).all C = true
  | _, _, _, .dann b k => (blockOrteP P b).all C = true ∧ k.oR P C
  | _, _, _, .schrumpf k => k.oR P C
  | _, _, _, .frei _ k => k.oR P C
  | _, _, _, .trav _ inv body _ k =>
      inv.orte.all C = true ∧ (blockOrteP P body).all C = true ∧ k.oR P C
  | _, _, _, .travRest _ inv body _ k =>
      inv.orte.all C = true ∧ (blockOrteP P body).all C = true ∧ k.oR P C
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte.all C = true ∧ (blockOrteP P body).all C = true ∧
        (blockOrteP P ueber).all C = true ∧ k.oR P C
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte.all C = true ∧ (blockOrteP P body).all C = true ∧
        (blockOrteP P ueber).all C = true ∧ k.oR P C
  | _, _, _, .ewig _ _ inv body k =>
      inv.orte.all C = true ∧ (blockOrteP P body).all C = true ∧ k.oR P C
  | _, _, _, .ewigRest _ _ inv body k =>
      inv.orte.all C = true ∧ (blockOrteP P body).all C = true ∧ k.oR P C
  | _, _, _, .wartet b k => (blockOrteP P b).all C = true ∧ k.oR P C
  | _, _, _, .wartetSonst _ err b k =>
      (endblockOrteP P err).all C = true ∧ (blockOrteP P b).all C = true ∧ k.oR P C
  | _, _, _, .abbruch k => k.oR P C
  | _, _, _, .leer => True

section Wahl

variable {V : Vertrag D} {l : Bool}

theorem all_armWahlG (P : Programm D) (C : D.Tab ⊕ D.Glob → Bool) {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    (armsOrteP P arms).all C = true → (blockOrteP P (armWahlG arms v).2.1).all C = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [armsOrteP, List.all_append, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [armsOrteP, List.all_append, Bool.and_eq_true] at h
      exact all_armWahlG P C rest _ h.2

theorem all_grundWahlG (P : Programm D) (C : D.Tab ⊕ D.Glob → Bool) {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    (grundArmsOrteP P arms).all C = true → (blockOrteP P (grundWahlG arms r)).all C = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [grundArmsOrteP, List.all_append, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [grundArmsOrteP, List.all_append, Bool.and_eq_true] at h
      exact all_grundWahlG P C rest _ h.2

end Wahl
set_option hygiene false in
/-! ## 2. Every rule keeps the read bound -/

/-- Case (A) of `schrittOrte`: a head-local step. -/
macro "kopfO" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self],
    fun C hok => ?_⟩
  dsimp only; rw [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hok
  dsimp only at hok ⊢
  simp only [GRest.oR, endblockOrteP, blockOrteP, stmtOrteP, blockOrteP_alsBlock,
    List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
    Bool.true_and] at hok ⊢))

set_option maxHeartbeats 4000000 in
/-- **Every rule of G, classified by what it does to the read bound**: (A) a
    head-local step keeps the stack and the function and carries `oR` to the
    new residue; (B) a push suspends the head as a caller frame carrying
    `oR` and enters the callee's body; (C) a pop resumes the caller, whose
    residue carried `oR`. -/
theorem schrittOrte {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M') :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      (M'.faeden f).kopf.f = (M.faeden f).kopf.f ∧
      ∀ C : D.Tab ⊕ D.Glob → Bool, (M.faeden f).kopf.rest.2.2.2.2.oR P C →
        (M'.faeden f).kopf.rest.2.2.2.2.oR P C) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      caller'.f = (M.faeden f).kopf.f ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      ∀ C : D.Tab ⊕ D.Glob → Bool, (M.faeden f).kopf.rest.2.2.2.2.oR P C →
        caller'.rest.2.2.2.2.oR P C) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      (M'.faeden f).kopf.f = caller.f ∧
      ∀ C : D.Tab ⊕ D.Glob → Bool, caller.rest.2.2.2.2.oR P C →
        (M'.faeden f).kopf.rest.2.2.2.2.oR P C) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw =>
      kopfO
      have h := all_armWahlG P C arms (eval σ₁ v σ₁ ρ) (by simp_all)
      rw [hw] at h
      have h2 : (blockOrteP P b).all C = true := h
      simp_all
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
      kopfO
      have h := all_armWahlG P C arms (eval σ₁ v σ₁ ρ) (by simp_all)
      rw [hw] at h
      have h2 : (blockOrteP P b).all C = true := h
      simp_all
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
      kopfO
      have h := all_grundWahlG P C arms (eval σ₁ r σ₁ ρ) (by simp_all)
      rw [hw] at h
      simp_all
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact hok.2
    | rueck caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | _ =>
      kopfO
      all_goals simp_all
  | g2 hs =>
    cases hs with
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.2, hok.2⟩
    | _ =>
      kopfO
      all_goals simp_all
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.2, hok.2⟩
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1.2, hok.1.2, hok.2⟩
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.2, hok.2⟩
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact hok.2
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.2, hok.2⟩
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1.2, hok.1.2, hok.2⟩
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err .nil
          (.dann rest k)⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], rfl,
        by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
      rw [hhead] at hok
      dsimp only at hok ⊢
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1.2, by simp, hok.1.2, hok.2⟩
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.oR] <;> exact fun h => by simp_all
    | _ =>
      kopfO
      all_goals simp_all
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact id
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.oR] <;> exact fun h => by simp_all
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [GRest.oR] <;> exact fun h => by simp_all
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.oR, blockOrteP_alsBlock]
      exact fun h => ⟨h.1, h.2.2⟩
    | _ =>
      kopfO
      all_goals simp_all
  | g5 hs =>
    cases hs with
    | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.oR, blockOrteP_alsBlock]
      exact fun h => ⟨h.1, h.2.2⟩
    | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [GRest.oR, blockOrteP_alsBlock]
      exact fun h => ⟨h.1, h.2.2⟩
    | _ =>
      kopfO
      all_goals simp_all
  | g6 hs =>
    cases hs with
    | _ =>
      kopfO
      all_goals simp_all

end Gabbro.Grammatik
