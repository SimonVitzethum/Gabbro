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
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden

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

section Wahl

variable {V : Vertrag D} {l : Bool}

theorem all_armWahlG (P : Programm D) (C : D.Tab ⊕ D.Glob → Bool) {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
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
/-! ## 2. Every rule keeps the read bound -/

set_option hygiene false in
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
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw =>
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
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun C hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hok ⊢
    exact ⟨hok.1.2, hok.2⟩
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
  | rueck caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact id
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
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun C => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [GRest.oR] <;> exact fun h => by simp_all
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

/-! ## 3. The frame invariant -/

/-- The footprint of `f`, as a carrier test. -/
def fussC (P : Programm D) (f : D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  istIn (fussOrteG P f) c

/-- **The read bound of a thread**: every frame's residue reads only
    carriers of its function's footprint. -/
def OrteInvG (P : Programm D) (z : RufFadenG D) : Prop :=
  ∀ F ∈ z.kopf :: z.stapel, F.rest.2.2.2.2.oR P (fussC P F.f)

theorem body_oR (P : Programm D) (g : D.Fn) :
    (endblockOrteP P (P.rumpf g)).all (fussC P g) = true :=
  List.all_eq_true.mpr fun _ hc => istIn_iff.mpr (fuss_rumpfG P g hc)

section Inv

variable {P : Programm D} {O : Orakel D} {pa : Nat}

theorem orteInvG_schritt {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O pa M f M')
    (h : OrteInvG P (M.faeden f)) : OrteInvG P (M'.faeden f) := by
  have hk := h _ List.mem_cons_self
  rcases schrittOrte hs with ⟨hst, hf, hR⟩ | ⟨g, caller', rho, s0, hst, hcf, hkopf, hR⟩ |
      ⟨caller, rst, hpop, hst, hf, hR⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · have := hR (fussC P (M.faeden f).kopf.f) hk
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (List.mem_cons_of_mem _ hF)
  · have hc := hR (fussC P (M.faeden f).kopf.f) hk
    intro F hF
    rw [hst, hkopf] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact body_oR P g
    · rcases List.mem_cons.mp hF with rfl | hF
      · rw [← hcf] at hc
        exact hc
      · exact h F (List.mem_cons_of_mem _ hF)
  · have hc := h caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · have := hR _ hc
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (by rw [hpop]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

/-- **The read bound on every reachable machine** -- no premise: a frame
    enters with its function's body, whose reads are its footprint. -/
theorem orteInvG_erreichbar (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, OrteInvG P (M.faeden t) := by
  induction hr with
  | start =>
      intro t F hF
      have e : (RufStartG P sp init).faeden t =
          ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
            Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
            startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
        cases init t
        rfl
      rw [e] at hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact body_oR P _
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact orteInvG_schritt hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Inv
/-! ## 4. The events of one step -/

/-- The write permission of a contract, per carrier. -/
def schreibV (V : Vertrag D) : D.Tab ⊕ D.Glob → Bool
  | .inl t => V.schreibt t
  | .inr g => V.gschreibt g

theorem schreibV_vertragVon (f : D.Fn) (c : D.Tab ⊕ D.Glob) :
    schreibV (vertragVon D f) c = TraegerSchreibt f c := by
  cases c <;> rfl

/-- **Recorded events within bounds**: every read event is on a carrier in
    `C`, every write event on a carrier in `W`. -/
def EvOk (C W : D.Tab ⊕ D.Glob → Bool) (X : List (Ereignis D)) : Prop :=
  ∀ e ∈ X, ∀ c w, zugriffVon e = some (c, w) → (w = false → C c = true) ∧ (w = true → W c = true)

section Ev

variable {C W : D.Tab ⊕ D.Glob → Bool}

theorem evOk_nil : EvOk (D := D) C W [] := fun _ h => absurd h List.not_mem_nil

theorem evOk_append {X Y : List (Ereignis D)} (hX : EvOk C W X) (hY : EvOk C W Y) :
    EvOk C W (X ++ Y) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hX e he
  · exact hY e he

theorem evOk_lese (σ : World D) (Λ : List (Res D)) {os : List (D.Tab ⊕ D.Glob)}
    (h : os.all C = true) : EvOk C W (leseEv σ Λ os) := by
  intro e he c w hz
  simp only [leseEv, List.mem_map] at he
  obtain ⟨o, ho, rfl⟩ := he
  have hC := (List.all_eq_true.mp h) o ho
  cases o with
  | inl t =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨fun _ => hC, fun h => by cases h⟩
  | inr g =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨fun _ => hC, fun h => by cases h⟩

theorem evOk_schreibT {t : D.Tab} {Λ : List (Res D)} {h : List D.Lock}
    (hw : W (.inl t) = true) : EvOk C W [Ereignis.zugriff t true Λ h] := by
  intro e he c w hz
  rw [List.mem_singleton] at he
  subst he
  simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact ⟨fun h => (by cases h), fun _ => hw⟩

theorem evOk_schreibG {g : D.Glob} {Λ : List (Res D)} {h : List D.Lock}
    (hw : W (.inr g) = true) : EvOk C W [Ereignis.gzugriff g true Λ h] := by
  intro e he c w hz
  rw [List.mem_singleton] at he
  subst he
  simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact ⟨fun h => (by cases h), fun _ => hw⟩

theorem evOk_sperre (e : Ereignis D) (he : zugriffVon e = none) : EvOk C W [e] := by
  intro e' h c w hz
  rw [List.mem_singleton] at h
  subst h
  rw [he] at hz
  cases hz

theorem schreibBytes_ev (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) (hw : W (.inl t) = true) :
    ∀ (bs : List Byte) (σ : World D) (k : Int),
      ∃ X, (σ.schreibBytes t f hf Λ k bs).spur = X ++ σ.spur ∧ EvOk C W X := by
  intro bs
  induction bs with
  | nil => intro σ k; exact ⟨[], rfl, evOk_nil⟩
  | cons b bs ih =>
      intro σ k
      simp only [World.schreibBytes]
      obtain ⟨X, hX, hok⟩ := ih (σ.schreibSlot t Λ k f
        (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))) (k + 1)
      refine ⟨X ++ [Ereignis.zugriff t true Λ σ.haelt], ?_, evOk_append hok (evOk_schreibT hw)⟩
      rw [hX, List.append_assoc]
      rfl

theorem axiomSpur_ev {tabs : List D.Tab} {globs : List D.Glob} {a : D.Ax} {Λ : List (Res D)}
    {h : List D.Lock} (hw : ∀ t, D.aschreibt a t = true → W (.inl t) = true)
    (hg : ∀ g, D.agschreibt a g = true → W (.inr g) = true) :
    EvOk C W (axiomSpur tabs globs a Λ h) := by
  intro e he c w hz
  rcases axiomSpur_mem he with ⟨t, _, ht, rfl⟩ | ⟨g, _, hgg, rfl⟩
  · simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨fun h => (by cases h), fun _ => hw t ht⟩
  · simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨fun h => (by cases h), fun _ => hg g hgg⟩

/-- The trace of an axiom answer under held guards: the declared writes. -/
theorem axiom_ev (O : Orakel D) (hO : GutO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    {Λ : List (Res D)} (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hh : HeldIn Λ σ.haelt)
    (hw : ∀ t, D.aschreibt a t = true → W (.inl t) = true)
    (hg : ∀ g, D.agschreibt a g = true → W (.inr g) = true) :
    ∃ X, (O.wirkt a σ ρ).1.spur = X ++ σ.spur ∧ EvOk C W X := by
  have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt :=
    fun t hwr L hL => hh L (hd t hwr _ hL)
  have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt :=
    fun g hwr L hL => hh L (hgd g hwr _ hL)
  obtain ⟨_, _, hcond⟩ := hO a σ ρ
  obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
  exact ⟨_, hspur, axiomSpur_ev hw hg⟩

end Ev

end Gabbro.Grammatik
