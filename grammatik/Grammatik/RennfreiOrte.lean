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
import Grammatik.RennfreiVoll
import Grammatik.ZielOrtMehrfaden

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

/-- **The events of a leaf**: its reads lie on its read carriers
    (`stmtOrteP`), its writes on carriers its contract may write. -/
theorem blatt_ev (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hO : GutO O)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (C : D.Tab ⊕ D.Glob → Bool) :
    ∀ (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true → (stmtOrteP P s).all C = true →
      ∀ (σ : World D) (ρ : Env D Γ), HeldIn Λ σ.haelt → ∀ σ',
        (execStmt O passes R s σ ρ).welt = some σ' →
          ∃ X, σ'.spur = X ++ σ.spur ∧ EvOk C (schreibV V) X
  | .assignSlot t f i e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ (i.orte ++ e.orte), rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
  | .assignDurch p t _ f i e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ (p.orte ++ i.orte ++ e.orte), rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
  | .assignGlob g e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ e.orte, rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibG hw) (evOk_lese σ Λ hC)
  | .schreibBytes t f hf n i _ _ e hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      obtain ⟨X, hX, hok⟩ := schreibBytes_ev (C := C) (W := schreibV V) t f hf Λ hw
        (zahlZuBytes n (eval (σ.lese Λ (i.orte ++ e.orte)) e (σ.lese Λ (i.orte ++ e.orte)) ρ).n)
        (σ.lese Λ (i.orte ++ e.orte))
        (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρ).n
      refine ⟨X ++ leseEv σ Λ (i.orte ++ e.orte), ?_, evOk_append hok (evOk_lese σ Λ hC)⟩
      rw [hX, List.append_assoc]
      rfl
  | .assignVar x e, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨leseEv σ Λ e.orte, rfl, evOk_lese σ Λ hC⟩
  | .uebergang t f hτ i von nach hn he hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        refine ⟨_ :: leseEv σ Λ (.inl t :: i.orte), rfl, ?_⟩
        exact evOk_append (X := [_]) (evOk_schreibT hw) (evOk_lese σ Λ hC)
      · simp [Ausgang.welt] at h
  | .axiomCall a args _ hw hg hd hgd, _, hC, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have e1 : σ1 = (O.wirkt a (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst ha
          simp only [axiomAntwort] at this
          exact this.symm
        obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := schreibV V) O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldIn hh)
          hw hg
        refine ⟨X ++ leseEv σ Λ args.orte, ?_, evOk_append hok (evOk_lese σ Λ hC)⟩
        rw [e1, hX, List.append_assoc]
        rfl
      · simp [Ausgang.welt] at h
  | .regSchreib r _ e, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨leseEv σ Λ e.orte, rfl, evOk_lese σ Λ hC⟩
  | .transition .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .publish g e _ _ hw hL, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      refine ⟨_ :: leseEv σ Λ e.orte, rfl, ?_⟩
      exact evOk_append (X := [_]) (evOk_schreibG hw) (evOk_lese σ Λ hC)
  | .advances .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .retires .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .ret e _, _, hC, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨leseEv σ Λ e.orte, rfl, evOk_lese σ Λ hC⟩
  | .retGrund .., _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .leave _, _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .next _, _, _, σ, ρ, _, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact ⟨[], rfl, evOk_nil⟩
  | .ite .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .onOption .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .onTag .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .onGrund .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .call .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .callInd .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .locks .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .breaking .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .traverse .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .retry .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf
  | .forever .., hleaf, _, _, _, _, _, _ => by simp [Stmt.istBlatt] at hleaf

set_option hygiene false in
/-- A step whose trace grows by the reads of one list of carriers of the
    head residue. -/
macro "leseO" : tactic => `(tactic| (
  simp only [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hC
  dsimp only at hC ⊢
  simp only [GRest.oR, endblockOrteP, blockOrteP, stmtOrteP, blockOrteP_alsBlock,
    List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
    Bool.true_and] at hC
  subst_vars
  first
    | exact ⟨[], rfl, evOk_nil⟩
    | exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by simp_all)⟩))

set_option maxHeartbeats 4000000 in
/-- **The events of one step, bounded**: given the read bound `C` of the
    acting frame's residue, every read event of the step is on a carrier in
    `C` and every write event on a carrier the acting frame's function may
    write. -/
theorem schritt_ev {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    {C : D.Tab ⊕ D.Glob → Bool} (hC : (M.faeden f).kopf.rest.2.2.2.2.oR P C) :
    ∃ X, (M'.faeden f).spur = X ++ (M.faeden f).spur ∧
      EvOk C (TraegerSchreibt (M.faeden f).kopf.f) X := by
  have hW : ∀ c, schreibV (vertragVon D (M.faeden f).kopf.f) c =
      TraegerSchreibt (M.faeden f).kopf.f c := schreibV_vertragVon _
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      obtain ⟨X, hX, hok⟩ := blatt_ev P O passes keinRuf hO C s hleaf hC.1 (M.weltVon f) ρ hΛ
        σ' (by rw [hstep]; rfl)
      exact ⟨X, hX, fun e he c w hz => by rw [← hW]; exact hok e he c w hz⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      obtain ⟨X, hX, hok⟩ := blatt_ev P O passes keinRuf hO C s hleaf hC.1.1 (M.weltVon f) ρ hΛ
        σ' (by rw [hstep]; rfl)
      exact ⟨X, hX, fun e he c w hz => by rw [← hW]; exact hok e he c w hz⟩
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | freiGib l Γ Λ L k ρ hhead =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact ⟨[_], rfl, evOk_sperre _ rfl⟩
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, List.all_append, Bool.and_eq_true] at hC
      rw [hs₁, leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.2.1⟩
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
      simp only [rufUpdateG_self]
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨[], rfl, evOk_nil⟩
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, List.all_cons, Bool.and_eq_true] at hC
      subst hs₂ hs₁
      refine ⟨_ :: leseEv (M.weltVon f) Λ (Sum.inr g :: neuE.orte), rfl, ?_⟩
      refine evOk_append (X := [_]) (evOk_schreibG ?_) (evOk_lese _ _ ?_)
      · rw [← hW]; exact hw
      · simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨hC.1.1.1, hC.1.1.2⟩
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        ((M.weltVon f).lese Λ args.orte)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ leseEv (M.weltVon f) Λ args.orte, ?_, evOk_append hok (evOk_lese _ _ hC.1.1)⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1.1⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1.1⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1.1.1⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by
        simp only [List.all_append, Bool.and_eq_true]; exact hC.1.1)⟩
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by
        simp only [List.all_append, Bool.and_eq_true]; exact hC.1)⟩
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs0
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ (by
        simp only [List.all_append, Bool.and_eq_true]; exact hC.1.1)⟩
  | rueck caller rst hpop Γ Λ e hperm ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      simp only [rufUpdateG_self]
      rw [hh] at hC
      simp only [GRest.oR, endblockOrteP] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
      simp only [rufUpdateG_self]
      rw [hh] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hh g hfg rho hrho s0
      hs0 hΛ s1 hs1 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hh] at hC
      simp only [GRest.oR, endblockOrteP] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, blockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1.1⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller
      hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, stmtOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs1
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.1⟩
  | _ => leseO

/-! ## 5. Every access of a step is bounded by its function -/

/-- The access set of a step is its bounded events. -/
theorem zugriffe_ev {M M' : RufMaschineG D} {f : Faden} {C W : D.Tab ⊕ D.Glob → Bool}
    {X : List (Ereignis D)} (hX : (M'.faeden f).spur = X ++ (M.faeden f).spur)
    (hok : EvOk C W X) {c : D.Tab ⊕ D.Glob} {w : Bool} (h : (c, w) ∈ zugriffe M M' f) :
    (w = false → C c = true) ∧ (w = true → W c = true) := by
  rw [zugriffe_ereignisse, ereignisse_eq hX, List.mem_filterMap] at h
  obtain ⟨e, he, hz⟩ := h
  exact hok e he c w hz

section Lauf

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **A step's accesses, bounded by the acting function**: a read is on a
    footprint carrier of the acting frame's function; a write (event or
    memory change) is on a carrier that function may write. -/
theorem schritt_zugriffe (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M M' : RufMaschineG D} {f : Faden}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) (hs : RufSchrittG P O passes M f M')
    (c : D.Tab ⊕ D.Glob) :
    (ZugriffG M M' f c → c ∈ fussOrteG P (M.faeden f).kopf.f ∨
      TraegerSchreibt (M.faeden f).kopf.f c = true) ∧
    (SchreibG M M' f c → TraegerSchreibt (M.faeden f).kopf.f c = true) := by
  have hI := orteInvG_erreichbar sp init hr f _ List.mem_cons_self
  obtain ⟨X, hX, hok⟩ := schritt_ev hO hs hI
  have hmem : ¬ TraegerGleich M'.speicher M.speicher c →
      TraegerSchreibt (M.faeden f).kopf.f c = true := by
    intro hn
    cases hb : TraegerSchreibt (M.faeden f).kopf.f c
    · exact absurd (schritt_traeger hO hs c (Or.inr hb)) hn
    · rfl
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rcases hz with ⟨w, hw⟩ | hm
    · have h := zugriffe_ev hX hok hw
      cases w
      · exact Or.inl (istIn_iff.mp (h.1 rfl))
      · exact Or.inr (h.2 rfl)
    · exact Or.inr (hmem hm)
  · rcases hz with hw | hm
    · exact (zugriffe_ev hX hok hw).2 rfl
    · exact hmem hm

/-- **Accesses stay in the call graph**: with closed per-thread call graphs
    `K` containing the start functions, every access of a step of thread
    `f` is a footprint read or a signature write of SOME function of `K f`,
    and every write is a signature write of some function of `K f`. -/
theorem zugriff_im_graph (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {M M' : RufMaschineG D} {f : Faden}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) (hs : RufSchrittG P O passes M f M')
    (c : D.Tab ⊕ D.Glob) :
    (ZugriffG M M' f c → ∃ g, K f g = true ∧
      (c ∈ fussOrteG P g ∨ TraegerSchreibt g c = true)) ∧
    (SchreibG M M' f c → ∃ g, K f g = true ∧ TraegerSchreibt g c = true) := by
  have hInv := merkInvG_erreichbar (O := O) (pa := passes) sp init (fun t g => K t g = true)
    (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
  have hK := (hInv f _ List.mem_cons_self).1
  obtain ⟨h1, h2⟩ := schritt_zugriffe hO sp init hr hs c
  exact ⟨fun hz => ⟨_, hK, h1 hz⟩, fun hz => ⟨_, hK, h2 hz⟩⟩

/-- **Write-separated over the call graphs**: if one thread's graph may
    write `c`, no OTHER thread's graph may write it or have it in a
    footprint. -/
def SchreibGetrenntK (P : Programm D) (K : Faden → D.Fn → Bool) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ t u, t ≠ u → ∀ g, K t g = true → TraegerSchreibt g c = true →
    ∀ h, K u h = true → TraegerSchreibt h c = false ∧ c ∉ fussOrteG P h

/-- **No cross-thread pair with a write on a write-separated carrier.** On
    every run from the start, two accesses to `c` by different threads, one
    of them a write, do not exist when `c` is write-separated over closed
    call graphs that contain the start functions. -/
theorem rennfrei_ungeschuetzt (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true)
    (ms : Nat → RufMaschineG D) (ts : Nat → Faden) (n : Nat)
    (hl : LaufG P O passes (RufStartG P sp init) ms ts n) (i j : Nat) (hij : i < j)
    (hjn : j < n) (hfg : ts i ≠ ts j) (c : D.Tab ⊕ D.Glob) (hsep : SchreibGetrenntK P K c)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (ts i) c) (hzj : ZugriffG (ms j) (ms (j + 1)) (ts j) c)
    (hw : SchreibG (ms i) (ms (i + 1)) (ts i) c ∨ SchreibG (ms j) (ms (j + 1)) (ts j) c) :
    False := by
  have gi := zugriff_im_graph hO hvoll sp init K hAbg hWurzel
    (laufG_erreichbar hl i (by omega)) (hl.2 i (by omega)) c
  have gj := zugriff_im_graph hO hvoll sp init K hAbg hWurzel
    (laufG_erreichbar hl j (by omega)) (hl.2 j (by omega)) c
  rcases hw with hw | hw
  · obtain ⟨g, hg, hgw⟩ := gi.2 hw
    obtain ⟨h, hh, hhz⟩ := gj.1 hzj
    obtain ⟨h1, h2⟩ := hsep _ _ hfg g hg hgw h hh
    rcases hhz with hhz | hhz
    · exact h2 hhz
    · rw [h1] at hhz; cases hhz
  · obtain ⟨g, hg, hgw⟩ := gj.2 hw
    obtain ⟨h, hh, hhz⟩ := gi.1 hzi
    obtain ⟨h1, h2⟩ := hsep _ _ (Ne.symm hfg) g hg hgw h hh
    rcases hhz with hhz | hhz
    · exact h2 hhz
    · rw [h1] at hhz; cases hhz

/-- **Race freedom for every carrier** (not atomic, not a publish payload):
    a cross-thread pair with a write on `c` is ordered through a guard lock
    of `c`. Guarded carriers: `rennfrei_g_voll`. Unguarded carriers: every
    such carrier is write-separated (`hsep`), so the pair does not exist
    (`rennfrei_ungeschuetzt`). -/
theorem rennfrei_alle (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hex : StartExklusiv init) (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true)
    (hsep : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
      SchreibGetrenntK P K c) :
    ∀ (ms : Nat → RufMaschineG D) (ts : Nat → Faden) (n : Nat),
      LaufG P O passes (RufStartG P sp init) ms ts n →
      ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → ts i ≠ ts j →
        ZugriffG (ms i) (ms (i + 1)) (ts i) c → ZugriffG (ms j) (ms (j + 1)) (ts j) c →
        (SchreibG (ms i) (ms (i + 1)) (ts i) c ∨ SchreibG (ms j) (ms (j + 1)) (ts j) c) →
        ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
        ∃ L, Bewacht c L ∧ GeordnetG ms ts L i j := by
  intro ms ts n hl i j c hij hjn hfg hzi hzj hw hA hPa
  by_cases hB : ∃ L, Bewacht c L
  · obtain ⟨L, hL⟩ := hB
    exact ⟨L, hL, rennfrei_g_voll P O passes sp init hO hex ms ts n hl i j hij hjn hfg c L hL
      hzi hzj⟩
  · exact (rennfrei_ungeschuetzt hO hvoll sp init K hAbg hWurzel ms ts n hl i j hij hjn hfg c
      (hsep c (fun L hL => hB ⟨L, hL⟩) hA hPa) hzi hzj hw).elim

end Lauf

#print axioms Gabbro.Grammatik.schrittOrte
#print axioms Gabbro.Grammatik.orteInvG_erreichbar
#print axioms Gabbro.Grammatik.blatt_ev
#print axioms Gabbro.Grammatik.schritt_ev
#print axioms Gabbro.Grammatik.schritt_zugriffe
#print axioms Gabbro.Grammatik.zugriff_im_graph
#print axioms Gabbro.Grammatik.rennfrei_ungeschuetzt
#print axioms Gabbro.Grammatik.rennfrei_alle

end Gabbro.Grammatik
