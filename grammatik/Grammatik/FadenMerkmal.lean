/-
  File:      Grammatik/FadenMerkmal.lean
  Subject:   WHAT A THREAD CAN STILL RUN -- a syntactic feature set of a
             residue (the direct callees, the signatures of indirect calls,
             the locks taken by `locks` blocks) and its invariance along
             every rule of machine G.

  The goal theorem needs, for concurrency, three facts about each thread
  that no invariant of G carried:

  * which functions the thread can run at all (the call graph from its start
    function), to exempt carriers only one thread reaches from the footprint
    check (`ZielOrtMehrfaden.lean`);
  * that every `locks L` still ahead of a frame takes a lock of rank at least
    the frame's floor (`StufenOk` read on the residue), for deadlock freedom
    (`Verklemmung.lean`);
  * that the `abbruch` layer behind an `else` branch names the same held
    locks as the block it stands behind (so a `leave`/`next` out of it keeps
    the held set).

  All three are one predicate `GRest.mR A` over a feature set `A : Merkmal D`,
  hereditary over the residue, and `schrittMerk` classifies every rule: a
  head-local step keeps the stack and the function and carries the
  predicate to the new residue; a push names a callee the old residue
  admitted and carries the predicate to the suspended caller; a pop resumes
  the caller with the predicate its suspended residue had. The call-graph
  closure `MerkAbg` then gives the thread invariant `MerkInvG` on every
  reachable machine (`merkInvG_erreichbar`).
-/
import Grammatik.RufHaeltG
import Grammatik.RufAdaequatG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The feature set -/

/-- **A feature set**: the admitted direct callees, the admitted signatures
    of indirect calls, the admitted locks of `locks` blocks. -/
structure Merkmal (D : Deklaration) where
  ruf : D.Fn → Bool
  ind : Nat → Bool
  sperre : D.Lock → Bool

mutual

/-- Every call, indirect call and `locks` in the statement is admitted. -/
def mS (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => mB A t && mB A e
  | .onOption _ p a => mB A p && mB A a
  | .onTag _ arms => mArms A arms
  | .onGrund _ arms => mGArms A arms
  | .call g _ _ _ => A.ruf g
  | .callInd (n := n) _ _ _ _ => A.ind n
  | .locks L _ body => A.sperre L && mB A body
  | .breaking _ body => mB A body
  | .traverse _ _ body => mB A body
  | .retry _ _ body ueber => mB A body && mB A ueber
  | .forever _ _ body => mB A body
  | .assignSlot .. => true
  | .assignDurch .. => true
  | .assignGlob .. => true
  | .schreibBytes .. => true
  | .assignVar .. => true
  | .uebergang .. => true
  | .axiomCall .. => true
  | .regSchreib .. => true
  | .transition .. => true
  | .publish .. => true
  | .advances .. => true
  | .retires .. => true
  | .ret .. => true
  | .retGrund .. => true
  | .leave _ => true
  | .next _ => true

def mB (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => mS A s && mB A rest
  | .bind _ rest => mB A rest
  | .bindCall g _ _ _ _ rest => A.ruf g && mB A rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => A.ind n && mB A rest
  | .bindCallElse g _ _ _ _ err rest => A.ruf g && mE A err && mB A rest
  | .bindAxiom _ _ _ _ _ _ _ rest => mB A rest
  | .regLies _ _ rest => mB A rest
  | .regLiesElse _ _ _ sonst rest => mE A sonst && mB A rest
  | .awaits _ _ _ _ rest => mB A rest
  | .exchange _ _ _ _ rest => mB A rest
  | .narrow _ _ _ sonst rest => mE A sonst && mB A rest
  | .pruefung _ sonst rest => mE A sonst && mB A rest
  | .gleit _ _ _ _ _ rest => mB A rest
  | .gleitLit _ _ _ rest => mB A rest
  | .gleitVon _ _ _ rest => mB A rest
  | .gleitNarrow _ _ _ sonst rest => mE A sonst && mB A rest

def mArms (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => mB A b && mArms A rest

def mGArms (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => mB A b && mGArms A rest

def mE (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => mS A s && mE A rest
  | .bind _ rest => mE A rest
end

/-- **The residue predicate**: every block, end block and loop body still to
    run is admitted, and every `abbruch` layer names the held locks of the
    block it stands behind. -/
def GRest.mR (A : Merkmal D) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => mE A e = true
  | _, _, _, .dann b k => mB A b = true ∧ k.mR A
  | _, _, _, .schrumpf k => k.mR A
  | _, _, _, .frei _ k => k.mR A
  | _, _, _, .trav _ _ body _ k => mB A body = true ∧ k.mR A
  | _, _, _, .travRest _ _ body _ k => mB A body = true ∧ k.mR A
  | _, _, _, .wieder _ _ body ueber k => mB A body = true ∧ mB A ueber = true ∧ k.mR A
  | _, _, _, .wiederRest _ _ body ueber k => mB A body = true ∧ mB A ueber = true ∧ k.mR A
  | _, _, _, .ewig _ _ _ body k => mB A body = true ∧ k.mR A
  | _, _, _, .ewigRest _ _ _ body k => mB A body = true ∧ k.mR A
  | _, _, _, .wartet b k => mB A b = true ∧ k.mR A
  | _, _, _, .wartetSonst _ err b k => mE A err = true ∧ mB A b = true ∧ k.mR A
  | _, _, Λ, @GRest.abbruch _ _ _ _ _ Λk k =>
      (∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) ∧ k.mR A

/-- The callee `g` is admitted: directly, or through its signature. -/
def RufZiel (A : Merkmal D) (g : D.Fn) : Prop := A.ruf g = true ∨ A.ind (D.sig g) = true

/-! ## 2. Selection and `else` blocks keep the predicate -/

section Hilfen

variable {V : Vertrag D} {l : Bool}

theorem mB_alsBlock (A : Merkmal D) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), mB A e.alsBlock.2 = mE A e
  | _, _, .ret _ _ => rfl
  | _, _, .retGrund _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]

theorem mB_armWahlG (A : Merkmal D) {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    mArms A arms = true → mB A (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [mArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [mArms, Bool.and_eq_true] at h
      exact mB_armWahlG A rest _ h.2

theorem mB_grundWahlG (A : Merkmal D) {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    mGArms A arms = true → mB A (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [mGArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [mGArms, Bool.and_eq_true] at h
      exact mB_grundWahlG A rest _ h.2

/-- The `abbruch` layer of an `else` branch run as a block: both the branch
    and the block it replaced keep the held set of their common start. -/
theorem abbruch_iff {Γ Γ' : Ctx} {Λ Λk : List (Res D)} (e : Endblock D V l Γ' Λ)
    (b : Block D V l Γ Λ Λk) :
    ∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ e.alsBlock.1 :=
  fun L => (Block.held_iff b L).trans (Block.held_iff e.alsBlock.2 L).symm

end Hilfen

/-! ## 3. Every rule, classified -/

set_option hygiene false in
/-- Case (A) of `schrittMerk`: a head-local step. -/
macro "kopfM" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self],
    fun A hok => ?_⟩
  dsimp only; rw [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hok
  dsimp only at hok ⊢
  simp only [GRest.mR, mE, mB, mS, mB_alsBlock, Bool.and_eq_true] at hok ⊢))

set_option maxHeartbeats 2000000 in
/-- **Every rule of G, classified by what it does to the residue
    predicate**: (A) a head-local step keeps the stack and the function
    and carries `mR` to the new residue; (B) a push suspends the head as a
    caller frame carrying `mR`, and names a callee the old residue admitted;
    (C) a pop resumes the caller, whose residue carried `mR`. -/
theorem schrittMerk {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M') :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      (M'.faeden f).kopf.f = (M.faeden f).kopf.f ∧
      ∀ A : Merkmal D, (M.faeden f).kopf.rest.2.2.2.2.mR A →
        (M'.faeden f).kopf.rest.2.2.2.2.mR A) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      caller'.f = (M.faeden f).kopf.f ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      ∀ A : Merkmal D, (M.faeden f).kopf.rest.2.2.2.2.mR A →
        RufZiel A g ∧ caller'.rest.2.2.2.2.mR A) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      (M'.faeden f).kopf.f = caller.f ∧
      ∀ A : Merkmal D, caller.rest.2.2.2.2.mR A → (M'.faeden f).kopf.rest.2.2.2.2.mR A) := by
  cases hs with
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw =>
    kopfM
    have h := mB_armWahlG A arms (eval σ₁ v σ₁ ρ) hok.1.1
    rw [hw] at h
    have h2 : mB A b = true := h
    simp_all
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
    kopfM
    have h := mB_armWahlG A arms (eval σ₁ v σ₁ ρ) hok.1.1
    rw [hw] at h
    have h2 : mB A b = true := h
    simp_all
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
    kopfM
    have h := mB_grundWahlG A arms (eval σ₁ r σ₁ ρ) hok.1.1
    rw [hw] at h
    simp_all
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead =>
    kopfM
    exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead =>
    kopfM
    exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead =>
    kopfM
    exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead =>
    kopfM
    exact ⟨hok.1.1, abbruch_iff sonst rest, hok.2⟩
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.mR, mE, mS, Bool.and_eq_true] at hok ⊢
    exact ⟨Or.inl hok.1, hok.2⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hok ⊢
    exact ⟨Or.inl hok.1.1, hok.1.2, hok.2⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.mR, mB, Bool.and_eq_true] at hok ⊢
    exact ⟨Or.inl hok.1.1, hok.1.2, hok.2⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.mR, mB, Bool.and_eq_true] at hok ⊢
    exact ⟨Or.inl hok.1.1.1, hok.1.1.2, hok.1.2, hok.2⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hok ⊢
    exact ⟨Or.inr (hg ▸ hok.1.1), hok.1.2, hok.2⟩
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.mR, mE, mS, Bool.and_eq_true] at hok ⊢
    exact ⟨Or.inr (hg ▸ hok.1), hok.2⟩
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], rfl,
      by dsimp only; rw [rufUpdateG_self], fun A hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.mR, mB, Bool.and_eq_true] at hok ⊢
    exact ⟨Or.inr (hg ▸ hok.1.1), hok.1.2, hok.2⟩
  | rueck caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact id
  | rueckCons caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact id
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact id
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [GRest.mR] <;> exact fun h => by simp_all
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [GRest.mR] <;> exact fun h => by simp_all
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [GRest.mR] <;> exact fun h => by simp_all
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [GRest.mR, mB_alsBlock]
    exact fun h => ⟨h.1, abbruch_iff err restb, h.2.2⟩
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [GRest.mR, mB_alsBlock]
    exact fun h => ⟨h.1, abbruch_iff err restb, h.2.2⟩
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun A => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [GRest.mR, mB_alsBlock]
    exact fun h => ⟨h.1, abbruch_iff err restb, h.2.2⟩
  | _ =>
    kopfM
    all_goals simp_all

/-! ## 4. The thread invariant -/

/-- **The thread invariant**: every frame runs a function in `Z`, and its
    residue carries the predicate at the feature set of its function. -/
def MerkInvG (Z : D.Fn → Prop) (A : D.Fn → Merkmal D) (z : RufFadenG D) : Prop :=
  ∀ F ∈ z.kopf :: z.stapel, Z F.f ∧ F.rest.2.2.2.2.mR (A F.f)

/-- **The closure of a feature assignment**: every function in `Z` has an
    admitted body, and every callee its features admit is in `Z`. -/
def MerkAbg (P : Programm D) (Z : D.Fn → Prop) (A : D.Fn → Merkmal D) : Prop :=
  ∀ f, Z f → mE (A f) (P.rumpf f) = true ∧ ∀ g, RufZiel (A f) g → Z g

section Inv

variable {P : Programm D} {O : Orakel D} {pa : Nat}

theorem merkInvG_schritt {Z : D.Fn → Prop} {A : D.Fn → Merkmal D} (hA : MerkAbg P Z A)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O pa M f M')
    (h : MerkInvG Z A (M.faeden f)) : MerkInvG Z A (M'.faeden f) := by
  have hk := h _ List.mem_cons_self
  rcases schrittMerk hs with ⟨hst, hf, hR⟩ | ⟨g, caller', rho, s0, hst, hcf, hkopf, hR⟩ |
      ⟨caller, rst, hpop, hst, hf, hR⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · refine ⟨hf ▸ hk.1, ?_⟩
      have := hR (A (M.faeden f).kopf.f) hk.2
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (List.mem_cons_of_mem _ hF)
  · obtain ⟨hz, hc⟩ := hR (A (M.faeden f).kopf.f) hk.2
    have hg := (hA _ hk.1).2 g hz
    intro F hF
    rw [hst, hkopf] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact ⟨hg, (hA g hg).1⟩
    · rcases List.mem_cons.mp hF with rfl | hF
      · refine ⟨hcf ▸ hk.1, ?_⟩
        rw [← hcf] at hc
        exact hc
      · exact h F (List.mem_cons_of_mem _ hF)
  · have hc := h caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · refine ⟨hf ▸ hc.1, ?_⟩
      have := hR (A caller.f) hc.2
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (by rw [hpop]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

/-- **The thread invariant on every reachable machine**, per thread `t` with
    its own function set `Z t` and features `A t`, given the closure and a
    start function in `Z t`. -/
theorem merkInvG_erreichbar (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (Z : Faden → D.Fn → Prop) (A : Faden → D.Fn → Merkmal D)
    (hA : ∀ t, MerkAbg P (Z t) (A t)) (hZ : ∀ t, Z t (init t).1) {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, MerkInvG (Z t) (A t) (M.faeden t) := by
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
      exact ⟨hZ t, (hA t _ (hZ t)).1⟩
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact merkInvG_schritt (hA t) hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Inv

#print axioms Gabbro.Grammatik.schrittMerk
#print axioms Gabbro.Grammatik.merkInvG_erreichbar

end Gabbro.Grammatik
