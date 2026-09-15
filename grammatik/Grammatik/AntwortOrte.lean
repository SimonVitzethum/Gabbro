/-
  File:      Grammatik/AntwortOrte.lean
  Subject:   THE ANSWER SITES OF A BODY, and what machine G can still reach of them
             (round-6 finding W1, 2026-09-15).

  THE FINDING (W1). `HaltArt.nieZurueck` named every axiom call or register read whose
  declared answer type is EMPTY (`AntwortLeer`): `never`, `.grund 0`, an empty range, a sum
  without a value, a pointer type no function has. Its reason in Spec's ONE list -- "the
  continuation is unreachable in the C as in G" -- is true only for an axiom `-> never`,
  whose C prototype is `_Noreturn`. For every other empty type, and for every register, the
  C call or read RETURNS and the continuation runs, covered by nothing. Probe A behind an
  axiom returning `fn(sig 5)` (no function has signature 5) met (b) and was certified.

  THE REPAIR. The checker refuses such a site (`AkzeptiertSpec.antworten`, Spec.lean; the
  Bool `antwortenB`, Zielsatz/Akzeptiert.lean): every answer site of every body is an axiom
  whose declared result is `never`, or has an answerable type (`StelleOk`). This file gives
  * `Stmt.ants` / `Block.ants` / `Endblock.ants` / `Arms.ants` / `GrundArms.ants` -- the
    answer sites of a body: `inl a` for an axiom call (`bindAxiom`, `axiomCall`), `inr r`
    for a register read (`regLies`, `regLiesElse`);
  * `StelleOk` -- the site is an axiom `-> never`, or its declared answer type is not empty;
  * `GRest.aR C` -- every block still to run in a residue has its sites in `C`, kept by every
    rule of G (`schrittAnt`, the twin of `schrittOrte`, RennfreiOrte.lean);
  * `antInvG_erreichbar` -- on every reachable machine every frame's residue has its sites
    in `C`, when every BODY has (a frame enters with its function's body, and G continues
    only with sub-blocks of it).
  With it, a thread of a reachable machine can stand at an empty answer type only at an
  axiom `-> never` (`fort_dann`, Fortschritt.lean; `KopfHalt .nieZurueck`, Spec.lean).
-/
import Grammatik.RufAdaequatG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The answer sites of a body -/

mutual

/-- The answer sites of a statement: an axiom call without a result (`axiomCall`). -/
def Stmt.ants {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Ax ⊕ D.Reg)
  | .ite _ t e => t.ants ++ e.ants
  | .onOption _ p a => p.ants ++ a.ants
  | .onTag _ arms => arms.ants
  | .onGrund _ arms => arms.ants
  | .locks _ _ body => body.ants
  | .breaking _ body => body.ants
  | .traverse _ _ body => body.ants
  | .retry _ _ body ueber => body.ants ++ ueber.ants
  | .forever _ _ body => body.ants
  | .axiomCall a .. => [.inl a]
  | _ => []

/-- The answer sites of a block: `let x = a(…)` (`inl a`), `let x = R` and
    `let x = R else …` (`inr R`). -/
def Block.ants {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (D.Ax ⊕ D.Reg)
  | .nil => []
  | .cons s rest => s.ants ++ rest.ants
  | .bind _ rest => rest.ants
  | .bindCall _ _ _ _ _ rest => rest.ants
  | .bindCallInd _ _ _ _ _ rest => rest.ants
  | .bindCallElse _ _ _ _ _ err rest => err.ants ++ rest.ants
  | .bindAxiom a _ _ _ _ _ _ rest => .inl a :: rest.ants
  | .regLies r _ rest => .inr r :: rest.ants
  | .regLiesElse r _ _ sonst rest => .inr r :: (sonst.ants ++ rest.ants)
  | .awaits _ _ _ _ rest => rest.ants
  | .exchange _ _ _ _ rest => rest.ants
  | .narrow _ _ _ sonst rest => sonst.ants ++ rest.ants
  | .pruefung _ sonst rest => sonst.ants ++ rest.ants
  | .gleit _ _ _ _ _ rest => rest.ants
  | .gleitLit _ _ _ rest => rest.ants
  | .gleitVon _ _ _ rest => rest.ants
  | .gleitNarrow _ _ _ sonst rest => sonst.ants ++ rest.ants

def Endblock.ants {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Ax ⊕ D.Reg)
  | .ret .. => []
  | .retGrund .. => []
  | .leave .. => []
  | .next .. => []
  | .cons s rest => s.ants ++ rest.ants
  | .bind _ rest => rest.ants

def Arms.ants {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → List (D.Ax ⊕ D.Reg)
  | .nil => []
  | .cons b rest => b.ants ++ rest.ants

def GrundArms.ants {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → List (D.Ax ⊕ D.Reg)
  | .nil => []
  | .cons b rest => b.ants ++ rest.ants

end

/-- **An admissible answer site** (W1): an axiom whose declared result is `never` (the C
    prototype is `_Noreturn`: the call really does not return), or a site whose declared
    answer type has a value (`¬ AntwortLeer`; decided over the program's functions by
    `antwortB`, EinpassenVoll.lean). A register read never "does not return" in C, so a
    register with an empty type is refused outright. -/
def StelleOk (D : Deklaration) : D.Ax ⊕ D.Reg → Prop
  | .inl a => D.aerg a = some .never ∨ ¬ AntwortLeer D (D.aerg a)
  | .inr r => ¬ AntwortLeer D (some (D.rtyp r))

/-- `StelleOk` as a test (classical; the checker's decision is `stelleB`). -/
noncomputable def stelleC (D : Deklaration) (x : D.Ax ⊕ D.Reg) : Bool :=
  @decide (StelleOk D x) (Classical.propDecidable _)

theorem stelleC_iff {x : D.Ax ⊕ D.Reg} : stelleC D x = true ↔ StelleOk D x := by
  unfold stelleC
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- An end block run as a block has the end block's sites. -/
theorem ants_alsBlock {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), e.alsBlock.2.ants = e.ants
  | _, _, .ret _ _ => rfl
  | _, _, .retGrund _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]

/-! ## 2. What a residue still reaches -/

/-- **Every block still to run in the residue has its answer sites in `C`.** -/
def GRest.aR (C : D.Ax ⊕ D.Reg → Bool) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.ants.all C = true
  | _, _, _, .dann b k => b.ants.all C = true ∧ k.aR C
  | _, _, _, .schrumpf k => k.aR C
  | _, _, _, .frei _ k => k.aR C
  | _, _, _, .trav _ _ body _ k => body.ants.all C = true ∧ k.aR C
  | _, _, _, .travRest _ _ body _ k => body.ants.all C = true ∧ k.aR C
  | _, _, _, .wieder _ _ body ueber k =>
      body.ants.all C = true ∧ ueber.ants.all C = true ∧ k.aR C
  | _, _, _, .wiederRest _ _ body ueber k =>
      body.ants.all C = true ∧ ueber.ants.all C = true ∧ k.aR C
  | _, _, _, .ewig _ _ _ body k => body.ants.all C = true ∧ k.aR C
  | _, _, _, .ewigRest _ _ _ body k => body.ants.all C = true ∧ k.aR C
  | _, _, _, .wartet b k => b.ants.all C = true ∧ k.aR C
  | _, _, _, .wartetSonst _ err b k => err.ants.all C = true ∧ b.ants.all C = true ∧ k.aR C
  | _, _, _, .abbruch k => k.aR C

section Wahl

variable {V : Vertrag D} {l : Bool}

theorem ants_armWahlG (C : D.Ax ⊕ D.Reg → Bool) {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.ants.all C = true → (armWahlG arms v).2.1.ants.all C = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.ants, List.all_append, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [Arms.ants, List.all_append, Bool.and_eq_true] at h
      exact ants_armWahlG C rest _ h.2

theorem ants_grundWahlG (C : D.Ax ⊕ D.Reg → Bool) {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    arms.ants.all C = true → (grundWahlG arms r).ants.all C = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [GrundArms.ants, List.all_append, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [GrundArms.ants, List.all_append, Bool.and_eq_true] at h
      exact ants_grundWahlG C rest _ h.2

end Wahl

/-! ## 3. Every rule keeps the site bound -/

set_option hygiene false in
/-- A head-local step. -/
macro "kopfAnt" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩
  dsimp only; rw [rufUpdateG_self]
  rw [‹(M.faeden f).kopf.rest = _›] at hok
  dsimp only at hok ⊢
  simp only [GRest.aR, Endblock.ants, Block.ants, Stmt.ants, ants_alsBlock,
    List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
    Bool.true_and] at hok ⊢))

set_option maxHeartbeats 4000000 in
/-- **Every rule of G, classified by what it does to the site bound** (the twin of
    `schrittOrte`): (A) a head-local step keeps the stack and the function and carries `aR`
    to the new residue; (B) a push suspends the head as a caller frame carrying `aR` and
    enters the callee's body; (C) a pop resumes the caller, whose residue carried `aR`. -/
theorem schrittAnt {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (C : D.Ax ⊕ D.Reg → Bool) (hs : RufSchrittG P O pa M f M') :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      ((M.faeden f).kopf.rest.2.2.2.2.aR C → (M'.faeden f).kopf.rest.2.2.2.2.aR C)) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      ((M.faeden f).kopf.rest.2.2.2.2.aR C → caller'.rest.2.2.2.2.aR C)) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      (caller.rest.2.2.2.2.aR C → (M'.faeden f).kopf.rest.2.2.2.2.aR C)) := by
  cases hs with
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw =>
    kopfAnt
    have h := ants_armWahlG C arms (eval σ₁ v σ₁ ρ) (by simp_all)
    rw [hw] at h
    have h2 : b.ants.all C = true := h
    simp_all
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
    kopfAnt
    have h := ants_armWahlG C arms (eval σ₁ v σ₁ ρ) (by simp_all)
    rw [hw] at h
    have h2 : b.ants.all C = true := h
    simp_all
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
    kopfAnt
    have h := ants_grundWahlG C arms (eval σ₁ r σ₁ ρ) (by simp_all)
    rw [hw] at h
    simp_all
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.aR, Endblock.ants, Stmt.ants, List.all_append, List.all_nil,
      Bool.true_and] at hok ⊢
    exact hok
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.aR, Block.ants, Stmt.ants, List.all_append, List.all_nil,
      Bool.true_and] at hok ⊢
    exact hok
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.aR, Block.ants] at hok ⊢
    exact hok
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.aR, Block.ants, List.all_append, Bool.and_eq_true] at hok ⊢
    exact ⟨hok.1.1, hok.1.2, hok.2⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.aR, Block.ants, Stmt.ants, List.all_append, List.all_nil,
      Bool.true_and] at hok ⊢
    exact hok
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.aR, Endblock.ants, Stmt.ants, List.all_append, List.all_nil,
      Bool.true_and] at hok ⊢
    exact hok
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self],
      by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    rw [hhead] at hok
    dsimp only at hok ⊢
    simp only [GRest.aR, Block.ants] at hok ⊢
    exact hok
  | rueck caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact id
  | rueckCons caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact id
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact id
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [GRest.aR] <;> exact fun h => by simp_all
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [GRest.aR] <;> exact fun h => by simp_all
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [GRest.aR] <;> exact fun h => by simp_all
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [GRest.aR, ants_alsBlock]
    exact fun h => ⟨h.1, h.2.2⟩
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [GRest.aR, ants_alsBlock]
    exact fun h => ⟨h.1, h.2.2⟩
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self], ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [GRest.aR, ants_alsBlock]
    exact fun h => ⟨h.1, h.2.2⟩
  | _ =>
    kopfAnt
    all_goals simp_all

/-! ## 4. The frame invariant -/

/-- **The site bound of a thread**: every frame's residue has its answer sites in `C`. -/
def AntInvG (C : D.Ax ⊕ D.Reg → Bool) (z : RufFadenG D) : Prop :=
  ∀ F ∈ z.kopf :: z.stapel, F.rest.2.2.2.2.aR C

section Inv

variable {P : Programm D} {O : Orakel D} {pa : Nat} {C : D.Ax ⊕ D.Reg → Bool}

theorem antInvG_schritt (hB : ∀ g, (P.rumpf g).ants.all C = true) {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M') (h : AntInvG C (M.faeden f)) :
    AntInvG C (M'.faeden f) := by
  have hk := h _ List.mem_cons_self
  rcases schrittAnt C hs with ⟨hst, hR⟩ | ⟨g, caller', rho, s0, hst, hkopf, hR⟩ |
      ⟨caller, rst, hpop, hst, hR⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hR hk
    · rw [hst] at hF
      exact h F (List.mem_cons_of_mem _ hF)
  · have hc := hR hk
    intro F hF
    rw [hst, hkopf] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hB g
    · rcases List.mem_cons.mp hF with rfl | hF
      · exact hc
      · exact h F (List.mem_cons_of_mem _ hF)
  · have hc := h caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hR hc
    · rw [hst] at hF
      exact h F (by rw [hpop]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

/-- **The site bound on every reachable machine**, when every body meets it: a frame enters
    with its function's body, and G continues only with sub-blocks of it. -/
theorem antInvG_erreichbar (hB : ∀ g, (P.rumpf g).ants.all C = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, AntInvG C (M.faeden t) := by
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
      exact hB _
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact antInvG_schritt hB hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

/-- **The head of a reachable thread, under the checker's site bound**: every block the head
    residue still runs has only admissible answer sites (`StelleOk`). -/
theorem kopf_ants (hB : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) (t : Faden) :
    (M.faeden t).kopf.rest.2.2.2.2.aR (stelleC D) :=
  antInvG_erreichbar (fun g => List.all_eq_true.mpr fun x hx => stelleC_iff.mpr (hB g x hx))
    sp init hr t _ List.mem_cons_self

end Inv

#print axioms Gabbro.Grammatik.schrittAnt
#print axioms Gabbro.Grammatik.antInvG_erreichbar
#print axioms Gabbro.Grammatik.kopf_ants

end Gabbro.Grammatik
