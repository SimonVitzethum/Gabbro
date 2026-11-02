/-
  File:      Grammatik/AntwortOrte.lean
  Subject:   THE ANSWER SITES OF A BODY, and what machine G can still reach of them
             (round-6 finding W1, 2026-09-15).

  THE FINDING (W1). `HaltArt.nieZurueck` named every axiom call or register read whose
  declared answer type is EMPTY (`AntwortLeer`): `never`, `.why 0`, an empty range, a sum
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
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
@[expose] public section


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
  | .onWhy _ arms => arms.ants
  | .locks _ _ body => body.ants
  | .breaking _ body => body.ants
  | .traverse _ _ body => body.ants
  | .consumeTraverse _ _ _ _ _ _ body => body.ants
  | .retry _ _ body ueber => body.ants ++ ueber.ants
  | .forever _ _ body => body.ants
  | .axiomCall a .. => [.inl a]
  | .axiomCallElse a _ _ _ _ _ _ _ err => .inl a :: err.ants
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
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => .inl a :: (err.ants ++ rest.ants)
  | .bindAxiomOpt a _ _ _ _ _ _ rest => .inl a :: rest.ants
  | .bindAxiomOptElse a _ _ _ _ _ _ _ err rest => .inl a :: (err.ants ++ rest.ants)
  | .regRead r _ rest => .inr r :: rest.ants
  | .regReadElse r _ _ sonst rest => .inr r :: (sonst.ants ++ rest.ants)
  | .awaits _ _ _ _ _ rest => rest.ants
  | .exchange _ _ _ _ rest => rest.ants
  | .narrow _ _ _ sonst rest => sonst.ants ++ rest.ants
  | .narrowRequired _ _ _ rest => rest.ants
  | .check _ sonst rest => sonst.ants ++ rest.ants
  | .float _ _ _ _ _ rest => rest.ants
  | .floatLit _ _ _ rest => rest.ants
  | .floatOf _ _ _ rest => rest.ants
  | .floatNarrow _ _ _ sonst rest => sonst.ants ++ rest.ants

def Endblock.ants {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Ax ⊕ D.Reg)
  | .ret .. => []
  | .retWhy .. => []
  | .retScoped .. => []
  | .retWhyScoped .. => []
  | .leave .. => []
  | .next .. => []
  | .cons s rest => s.ants ++ rest.ants
  | .bind _ rest => rest.ants
  | .bindCall _ _ _ _ _ rest => rest.ants
  | .bindCallElse _ _ _ _ _ err rest => err.ants ++ rest.ants
  | .bindAxiom a _ _ _ _ _ _ rest => .inl a :: rest.ants
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => .inl a :: (err.ants ++ rest.ants)
  | .bindAxiomOpt a _ _ _ _ _ _ rest => .inl a :: rest.ants
  | .bindAxiomOptElse a _ _ _ _ _ _ _ err rest => .inl a :: (err.ants ++ rest.ants)
  | .regRead r _ rest => .inr r :: rest.ants
  | .regReadElse r _ _ sonst rest => .inr r :: (sonst.ants ++ rest.ants)
  | .awaits g _ _ _ _ rest => rest.ants
  | .bindCallInd _ _ _ _ _ rest => rest.ants
  | .narrow _ _ _ sonst rest => sonst.ants ++ rest.ants
  | .narrowRequired _ _ _ rest => rest.ants
  | .exchange _ _ _ _ rest => rest.ants
  | .ite _ t e => e.ants ++ t.ants

def Arms.ants {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → List (D.Ax ⊕ D.Reg)
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
  | _, _, .retWhy _ _ => rfl
  | _, _, .retScoped _ _ => rfl
  | _, _, .retWhyScoped _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bindAxiom a _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bindCallElse a _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bindAxiomElse a _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bindAxiomOpt a _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bindAxiomOptElse a _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.ants, Endblock.ants, ants_alsBlock t]

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
  | _, _, _, .leer => True

section Wahl

variable {V : Vertrag D} {l : Bool}

theorem ants_armWahlG (C : D.Ax ⊕ D.Reg → Bool) {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
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


end Gabbro.Grammatik
