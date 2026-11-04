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
module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG

@[expose] public section



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
  | .onWhy _ arms => mGArms A arms
  | .call g _ _ _ => A.ruf g
  | .callInd (n := n) _ _ _ _ => A.ind n
  | .callIndElse (n := n) _ _ _ _ _ err => A.ind n && mE A err
  | .locks L _ body => A.sperre L && mB A body
  | .breaking _ body => mB A body
  | .traverse _ _ body => mB A body
  | .consumeTraverse _ _ _ _ _ _ body => mB A body
  | .retry _ _ body ueber => mB A body && mB A ueber
  | .forever _ _ body => mB A body
  | .assignSlot .. => true
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => true
  | .assignGlob .. => true
  | .putBytes .. => true
  | .assignVar .. => true
  | .shift .. => true
  | .axiomCall .. => true
  | .axiomCallElse _ _ _ _ _ _ _ _ err => mE A err
  | .regWrite .. => true
  | .transition .. => true
  | .publish .. => true
  | .advances .. => true
  | .retires .. => true
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true

def mB (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => mS A s && mB A rest
  | .bind _ rest => mB A rest
  | .bindCall g _ _ _ _ rest => A.ruf g && mB A rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => A.ind n && mB A rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => A.ind n && mE A err && mB A rest
  | .bindCallElse g _ _ _ _ err rest => A.ruf g && mE A err && mB A rest
  | .bindAxiom _ _ _ _ _ _ _ rest => mB A rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => mE A err && mB A rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => mB A rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => mE A err && mB A rest
  | .regRead _ _ rest => mB A rest
  | .regReadElse _ _ _ sonst rest => mE A sonst && mB A rest
  | .awaits _ _ _ _ _ rest => mB A rest
  | .exchange _ _ _ _ rest => mB A rest
  | .narrow _ _ _ sonst rest => mE A sonst && mB A rest
  | .narrowRequired _ _ _ rest => mB A rest
  | .check _ sonst rest => mE A sonst && mB A rest
  | .float _ _ _ _ _ rest => mB A rest
  | .floatLit _ _ _ rest => mB A rest
  | .floatOf _ _ _ rest => mB A rest
  | .floatNarrow _ _ _ sonst rest => mE A sonst && mB A rest

def mArms (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => mB A b && mArms A rest

def mGArms (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => mB A b && mGArms A rest

def mE (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => mS A s && mE A rest
  | .bind _ rest => mE A rest
  | .bindCall g _ _ _ _ rest => A.ruf g && mE A rest
  | .bindCallElse g _ _ _ _ err rest => A.ruf g && mE A err && mE A rest
  | .bindAxiom _ _ _ _ _ _ _ rest => mE A rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => mE A err && mE A rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => mE A rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => mE A err && mE A rest
  | .regRead _ _ rest => mE A rest
  | .regReadElse _ _ _ sonst rest => mE A sonst && mE A rest
  | .awaits _ _ _ _ _ rest => mE A rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => A.ind n && mE A rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => A.ind n && mE A err && mE A rest
  | .narrow _ _ _ sonst rest => mE A sonst && mE A rest
  | .narrowRequired _ _ _ rest => mE A rest
  | .exchange _ _ _ _ rest => mE A rest
  | .ite _ t e => mE A t && mE A e
  | .float _ _ _ _ _ rest => mE A rest
  | .floatLit _ _ _ rest => mE A rest
  | .floatOf _ _ _ rest => mE A rest
  | .floatNarrow _ _ _ sonst rest => mE A sonst && mE A rest
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
  | _, _, _, .verbrauch _ _ _ _ _ _ body _ k => mB A body = true ∧ k.mR A
  | _, _, _, .verbrauchRest _ _ _ _ _ _ body _ _ k => mB A body = true ∧ k.mR A
  | _, _, _, .wieder _ _ body ueber k => mB A body = true ∧ mB A ueber = true ∧ k.mR A
  | _, _, _, .wiederRest _ _ body ueber k => mB A body = true ∧ mB A ueber = true ∧ k.mR A
  | _, _, _, .ewig _ _ _ body k => mB A body = true ∧ k.mR A
  | _, _, _, .ewigRest _ _ _ body k => mB A body = true ∧ k.mR A
  | _, _, _, .wartet b k => mB A b = true ∧ k.mR A
  | _, _, _, .wartetSonst _ err b k => mE A err = true ∧ mB A b = true ∧ k.mR A
  | _, _, Λ, @GRest.abbruch _ _ _ _ _ Λk k =>
      (∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) ∧ k.mR A
  | _, _, _, .leer => True
  | _, _, _, .rueckBereit _ k => k.mR A
  | _, _, _, .zurueckgekehrt _ => True
  | _, _, _, .aufraeumen _ _ => True

/-- The callee `g` is admitted: directly, or through its signature. -/
def RufZiel (A : Merkmal D) (g : D.Fn) : Prop :=
  A.ruf g = true ∨ ∃ n, D.passt g n = true ∧ A.ind n = true

/-! ## 2. Selection and `else` blocks keep the predicate -/

section Hilfen

variable {V : Vertrag D} {l : Bool}

theorem mB_alsBlock (A : Merkmal D) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), mB A e.alsBlock.2 = mE A e
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .retScoped _ _ => rfl
  | _, _, .retWhyScoped _ _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindCallIndElse p args he hp hr err rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A t, Bool.and_comm]

  | _, _, .float op a b lo hi rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .floatLit q lo hi rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .floatOf e lo hi rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
  | _, _, .floatNarrow e lo hi sonst rest => by
      simp only [Endblock.alsBlock, mB, mE, mB_alsBlock A rest]
theorem mB_armWahlG (A : Merkmal D) {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
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

end Gabbro.Grammatik
