module

public import Grammatik.Bausteine.Kernzelle.KernAbfrage
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik

variable {D : Deklaration}

variable [DecidableEq D.Ax]

/-! ## 1. Where a body queries the core

    A foreign call carries no call-graph edge (`reachB` cannot see it: a
    foreign body is answered outside the program, and the call itself is the
    trace event `Ereignis.fremd`). So the update-to-query link is not a graph
    round but a direct syntactic fact: the core-query wrapper binds the axiom.
    The traversal below mirrors the generic feature check `mE` case by case
    (`FadenMerkmal.Teil1`), with existence instead of admission: `true` iff
    some `bindAxiom`/`bindAxiomOpt` (plain, `else`, or top-level) of exactly
    `q` occurs. -/

variable (q : D.Ax)

mutual

/-- Some statement binds the core-query axiom. -/
def bindetAxS {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => bindetAxB q t || bindetAxB q e
  | .onOption _ p a => bindetAxB q p || bindetAxB q a
  | .onTag _ arms => bindetAxArms q arms
  | .onWhy _ arms => bindetAxGArms q arms
  | .call _ _ _ _ => false
  | .callInd _ _ _ _ => false
  | .locks _ _ body => bindetAxB q body
  | .breaking _ body => bindetAxB q body
  | .traverse _ _ body => bindetAxB q body
  | .consumeTraverse _ _ _ _ _ _ body => bindetAxB q body
  | .retry _ _ body ueber => bindetAxB q body || bindetAxB q ueber
  | .forever _ _ body => bindetAxB q body
  | .assignSlot _ _ _ _ _ _ => false
  | .assignThru _ _ _ _ _ _ _ _ => false
  | .assignGlob _ _ _ _ => false
  | .putBytes _ _ _ _ _ _ _ _ _ _ => false
  | .assignVar _ _ => false
  | .shift _ _ _ _ _ _ _ _ _ _ => false
  | .axiomCall a _ _ _ _ _ _ => decide (a = q)
  | .axiomCallElse _ a _ _ _ _ _ _ err => decide (a = q) || bindetAxE q err
  | .regWrite _ _ _ => false
  | .transition _ _ _ _ _ _ _ => false
  | .publish _ _ _ _ _ _ => false
  | .advances _ _ _ _ => false
  | .retires _ _ _ _ => false
  | .ret _ _ => false
  | .retWhy _ _ => false
  | .retScoped _ _ => false
  | .retWhyScoped _ _ => false
  | .leave _ => false
  | .next _ => false
  | .assignSlotRef _ _ _ _ _ _ _ _ => false
  | .callIndElse _ _ _ _ _ err => bindetAxE q err

/-- Some block binds the core-query axiom. -/
def bindetAxB {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => false
  | .cons s rest => bindetAxS q s || bindetAxB q rest
  | .bind _ rest => bindetAxB q rest
  | .bindCall _ _ _ _ _ rest => bindetAxB q rest
  | .bindCallInd _ _ _ _ _ rest => bindetAxB q rest
  | .bindCallIndElse _ _ _ _ _ err rest =>
      bindetAxE q err || bindetAxB q rest
  | .bindCallElse _ _ _ _ _ err rest => bindetAxE q err || bindetAxB q rest
  | .bindAxiom a _ _ _ _ _ _ rest => decide (a = q) || bindetAxB q rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxB q rest
  | .bindAxiomOpt _ a _ _ _ _ _ rest => decide (a = q) || bindetAxB q rest
  | .bindAxiomOptElse _ a _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxB q rest
  | .regRead _ _ rest => bindetAxB q rest
  | .regReadElse _ _ _ sonst rest => bindetAxE q sonst || bindetAxB q rest
  | .awaits _ _ _ _ _ rest => bindetAxB q rest
  | .exchange _ _ _ _ rest => bindetAxB q rest
  | .narrow _ _ _ sonst rest => bindetAxE q sonst || bindetAxB q rest
  | .narrowRequired _ _ _ rest => bindetAxB q rest
  | .check _ sonst rest => bindetAxE q sonst || bindetAxB q rest
  | .float _ _ _ _ rest => bindetAxB q rest
  | .floatLit _ _ rest => bindetAxB q rest
  | .floatOf _ _ rest => bindetAxB q rest
  | .floatNarrow _ _ _ sonst rest => bindetAxE q sonst || bindetAxB q rest

/-- Some tagged arm binds the core-query axiom. -/
def bindetAxArms {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => false
  | .cons b rest => bindetAxB q b || bindetAxArms q rest

/-- Some reason arm binds the core-query axiom. -/
def bindetAxGArms {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => false
  | .cons b rest => bindetAxB q b || bindetAxGArms q rest

/-- Some top-level body binds the core-query axiom. -/
def bindetAxE {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret _ _ => false
  | .retWhy _ _ => false
  | .retScoped _ _ => false
  | .retWhyScoped _ _ => false
  | .leave _ => false
  | .next _ => false
  | .cons s rest => bindetAxS q s || bindetAxE q rest
  | .bind _ rest => bindetAxE q rest
  | .bindCall _ _ _ _ _ rest => bindetAxE q rest
  | .bindCallElse _ _ _ _ _ err rest => bindetAxE q err || bindetAxE q rest
  | .bindAxiom a _ _ _ _ _ _ rest => decide (a = q) || bindetAxE q rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxE q rest
  | .bindAxiomOpt _ a _ _ _ _ _ rest => decide (a = q) || bindetAxE q rest
  | .bindAxiomOptElse _ a _ _ _ _ _ _ err rest =>
      decide (a = q) || bindetAxE q err || bindetAxE q rest
  | .regRead _ _ rest => bindetAxE q rest
  | .regReadElse _ _ _ sonst rest => bindetAxE q sonst || bindetAxE q rest
  | .awaits _ _ _ _ _ rest => bindetAxE q rest
  | .bindCallInd _ _ _ _ _ rest => bindetAxE q rest
  | .bindCallIndElse _ _ _ _ _ err rest => bindetAxE q err || bindetAxE q rest
  | .narrow _ _ _ sonst rest => bindetAxE q sonst || bindetAxE q rest
  | .narrowRequired _ _ _ rest => bindetAxE q rest
  | .exchange _ _ _ rest => bindetAxE q rest
  | .ite _ t e => bindetAxE q t || bindetAxE q e

end

/-! ## 2. The connected query

    The wrapper (`a.kernAbfrage`, already admitted by `akkuZulaessig` with
    its exact shape and the update's call edge) binds the hardware axiom
    through the C08 foreign-call path. Together with the shape and the
    provenance, this is the checked core identity: the update's queried core
    is the running core under the declared assignment, with no unproved
    hardware assumption beyond the named `AxVertragO` ensures on the answer. -/

/-- **The connected core query**: the shape, the hardware provenance and the
    wrapper's foreign bind. -/
def KernAbfrageVerbunden (P : Programm D) (a : AccumulatorDecl D) (q : D.Ax) : Prop :=
  KernAbfrageGestalt D q a.kernZahl ∧ KernAbfrageHerkunft D q ∧
    bindetAxE q (P.rumpf a.kernAbfrage) = true

/-- The connected query, decided over the member lists. -/
def kernAbfrageEinzelB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob)
    (a : AccumulatorDecl D) (q : D.Ax) : Bool :=
  kernAbfrageGestaltB D q a.kernZahl tabs globs &&
  kernAbfrageHerkunftB D q &&
  bindetAxE q (P.rumpf a.kernAbfrage)

/-- The Bool decides the connected query. -/
theorem kernAbfrageEinzelB_iff {P : Programm D} {tabs : List D.Tab}
    {globs : List D.Glob} {a : AccumulatorDecl D} {q : D.Ax}
    (hT : ∀ t : D.Tab, t ∈ tabs) (hG : ∀ g : D.Glob, g ∈ globs) :
    kernAbfrageEinzelB P tabs globs a q = true ↔ KernAbfrageVerbunden P a q := by
  unfold kernAbfrageEinzelB KernAbfrageVerbunden
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(kernAbfrageGestaltB_iff hT hG).mp h1,
      (kernAbfrageHerkunftB_iff).mp h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(kernAbfrageGestaltB_iff hT hG).mpr h1,
      (kernAbfrageHerkunftB_iff).mpr h2, h3⟩

#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrageEinzelB_iff

end Gabbro.Grammatik.Kernzelle
