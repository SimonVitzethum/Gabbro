/-
  File:      Grammatik/Gen/Abdeckung/Satz/MerkmalUnd.lean
  Subject:   `mE` is a conjunction over the sites of a body: two feature sets, the trivial one, finite lists
             (part of step 1, `ZellenSatz.lean`).
-/
import Grammatik.Gen.Abdeckung.Zellen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-! ## `mE` is a conjunction over the sites of a body -/

/-- The conjunction of two feature sets. -/
def _root_.Gabbro.Grammatik.Merkmal.und (A B : Merkmal D) : Merkmal D :=
  ⟨fun g => A.ruf g && B.ruf g, fun n => A.ind n && B.ind n, fun L => A.sperre L && B.sperre L⟩

@[simp] theorem Merkmal.und_ruf (A B : Merkmal D) (g : D.Fn) : (A.und B).ruf g = (A.ruf g && B.ruf g) := rfl
@[simp] theorem Merkmal.und_ind (A B : Merkmal D) (n : Nat) : (A.und B).ind n = (A.ind n && B.ind n) := rfl
@[simp] theorem Merkmal.und_sperre (A B : Merkmal D) (L : D.Lock) :
    (A.und B).sperre L = (A.sperre L && B.sperre L) := rfl

mutual

theorem mS_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → mS (A.und B) s = (mS A s && mS B s)
  | .ite _ t e => by
      simp only [mS, mB_und A B t, mB_und A B e, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .onOption _ p a => by
      simp only [mS, mB_und A B p, mB_und A B a, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .onTag _ arms => by simp only [mS, mArms_und A B arms]
  | .onWhy _ arms => by simp only [mS, mGArms_und A B arms]
  | .call .. => by simp only [mS, Merkmal.und_ruf]
  | .callInd .. => by simp only [mS, Merkmal.und_ind]
  | .locks L _ body => by
      simp only [mS, mB_und A B body, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .breaking _ body => by simp only [mS, mB_und A B body]
  | .traverse _ _ body => by simp only [mS, mB_und A B body]
  | .retry _ _ body ueber => by
      simp only [mS, mB_und A B body, mB_und A B ueber, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .forever _ _ body => by simp only [mS, mB_und A B body]
  | .assignSlot .. => rfl
  | .assignThru .. => rfl
  | .assignGlob .. => rfl
  | .putBytes .. => rfl
  | .assignVar .. => rfl
  | .shift .. => rfl
  | .axiomCall .. => rfl
  | .regWrite .. => rfl
  | .transition .. => rfl
  | .publish .. => rfl
  | .advances .. => rfl
  | .retires .. => rfl
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl

theorem mB_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → mB (A.und B) b = (mB A b && mB B b)
  | .nil => rfl
  | .cons s rest => by
      simp only [mB, mS_und A B s, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bind _ rest => by simp only [mB, mB_und A B rest]
  | .bindCall g _ _ _ _ rest => by
      simp only [mB, mB_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindCallInd _ _ _ _ _ rest => by
      simp only [mB, mB_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindCallElse g _ _ _ _ err rest => by
      simp only [mB, mE_und A B err, mB_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [mB, mE_und A B err, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .regRead _ _ rest => by simp only [mB, mB_und A B rest]
  | .regReadElse _ _ _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .awaits _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .exchange _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .narrow _ _ _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .check _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .float _ _ _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .floatLit _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .floatOf _ _ _ rest => by simp only [mB, mB_und A B rest]
  | .floatNarrow _ _ _ sonst rest => by
      simp only [mB, mE_und A B sonst, mB_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem mArms_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : (a : Arms D V l Γ Λ Λ' cs) → mArms (A.und B) a = (mArms A a && mArms B a)
  | .nil => rfl
  | .cons b rest => by
      simp only [mArms, mB_und A B b, mArms_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem mGArms_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → mGArms (A.und B) a = (mGArms A a && mGArms B a)
  | .nil => rfl
  | .cons b rest => by
      simp only [mGArms, mB_und A B b, mGArms_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem mE_und (A B : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → mE (A.und B) e = (mE A e && mE B e)
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl
  | .cons s rest => by
      simp only [mE, mS_und A B s, mE_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bind _ rest => by simp only [mE, mE_und A B rest]
  | .bindCall g _ _ _ _ rest => by
      simp only [mE, mE_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindCallElse g _ _ _ _ err rest => by
      simp only [mE, mE_und A B err, mE_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mE, mE_und A B rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [mE, mE_und A B err, mE_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .regRead _ _ rest => by simp only [mE, mE_und A B rest]
  | .regReadElse _ _ _ sonst rest => by
      simp only [mE, mE_und A B sonst, mE_und A B rest, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | .awaits _ _ _ _ rest => by simp only [mE, mE_und A B rest]
  | .bindCallInd _ _ _ _ _ rest => by
      simp only [mE, mE_und A B rest, Merkmal.und_ruf, Merkmal.und_ind, Merkmal.und_sperre, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

end

/-! ## The trivial feature set, finite conjunctions -/

/-- The feature set that admits everything. -/
def _root_.Gabbro.Grammatik.Merkmal.top : Merkmal D := ⟨fun _ => true, fun _ => true, fun _ => true⟩

mutual

theorem mS_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → mS Merkmal.top s = true
  | .ite _ t e => by simp only [mS, mB_top t, mB_top e, Bool.and_self]
  | .onOption _ p a => by simp only [mS, mB_top p, mB_top a, Bool.and_self]
  | .onTag _ arms => by simp only [mS, mArms_top arms]
  | .onWhy _ arms => by simp only [mS, mGArms_top arms]
  | .call .. => rfl
  | .callInd .. => rfl
  | .locks _ _ body => by simp only [mS, mB_top body]; rfl
  | .breaking _ body => by simp only [mS, mB_top body]
  | .traverse _ _ body => by simp only [mS, mB_top body]
  | .retry _ _ body ueber => by simp only [mS, mB_top body, mB_top ueber, Bool.and_self]
  | .forever _ _ body => by simp only [mS, mB_top body]
  | .assignSlot .. => rfl
  | .assignThru .. => rfl
  | .assignGlob .. => rfl
  | .putBytes .. => rfl
  | .assignVar .. => rfl
  | .shift .. => rfl
  | .axiomCall .. => rfl
  | .regWrite .. => rfl
  | .transition .. => rfl
  | .publish .. => rfl
  | .advances .. => rfl
  | .retires .. => rfl
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl

theorem mB_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → mB Merkmal.top b = true
  | .nil => rfl
  | .cons s rest => by simp only [mB, mS_top s, mB_top rest, Bool.and_self]
  | .bind _ rest => by simp only [mB, mB_top rest]
  | .bindCall _ _ _ _ _ rest => by simp only [mB, mB_top rest]; rfl
  | .bindCallInd _ _ _ _ _ rest => by simp only [mB, mB_top rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [mB, mE_top err, mB_top rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [mB, mE_top err, mB_top rest, Bool.and_self]
  | .regRead _ _ rest => by simp only [mB, mB_top rest]
  | .regReadElse _ _ _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]
  | .awaits _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .exchange _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .narrow _ _ _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]
  | .check _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]
  | .float _ _ _ _ _ rest => by simp only [mB, mB_top rest]
  | .floatLit _ _ _ rest => by simp only [mB, mB_top rest]
  | .floatOf _ _ _ rest => by simp only [mB, mB_top rest]
  | .floatNarrow _ _ _ sonst rest => by simp only [mB, mE_top sonst, mB_top rest, Bool.and_self]

theorem mArms_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → mArms Merkmal.top a = true
  | .nil => rfl
  | .cons b rest => by simp only [mArms, mB_top b, mArms_top rest, Bool.and_self]

theorem mGArms_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → mGArms Merkmal.top a = true
  | .nil => rfl
  | .cons b rest => by simp only [mGArms, mB_top b, mGArms_top rest, Bool.and_self]

theorem mE_top {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → mE Merkmal.top e = true
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl
  | .cons s rest => by simp only [mE, mS_top s, mE_top rest, Bool.and_self]
  | .bind _ rest => by simp only [mE, mE_top rest]
  | .bindCall _ _ _ _ _ rest => by simp only [mE, mE_top rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [mE, mE_top err, mE_top rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [mE, mE_top rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [mE, mE_top err, mE_top rest, Bool.and_self]
  | .regRead _ _ rest => by simp only [mE, mE_top rest]
  | .regReadElse _ _ _ sonst rest => by simp only [mE, mE_top sonst, mE_top rest, Bool.and_self]
  | .awaits _ _ _ _ rest => by simp only [mE, mE_top rest]
  | .bindCallInd _ _ _ _ _ rest => by simp only [mE, mE_top rest]; rfl

end

/-- The conjunction of a list of feature sets. -/
def _root_.Gabbro.Grammatik.Merkmal.alle (As : List (Merkmal D)) : Merkmal D := As.foldr Merkmal.und Merkmal.top

theorem mE_alle (As : List (Merkmal D)) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) : mE (Merkmal.alle As) e = As.all fun A => mE A e := by
  induction As with
  | nil => exact mE_top e
  | cons A rest ih =>
    show mE (A.und (Merkmal.alle rest)) e = _
    rw [mE_und, ih]
    rfl

theorem Merkmal.gleich {A B : Merkmal D} (h1 : ∀ g, A.ruf g = B.ruf g) (h2 : ∀ n, A.ind n = B.ind n)
    (h3 : ∀ L, A.sperre L = B.sperre L) : A = B := by
  cases A; cases B
  simp only [Merkmal.mk.injEq]
  exact ⟨funext h1, funext h2, funext h3⟩

theorem alle_ruf (As : List (Merkmal D)) (g : D.Fn) : (Merkmal.alle As).ruf g = As.all fun A => A.ruf g := by
  induction As with
  | nil => rfl
  | cons A rest ih => show (A.ruf g && (Merkmal.alle rest).ruf g) = _; rw [ih]; rfl

theorem alle_ind (As : List (Merkmal D)) (n : Nat) : (Merkmal.alle As).ind n = As.all fun A => A.ind n := by
  induction As with
  | nil => rfl
  | cons A rest ih => show (A.ind n && (Merkmal.alle rest).ind n) = _; rw [ih]; rfl

theorem alle_sperre (As : List (Merkmal D)) (L : D.Lock) :
    (Merkmal.alle As).sperre L = As.all fun A => A.sperre L := by
  induction As with
  | nil => rfl
  | cons A rest ih => show (A.sperre L && (Merkmal.alle rest).sperre L) = _; rw [ih]; rfl

end Gabbro.Grammatik.Gen
