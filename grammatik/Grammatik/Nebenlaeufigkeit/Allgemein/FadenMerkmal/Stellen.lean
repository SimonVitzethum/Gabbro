/-
  The call sites of a body, as a list.

  `mS`/`mB`/`mE` fold a feature set over a body: every direct callee, every signature of an
  indirect call and every lock of a `locks` block is admitted. Each question about one callee
  walks the body again. `stellenE` collects the same sites once; the fold is `all` over that
  list (`mE_stellen`), so a caller can keep the list and answer every question from it.
-/
module
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Teil1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- One site a feature set judges: a direct callee, the signature of an indirect call, a lock. -/
inductive Stelle (D : Deklaration) where
  | ruf : D.Fn → Stelle D
  | ind : Nat → Stelle D
  | sperre : D.Lock → Stelle D

/-- The verdict of a feature set on one site. -/
def Merkmal.an (A : Merkmal D) : Stelle D → Bool
  | .ruf g => A.ruf g
  | .ind n => A.ind n
  | .sperre L => A.sperre L

mutual
def stellenS {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → List (Stelle D)
  | .ite _ t e => stellenB t ++ stellenB e
  | .onOption _ p a => stellenB p ++ stellenB a
  | .onTag _ arms => stellenArms arms
  | .onWhy _ arms => stellenGArms arms
  | .call g _ _ _ => [Stelle.ruf g]
  | .callInd (n := n) _ _ _ _ => [Stelle.ind n]
  | .callIndElse (n := n) _ _ _ _ _ err => [Stelle.ind n] ++ stellenE err
  | .locks L _ body => [Stelle.sperre L] ++ stellenB body
  | .breaking _ body => stellenB body
  | .traverse _ _ body => stellenB body
  | .consumeTraverse _ _ _ _ _ _ body => stellenB body
  | .retry _ _ body ueber => stellenB body ++ stellenB ueber
  | .forever _ _ body => stellenB body
  | .assignSlot .. => []
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => []
  | .assignGlob .. => []
  | .putBytes .. => []
  | .assignVar .. => []
  | .shift .. => []
  | .axiomCall .. => []
  | .axiomCallElse _ _ _ _ _ _ _ _ err => stellenE err
  | .regWrite .. => []
  | .transition .. => []
  | .publish .. => []
  | .advances .. => []
  | .retires .. => []
  | .ret .. => []
  | .retWhy .. => []
  | .retScoped .. => []
  | .retWhyScoped .. => []
  | .leave _ => []
  | .next _ => []

def stellenB {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → List (Stelle D)
  | .nil => []
  | .cons s rest => stellenS s ++ stellenB rest
  | .bind _ rest => stellenB rest
  | .bindCall g _ _ _ _ rest => [Stelle.ruf g] ++ stellenB rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => [Stelle.ind n] ++ stellenB rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => [Stelle.ind n] ++ stellenE err ++ stellenB rest
  | .bindCallElse g _ _ _ _ err rest => [Stelle.ruf g] ++ stellenE err ++ stellenB rest
  | .bindAxiom _ _ _ _ _ _ _ rest => stellenB rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => stellenE err ++ stellenB rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => stellenB rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => stellenE err ++ stellenB rest
  | .regRead _ _ rest => stellenB rest
  | .regReadElse _ _ _ sonst rest => stellenE sonst ++ stellenB rest
  | .awaits _ _ _ _ _ rest => stellenB rest
  | .exchange _ _ _ _ rest => stellenB rest
  | .narrow _ _ _ sonst rest => stellenE sonst ++ stellenB rest
  | .narrowRequired _ _ _ rest => stellenB rest
  | .check _ sonst rest => stellenE sonst ++ stellenB rest
  | .float _ _ _ _ _ rest => stellenB rest
  | .floatLit _ _ _ rest => stellenB rest
  | .floatOf _ _ _ rest => stellenB rest
  | .floatNarrow _ _ _ sonst rest => stellenE sonst ++ stellenB rest

def stellenArms {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → List (Stelle D)
  | .nil => []
  | .cons b rest => stellenB b ++ stellenArms rest

def stellenGArms {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → List (Stelle D)
  | .nil => []
  | .cons b rest => stellenB b ++ stellenGArms rest

def stellenE {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → List (Stelle D)
  | .ret .. => []
  | .retWhy .. => []
  | .retScoped .. => []
  | .retWhyScoped .. => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stellenS s ++ stellenE rest
  | .bind _ rest => stellenE rest
  | .bindCall g _ _ _ _ rest => [Stelle.ruf g] ++ stellenE rest
  | .bindCallElse g _ _ _ _ err rest => [Stelle.ruf g] ++ stellenE err ++ stellenE rest
  | .bindAxiom _ _ _ _ _ _ _ rest => stellenE rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => stellenE err ++ stellenE rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => stellenE rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => stellenE err ++ stellenE rest
  | .regRead _ _ rest => stellenE rest
  | .regReadElse _ _ _ sonst rest => stellenE sonst ++ stellenE rest
  | .awaits _ _ _ _ _ rest => stellenE rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => [Stelle.ind n] ++ stellenE rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => [Stelle.ind n] ++ stellenE err ++ stellenE rest
  | .narrow _ _ _ sonst rest => stellenE sonst ++ stellenE rest
  | .narrowRequired _ _ _ rest => stellenE rest
  | .exchange _ _ _ _ rest => stellenE rest
  | .ite _ t e => stellenE t ++ stellenE e
  | .float _ _ _ _ _ rest => stellenE rest
  | .floatLit _ _ _ rest => stellenE rest
  | .floatOf _ _ _ rest => stellenE rest
  | .floatNarrow _ _ _ sonst rest => stellenE sonst ++ stellenE rest

end

mutual
theorem mS_stellen (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (x : Stmt D V l Γ Λ Λ') → mS A x = (stellenS x).all A.an
  | .ite _ t e => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A t, mB_stellen A e]
  | .onOption _ p a => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A p, mB_stellen A a]
  | .onTag _ arms => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mArms_stellen A arms]
  | .onWhy _ arms => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mGArms_stellen A arms]
  | .call g _ _ _ => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .callInd (n := n) _ _ _ _ => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .callIndElse (n := n) _ _ _ _ _ err => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err]
  | .locks L _ body => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A body]
  | .breaking _ body => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A body]
  | .traverse _ _ body => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A body]
  | .consumeTraverse _ _ _ _ _ _ body => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A body]
  | .retry _ _ body ueber => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A body, mB_stellen A ueber]
  | .forever _ _ body => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A body]
  | .assignSlot .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .assignGlob .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .putBytes .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .assignVar .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .shift .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .axiomCall .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .axiomCallElse _ _ _ _ _ _ _ _ err => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err]
  | .regWrite .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .transition .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .publish .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .advances .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .retires .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .ret .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .retWhy .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .retScoped .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .retWhyScoped .. => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .leave _ => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .next _ => by
    simp only [mS, stellenS, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]

theorem mB_stellen (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (x : Block D V l Γ Λ Λ') → mB A x = (stellenB x).all A.an
  | .nil => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .cons s rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mS_stellen A s, mB_stellen A rest]
  | .bind _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .bindCall g _ _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .bindCallInd (n := n) _ _ _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mB_stellen A rest]
  | .bindCallElse g _ _ _ _ err rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mB_stellen A rest]
  | .bindAxiom _ _ _ _ _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mB_stellen A rest]
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mB_stellen A rest]
  | .regRead _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .regReadElse _ _ _ sonst rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A sonst, mB_stellen A rest]
  | .awaits _ _ _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .exchange _ _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .narrow _ _ _ sonst rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A sonst, mB_stellen A rest]
  | .narrowRequired _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .check _ sonst rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A sonst, mB_stellen A rest]
  | .float _ _ _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .floatLit _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .floatOf _ _ _ rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A rest]
  | .floatNarrow _ _ _ sonst rest => by
    simp only [mB, stellenB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A sonst, mB_stellen A rest]

theorem mArms_stellen (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    (x : Arms D V l Γ Λ Λ' cs) → mArms A x = (stellenArms x).all A.an
  | .nil => by
    simp only [mArms, stellenArms, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .cons b rest => by
    simp only [mArms, stellenArms, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A b, mArms_stellen A rest]

theorem mGArms_stellen (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    (x : GrundArms D V l Γ Λ Λ' n) → mGArms A x = (stellenGArms x).all A.an
  | .nil => by
    simp only [mGArms, stellenGArms, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .cons b rest => by
    simp only [mGArms, stellenGArms, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mB_stellen A b, mGArms_stellen A rest]

theorem mE_stellen (A : Merkmal D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} :
    (x : Endblock D V l Γ Λ) → mE A x = (stellenE x).all A.an
  | .ret .. => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .retWhy .. => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .retScoped .. => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .retWhyScoped .. => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .leave _ => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .next _ => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an]
  | .cons s rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mS_stellen A s, mE_stellen A rest]
  | .bind _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .bindCall g _ _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .bindCallElse g _ _ _ _ err rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mE_stellen A rest]
  | .bindAxiom _ _ _ _ _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mE_stellen A rest]
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mE_stellen A rest]
  | .regRead _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .regReadElse _ _ _ sonst rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A sonst, mE_stellen A rest]
  | .awaits _ _ _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .bindCallInd (n := n) _ _ _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A err, mE_stellen A rest]
  | .narrow _ _ _ sonst rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A sonst, mE_stellen A rest]
  | .narrowRequired _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .exchange _ _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .ite _ t e => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A t, mE_stellen A e]
  | .float _ _ _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .floatLit _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .floatOf _ _ _ rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A rest]
  | .floatNarrow _ _ _ sonst rest => by
    simp only [mE, stellenE, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc,
      Merkmal.an, mE_stellen A sonst, mE_stellen A rest]

end

end Gabbro.Grammatik
