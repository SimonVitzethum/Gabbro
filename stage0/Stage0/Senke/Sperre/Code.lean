/-
  File:      stage0/Stage0/Senke/Sperre/Code.lean
  Subject:   Building blocks of the lock code (`Ticket/Code.lean`): `addC` adds to a word by `cas`, again until it
             holds; `futexC` builds the request block of a `futex` call and makes it. And which statements and blocks
             have no `ret` or `retWhy` (`retFreiS`, `retFreiB`), the condition of the body of a `locks`.
-/
module
public import Stage0.Senke.Ausdruck
public import Stage0.Senke.Stopp
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- `w := w + d` for the word at `a` by `cas`, again until it holds (scratch from `u`): 7 instructions. -/
def addC (a u : Nat) (d : Int) : List II :=
  [ci 1 u a 0, ci 15 ((u + 1 : Nat) : Int) u 0, ci 1 ((u + 3 : Nat) : Int) d 0,
    ci 3 ((u + 2 : Nat) : Int) ((u + 1 : Nat) : Int) ((u + 3 : Nat) : Int),
    ci 22 ((u + 4 : Nat) : Int) u ((u + 1 : Nat) : Int),
    ci 14 ((u + 4 : Nat) : Int) ((u + 4 : Nat) : Int) ((u + 1 : Nat) : Int),
    ci 19 ((u + 4 : Nat) : Int) (-96) 0]

/-- `futex (a, op, v)` with `v` from slot `v`, the request block from `q`: 8 instructions. -/
def futexC (a op : Nat) (v q : Nat) (vConst : Option Int) : List II :=
  [ci 1 q 202 0, ci 1 ((q + 1 : Nat) : Int) a 0, ci 1 ((q + 2 : Nat) : Int) op 0,
    (match vConst with
     | some k => ci 1 ((q + 3 : Nat) : Int) k 0
     | none => ci 2 ((q + 3 : Nat) : Int) v 0),
    ci 1 ((q + 4 : Nat) : Int) 0 0, ci 1 ((q + 5 : Nat) : Int) 0 0, ci 1 ((q + 6 : Nat) : Int) 0 0,
    ci 23 ((q + 7 : Nat) : Int) q 0]

variable {V : Vertrag D}

mutual
/-- A statement without `ret` or `retWhy`, among the forms the lowering takes (every other form: `false`). -/
def retFreiS : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' → Bool
  | _, _, _, _, .assignVar .. | _, _, _, _, .assignGlob .. | _, _, _, _, .assignSlot ..
  | _, _, _, _, .putBytes .. | _, _, _, _, .shift .. | _, _, _, _, .assignThru .. | _, _, _, _, .assignThruOwn .. | _, _, _, _, .call .. | _, _, _, _, .callInd .. | _, _, _, _, .advances .. | _, _, _, _, .retires ..
  | _, _, _, _, .leave _ | _, _, _, _, .next _ | _, _, _, _, .axiomCall .. | _, _, _, _, .publish .. => true
  | _, _, _, _, .ite _ t e => retFreiB t && retFreiB e
  | _, _, _, _, .onOption _ p a => retFreiB p && retFreiB a
  | _, _, _, _, .onTag _ arms => retFreiArms arms
  | _, _, _, _, .onWhy _ arms => retFreiGrundArms arms
  | _, _, _, _, .traverse _ _ b => retFreiB b
  | _, _, _, _, .breaking _ b => retFreiB b
  | _, _, _, _, .locks _ _ b => retFreiB b
  | _, _, _, _, .axiomCallElse .. => false
  | _, _, _, _, .callIndElse .. => false
  | _, _, _, _, .consumeTraverse .. => false
  | _, _, _, _, .retScoped .. => false
  | _, _, _, _, .retWhyScoped .. => false
  | _, _, _, _, .retry .. | _, _, _, _, .forever ..
  | _, _, _, _, .regWrite .. | _, _, _, _, .transition ..
  | _, _, _, _, .ret .. | _, _, _, _, .retWhy ..
  | _, _, _, _, .assignSlotRef .. => false

def retFreiB : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → Bool
  | _, _, _, _, .nil => true
  | _, _, _, _, .cons s r => retFreiS s && retFreiB r
  | _, _, _, _, .bind _ r => retFreiB r
  | _, _, _, _, .floatLit _ _ _ r | _, _, _, _, .floatOf _ _ _ r => retFreiB r
  | _, _, _, _, .bindCall _ _ _ _ _ r | _, _, _, _, .bindCallInd _ _ _ _ _ r => retFreiB r
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ r => retFreiB r
  | _, _, _, _, .bindAxiomOpt (e := some τ) _ _ _ _ _ _ r => retFreiB r
  | _, _, _, _, .awaits _ _ _ _ _ r => retFreiB r
  | _, _, _, _, .exchange _ _ _ _ r => retFreiB r
  | _, _, _, _, .bindAxiomOpt (e := none) .. | _, _, _, _, .bindAxiomOptElse .. => false
  | _, _, _, _, .bindCallIndElse .. => false
  | _, _, _, _, .bindCallElse .. | _, _, _, _, .bindAxiomElse ..
  | _, _, _, _, .regRead .. | _, _, _, _, .regReadElse ..
  | _, _, _, _, .narrow .. | _, _, _, _, .check ..
  | _, _, _, _, .float .. | _, _, _, _, .floatNarrow ..
  | _, _, _, _, .narrowRequired .. => false
def retFreiArms : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option Ty)} →
    Arms D V l Γ Λ Λ' cs → Bool
  | _, _, _, _, _, .nil => true
  | _, _, _, _, _, .cons b rest => retFreiB b && retFreiArms rest
def retFreiGrundArms : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {k : Nat} →
    GrundArms D V l Γ Λ Λ' k → Bool
  | _, _, _, _, _, .nil => true
  | _, _, _, _, _, .cons b rest => retFreiB b && retFreiGrundArms rest

end

end Gabbro.Stage0.Senke
