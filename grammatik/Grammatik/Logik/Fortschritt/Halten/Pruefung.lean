/-
  File:      Grammatik/Logik/Fortschritt/Halten/Pruefung.lean
  Subject:   THE HOLD-BOUND CHECK OF THE MODEL (K002), as a Bool over the syntax: every `locks L` section
             costs at most the bound of `L` in `kostenBlock` (machine-G steps, each call counted at its
             callee's declared cost) and calls only callees with a declared cost. The walker `haltS` ...
             `haltE` moved here from `Parser/Elab/Export/HeldBinding.lean` (the exporter keeps using it),
             so that the goal statement can name it.

  * The walker takes the return-predicate price `ep` of the function whose body it walks (C05): a
    value `return` inside a section is priced with `ep` there, exactly as `kostenBlock ep` prices it in
    the frame potential, so the epilogue of a return taken while `L` is held is part of `N L`.
  * `haltPasst` -- K001 (`kostenPasst`: every function of `ks` fits its declared cost, epilogue included)
    and K002 (every section in every function `g` of `fs` fits the bound `N` of its lock at
    `ep = kostenEpilog P g`, calling only functions of `ks`).
  * `haltSchranke ls N L = N L + 1 + ls.length` -- the hold time the checked bound gives in G steps
    (`haltezeit_aus`, Halten/Haltezeit.lean): the section body with the epilogue of a return inside it
    (`N L`), the release (`1`), and, when the section is left by a scoped `return`, the releases of the
    frame's outer locks before `L` (at most one per lock of `ls`).
-/
module
public import Grammatik.Logik.Fortschritt.KostenG.T3Basis
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/- `haltS h ep c Z pa s`: every `locks L` section in `s` whose lock has a bound `h L` costs at most the
   bound under the cost table `c` and the return-predicate price `ep`, and names only callees with `Z`. -/
mutual
def haltS (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => haltB h ep c Z pa t && haltB h ep c Z pa e
  | .onOption _ p a => haltB h ep c Z pa p && haltB h ep c Z pa a
  | .onTag _ arms => haltArms h ep c Z pa arms
  | .onWhy _ arms => haltGArms h ep c Z pa arms
  | .call g _ _ _ => true
  | .callInd _ _ _ _ => true
  | .callIndElse _ _ _ _ _ err => haltE h ep c Z pa err
  | .locks L _ body =>
    (match h L with
      | some n => decide (kostenBlock ep c pa body ≤ n) && rufeB Z (fun _ => false) true body
      | none => true) && haltB h ep c Z pa body
  | .breaking _ body => haltB h ep c Z pa body
  | .traverse _ _ body => haltB h ep c Z pa body
  | .consumeTraverse _ _ _ _ _ _ body => haltB h ep c Z pa body
  | .retry _ _ body ueber => haltB h ep c Z pa body && haltB h ep c Z pa ueber
  | .forever _ _ body => haltB h ep c Z pa body
  | .assignSlot .. => true
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => true
  | .assignGlob .. => true
  | .putBytes .. => true
  | .assignVar .. => true
  | .shift .. => true
  | .axiomCall .. => true
  | .axiomCallElse _ _ _ _ _ _ _ _ err => haltE h ep c Z pa err
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

def haltB (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => haltS h ep c Z pa s && haltB h ep c Z pa rest
  | .bind _ rest => haltB h ep c Z pa rest
  | .bindCall g _ _ _ _ rest => haltB h ep c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => haltB h ep c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest => haltE h ep c Z pa err && haltB h ep c Z pa rest
  | .bindCallElse g _ _ _ _ err rest => haltE h ep c Z pa err && haltB h ep c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => haltB h ep c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => haltE h ep c Z pa err && haltB h ep c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => haltB h ep c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => haltE h ep c Z pa err && haltB h ep c Z pa rest
  | .regRead _ _ rest => haltB h ep c Z pa rest
  | .regReadElse _ _ _ sonst rest => haltE h ep c Z pa sonst && haltB h ep c Z pa rest
  | .awaits _ _ _ _ _ rest => haltB h ep c Z pa rest
  | .exchange _ _ _ _ rest => haltB h ep c Z pa rest
  | .narrow _ _ _ sonst rest => haltE h ep c Z pa sonst && haltB h ep c Z pa rest
  | .narrowRequired _ _ _ rest => haltB h ep c Z pa rest
  | .check _ sonst rest => haltE h ep c Z pa sonst && haltB h ep c Z pa rest
  | .float _ _ _ _ _ rest => haltB h ep c Z pa rest
  | .floatLit _ _ _ rest => haltB h ep c Z pa rest
  | .floatOf _ _ _ rest => haltB h ep c Z pa rest
  | .floatNarrow _ _ _ sonst rest => haltE h ep c Z pa sonst && haltB h ep c Z pa rest

def haltArms (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => haltB h ep c Z pa b && haltArms h ep c Z pa rest

def haltGArms (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => haltB h ep c Z pa b && haltGArms h ep c Z pa rest

def haltE (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => haltS h ep c Z pa s && haltE h ep c Z pa rest
  | .bind _ rest => haltE h ep c Z pa rest
  | .bindCall g _ _ _ _ rest => haltE h ep c Z pa rest
  | .bindCallElse g _ _ _ _ err rest => haltE h ep c Z pa err && haltE h ep c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => haltE h ep c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => haltE h ep c Z pa err && haltE h ep c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => haltE h ep c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => haltE h ep c Z pa err && haltE h ep c Z pa rest
  | .regRead _ _ rest => haltE h ep c Z pa rest
  | .regReadElse _ _ _ sonst rest => haltE h ep c Z pa sonst && haltE h ep c Z pa rest
  | .awaits _ _ _ _ _ rest => haltE h ep c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => haltE h ep c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest => haltE h ep c Z pa err && haltE h ep c Z pa rest
  | .narrow _ _ _ sonst rest => haltE h ep c Z pa sonst && haltE h ep c Z pa rest
  | .narrowRequired _ _ _ rest => haltE h ep c Z pa rest
  | .exchange _ _ _ _ rest => haltE h ep c Z pa rest
  | .ite _ t e => haltE h ep c Z pa e && haltE h ep c Z pa t
  | .float _ _ _ _ _ rest => haltE h ep c Z pa rest
  | .floatLit _ _ _ rest => haltE h ep c Z pa rest
  | .floatOf _ _ _ rest => haltE h ep c Z pa rest
  | .floatNarrow _ _ _ sonst rest => haltE h ep c Z pa sonst && haltE h ep c Z pa rest
end


/-- **K001 and K002 on one program, as one Bool.** Every function of `ks` fits under its declared cost
    `decl` and calls only functions of `ks`, directly (`kostenPasst`); and every `locks L` section in the
    body of every function `g` of `fs` costs at most `N L` in `kostenBlock (kostenEpilog P g)` (calls
    counted at `decl`, a value return at the epilogue of `g`) and calls only functions of `ks` (`haltE`).
    With `fs` the complete function list, every section of the program is checked. -/
def haltPasst [DecidableEq D.Fn] (P : Programm D) (passes : Nat) (N : D.Lock → Nat)
    (decl : D.Fn → Nat) (fs ks : List D.Fn) : Bool :=
  kostenPasst P passes decl ks &&
    fs.all fun g =>
      haltE (fun L => some (N L)) (kostenEpilog P g) decl (fun h => ks.contains h) passes (P.rumpf g)

/-- **The hold time of a section of `L` in own steps of machine G**, derived from the checked bound
    `N L`: the body (`N L`), the release (`1`), and at most one release per lock of `ls` before `L` when
    the section is left by a scoped `return` (`haltezeit_aus`). A function of `N`, not `N` itself. -/
def haltSchranke (ls : List D.Lock) (N : D.Lock → Nat) (L : D.Lock) : Nat := N L + 1 + ls.length

end Gabbro.Grammatik
