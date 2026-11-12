/-
  The binding of a lock's declared hold bound (`lock L … held <= n ops`).

  The export gate admits a literal hold bound. The duty does not disappear: `holds` is the rule K002
  over the lowered program -- every `locks L { … }` section of a lock with a declared bound costs at
  most that bound in own steps of machine G (`kostenBlock`, each call counted at the callee's declared
  cost), and calls only functions that declare a cost. That such a section bound gives the hold-time
  premise of the waiting statement (`Haltezeit`) is not proved here; the premise stays named in
  `Spec.lean`.
-/
module
public import Grammatik.Parser.Elab.Export.CostBinding
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/- `haltS h c Z pa s`: every `locks L` section in `s` whose lock has a bound `h L` costs at most the
   bound under the cost table `c`, and names only callees with `Z`. -/
mutual
def haltS (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => haltB h c Z pa t && haltB h c Z pa e
  | .onOption _ p a => haltB h c Z pa p && haltB h c Z pa a
  | .onTag _ arms => haltArms h c Z pa arms
  | .onWhy _ arms => haltGArms h c Z pa arms
  | .call g _ _ _ => true
  | .callInd _ _ _ _ => true
  | .callIndElse _ _ _ _ _ err => haltE h c Z pa err
  | .locks L _ body =>
    (match h L with
      | some n => decide (kostenBlock c pa body ≤ n) && rufeB Z (fun _ => false) true body
      | none => true) && haltB h c Z pa body
  | .breaking _ body => haltB h c Z pa body
  | .traverse _ _ body => haltB h c Z pa body
  | .consumeTraverse _ _ _ _ _ _ body => haltB h c Z pa body
  | .retry _ _ body ueber => haltB h c Z pa body && haltB h c Z pa ueber
  | .forever _ _ body => haltB h c Z pa body
  | .assignSlot .. => true
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => true
  | .assignGlob .. => true
  | .putBytes .. => true
  | .assignVar .. => true
  | .shift .. => true
  | .axiomCall .. => true
  | .axiomCallElse _ _ _ _ _ _ _ _ err => haltE h c Z pa err
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

def haltB (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => haltS h c Z pa s && haltB h c Z pa rest
  | .bind _ rest => haltB h c Z pa rest
  | .bindCall g _ _ _ _ rest => haltB h c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => haltB h c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest => haltE h c Z pa err && haltB h c Z pa rest
  | .bindCallElse g _ _ _ _ err rest => haltE h c Z pa err && haltB h c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => haltB h c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => haltE h c Z pa err && haltB h c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => haltB h c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => haltE h c Z pa err && haltB h c Z pa rest
  | .regRead _ _ rest => haltB h c Z pa rest
  | .regReadElse _ _ _ sonst rest => haltE h c Z pa sonst && haltB h c Z pa rest
  | .awaits _ _ _ _ _ rest => haltB h c Z pa rest
  | .exchange _ _ _ _ rest => haltB h c Z pa rest
  | .narrow _ _ _ sonst rest => haltE h c Z pa sonst && haltB h c Z pa rest
  | .narrowRequired _ _ _ rest => haltB h c Z pa rest
  | .check _ sonst rest => haltE h c Z pa sonst && haltB h c Z pa rest
  | .float _ _ _ _ _ rest => haltB h c Z pa rest
  | .floatLit _ _ _ rest => haltB h c Z pa rest
  | .floatOf _ _ _ rest => haltB h c Z pa rest
  | .floatNarrow _ _ _ sonst rest => haltE h c Z pa sonst && haltB h c Z pa rest

def haltArms (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => haltB h c Z pa b && haltArms h c Z pa rest

def haltGArms (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => haltB h c Z pa b && haltGArms h c Z pa rest

def haltE (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => haltS h c Z pa s && haltE h c Z pa rest
  | .bind _ rest => haltE h c Z pa rest
  | .bindCall g _ _ _ _ rest => haltE h c Z pa rest
  | .bindCallElse g _ _ _ _ err rest => haltE h c Z pa err && haltE h c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => haltE h c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => haltE h c Z pa err && haltE h c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => haltE h c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => haltE h c Z pa err && haltE h c Z pa rest
  | .regRead _ _ rest => haltE h c Z pa rest
  | .regReadElse _ _ _ sonst rest => haltE h c Z pa sonst && haltE h c Z pa rest
  | .awaits _ _ _ _ _ rest => haltE h c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => haltE h c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest => haltE h c Z pa err && haltE h c Z pa rest
  | .narrow _ _ _ sonst rest => haltE h c Z pa sonst && haltE h c Z pa rest
  | .narrowRequired _ _ _ rest => haltE h c Z pa rest
  | .exchange _ _ _ _ rest => haltE h c Z pa rest
  | .ite _ t e => haltE h c Z pa e && haltE h c Z pa t
  | .float _ _ _ _ _ rest => haltE h c Z pa rest
  | .floatLit _ _ _ rest => haltE h c Z pa rest
  | .floatOf _ _ _ rest => haltE h c Z pa rest
  | .floatNarrow _ _ _ sonst rest => haltE h c Z pa sonst && haltE h c Z pa rest
end

end Gabbro.Grammatik

namespace Gabbro.Grammatik.Parser.HeldBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The declared literal hold bounds of the source locks, by name. -/
def declared (items : List SItemTief) : Tafel (String × Nat) (·.1) :=
  Tafel.von _ (items.filterMap fun
    | .lockT name _ _ (some (.lit n)) _ _ _ => some (name, n)
    | _ => none)

variable (H C : Tafel (String × Nat) (·.1)) (u : UProg)

/-- The declared hold bound of a lock of the unit. -/
def boundOf (L : Fin u.locks.length) : Option Nat := (H.finde (lockAt u L).name).map (·.2)

/-- **The hold bounds hold** (K002): every lock with a declared bound is a lock of the unit, and
    every section of such a lock, in every function, fits under the bound. -/
def holds (P : Programm (declOf u)) (passes : Nat) : Bool :=
  H.liste.all (fun p => u.locks.any (fun l => strEq l.name p.1)) &&
    (List.finRange u.fns.length).all fun g =>
      haltE (D := declOf u) (boundOf H u) (CostBinding.decl C u) (fun x => (CostBinding.costOf C u x).isSome)
        passes (P.rumpf g)

/-- The first function with a section over its lock's bound, for the refusal. -/
def failing (P : Programm (declOf u)) (passes : Nat) : Option String :=
  match H.liste.find? (fun p => !u.locks.any (fun l => strEq l.name p.1)) with
  | some p => some p.1
  | none => ((List.finRange u.fns.length).find? fun g =>
      !haltE (D := declOf u) (boundOf H u) (CostBinding.decl C u)
        (fun x => (CostBinding.costOf C u x).isSome) passes (P.rumpf g)).map fun g => (fnAt u g).name

end Gabbro.Grammatik.Parser.HeldBinding
