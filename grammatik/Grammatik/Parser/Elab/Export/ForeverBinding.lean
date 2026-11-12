/-
  The binding of a `forever` loop's declared pass bound (`per_pass bounded n ops`).

  The export gate admits a `forever` header of the bound shape (`foreverHeader`) once its effects are
  verified against the loop. The pass bound does not disappear: `holds` checks, over the lowered
  program, that the body of every `forever` costs at most the bound declared for its `progress`
  assumption (`kostenBlock`, each call counted at the callee's declared cost) and calls only functions
  that declare a cost. Loops that name the same assumption share the smallest of their bounds, so the
  check needs no pairing of source loops with lowered ones.
-/
module
public import Grammatik.Parser.Elab.Export.CostBinding
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/- `passS h c Z pa s`: the body of every `forever` in `s` whose assumption has a bound `h a` costs at
   most the bound under the cost table `c`, and names only callees with `Z`. -/
mutual
def passS (h : D.Annahme → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => passB h c Z pa t && passB h c Z pa e
  | .onOption _ p a => passB h c Z pa p && passB h c Z pa a
  | .onTag _ arms => passArms h c Z pa arms
  | .onWhy _ arms => passGArms h c Z pa arms
  | .call g _ _ _ => true
  | .callInd _ _ _ _ => true
  | .callIndElse _ _ _ _ _ err => passE h c Z pa err
  | .locks _ _ body => passB h c Z pa body
  | .breaking _ body => passB h c Z pa body
  | .traverse _ _ body => passB h c Z pa body
  | .consumeTraverse _ _ _ _ _ _ body => passB h c Z pa body
  | .retry _ _ body ueber => passB h c Z pa body && passB h c Z pa ueber
  | .forever a _ body =>
    (match h a with
      | some n => decide (kostenBlock c pa body ≤ n) && rufeB Z (fun _ => false) true body
      | none => true) && passB h c Z pa body
  | .assignSlot .. => true
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => true
  | .assignGlob .. => true
  | .putBytes .. => true
  | .assignVar .. => true
  | .shift .. => true
  | .axiomCall .. => true
  | .axiomCallElse _ _ _ _ _ _ _ _ err => passE h c Z pa err
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

def passB (h : D.Annahme → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => passS h c Z pa s && passB h c Z pa rest
  | .bind _ rest => passB h c Z pa rest
  | .bindCall g _ _ _ _ rest => passB h c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => passB h c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest => passE h c Z pa err && passB h c Z pa rest
  | .bindCallElse g _ _ _ _ err rest => passE h c Z pa err && passB h c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => passB h c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => passE h c Z pa err && passB h c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => passB h c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => passE h c Z pa err && passB h c Z pa rest
  | .regRead _ _ rest => passB h c Z pa rest
  | .regReadElse _ _ _ sonst rest => passE h c Z pa sonst && passB h c Z pa rest
  | .awaits _ _ _ _ _ rest => passB h c Z pa rest
  | .exchange _ _ _ _ rest => passB h c Z pa rest
  | .narrow _ _ _ sonst rest => passE h c Z pa sonst && passB h c Z pa rest
  | .narrowRequired _ _ _ rest => passB h c Z pa rest
  | .check _ sonst rest => passE h c Z pa sonst && passB h c Z pa rest
  | .float _ _ _ _ _ rest => passB h c Z pa rest
  | .floatLit _ _ _ rest => passB h c Z pa rest
  | .floatOf _ _ _ rest => passB h c Z pa rest
  | .floatNarrow _ _ _ sonst rest => passE h c Z pa sonst && passB h c Z pa rest

def passArms (h : D.Annahme → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => passB h c Z pa b && passArms h c Z pa rest

def passGArms (h : D.Annahme → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => passB h c Z pa b && passGArms h c Z pa rest

def passE (h : D.Annahme → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => passS h c Z pa s && passE h c Z pa rest
  | .bind _ rest => passE h c Z pa rest
  | .bindCall g _ _ _ _ rest => passE h c Z pa rest
  | .bindCallElse g _ _ _ _ err rest => passE h c Z pa err && passE h c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => passE h c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => passE h c Z pa err && passE h c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => passE h c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => passE h c Z pa err && passE h c Z pa rest
  | .regRead _ _ rest => passE h c Z pa rest
  | .regReadElse _ _ _ sonst rest => passE h c Z pa sonst && passE h c Z pa rest
  | .awaits _ _ _ _ _ rest => passE h c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => passE h c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest => passE h c Z pa err && passE h c Z pa rest
  | .narrow _ _ _ sonst rest => passE h c Z pa sonst && passE h c Z pa rest
  | .narrowRequired _ _ _ rest => passE h c Z pa rest
  | .exchange _ _ _ _ rest => passE h c Z pa rest
  | .ite _ t e => passE h c Z pa e && passE h c Z pa t
  | .float _ _ _ _ _ rest => passE h c Z pa rest
  | .floatLit _ _ _ rest => passE h c Z pa rest
  | .floatOf _ _ _ rest => passE h c Z pa rest
  | .floatNarrow _ _ _ sonst rest => passE h c Z pa sonst && passE h c Z pa rest
end

end Gabbro.Grammatik

namespace Gabbro.Grammatik.Parser.ForeverBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.ExportMetadata

/-- The headers of the `forever` loops of a body, in every nested position. -/
def loopHeaders : Nat → SAnw → List String
  | 0, _ => []
  | n + 1, .block ss _ => ss.flatMap (loopHeaders n)
  | n + 1, .bindElse _ _ _ _ b | n + 1, .bindAxiomOptElse _ _ _ _ b | n + 1, .callIndElse _ _ _ b
  | n + 1, .callElse _ _ _ b | n + 1, .waive _ b | n + 1, .locks _ _ b | n + 1, .watch _ b
  | n + 1, .retry _ b | n + 1, .trim _ _ b | n + 1, .elsif _ b | n + 1, .arm _ _ b
  | n + 1, .each _ _ _ _ _ _ _ b => loopHeaders n b
  | n + 1, .cond _ a bs b =>
    loopHeaders n a ++ bs.flatMap (loopHeaders n) ++ (b.map (loopHeaders n)).getD []
  | n + 1, .cases _ arms => arms.flatMap (loopHeaders n)
  | n + 1, .loop header b => header :: loopHeaders n b
  | n + 1, .alloc _ _ _ _ _ (some b) => loopHeaders n b
  | _ + 1, _ => []

/-- The declared pass bounds of the source loops: the `progress` assumption and the bound. -/
def declared (items : List SItemTief) : List (String × Nat) :=
  items.flatMap fun
    | .fnT _ body => (loopHeaders 10000 body).filterMap fun header =>
        (foreverHeader header).map fun k => (k.progress, k.bound)
    | _ => []

variable (F : List (String × Nat)) (C : Tafel (String × Nat) (·.1)) (u : UProg)

/-- The pass bound of an assumption of the unit: the smallest bound declared with it. -/
def boundOf : Option (Fin u.annahmen.length) → Option Nat
  | some a => ((F.filter fun p => strEq p.1 (u.annahmen.get a)).map (·.2)).min?
  | none => none

/-- **The pass bounds hold**: every assumption a bound is declared with is one of the unit, and the
    body of every `forever`, in every function, fits under its assumption's bound. -/
def holds (P : Programm (declOf u)) (passes : Nat) : Bool :=
  F.all (fun p => u.annahmen.any (strEq p.1)) &&
    (List.finRange u.fns.length).all fun g =>
      passE (D := declOf u) (boundOf F u) (CostBinding.decl C u) (fun x => (CostBinding.costOf C u x).isSome)
        passes (P.rumpf g)

/-- The first function with a `forever` body over its bound, for the refusal. -/
def failing (P : Programm (declOf u)) (passes : Nat) : Option String :=
  match F.find? (fun p => !u.annahmen.any (strEq p.1)) with
  | some p => some p.1
  | none => ((List.finRange u.fns.length).find? fun g =>
      !passE (D := declOf u) (boundOf F u) (CostBinding.decl C u)
        (fun x => (CostBinding.costOf C u x).isSome) passes (P.rumpf g)).map fun g => (fnAt u g).name

end Gabbro.Grammatik.Parser.ForeverBinding
