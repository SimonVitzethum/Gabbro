/-
  File:      Grammatik/Parser/Cover/Mitglieder.lean
  Subject:   Track P: the REGISTER MEMBERS a lowered program reaches. `Programm P` is a function from a function
             to its `Endblock`; this file walks every body and lists the constructors of `Expr`, `Stmt`,
             `Block`, `Endblock`, `Arms`, `Args` and `ErgExpr` it uses (named `Type.ctor`, as the coverage
             register `dokumente/llvm-modelldeckung.tsv` names its members), plus the `Ty` members of the
             declaration (parameter, result, field, static and foreign-body types). The census runner
             (`MitgliederLauf.lean`) prints the union over a directory of sources, so the members the pure-Lean
             elaboration reaches can be read next to those the exporter route reaches (`gen-differenz.py`).
-/
import Grammatik.Parser.Elab.UebersetzeAllg3

namespace Gabbro.Grammatik.Parser.Cover.Mitglieder

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {D : Deklaration}

mutual

/-- The members an expression uses. -/
def eE {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → List String
  | .lit _ => ["Expr.lit"]
  | .tru => ["Expr.tru"]
  | .fls => ["Expr.fls"]
  | .var _ => ["Expr.var"]
  | .glob .. => ["Expr.glob"]
  | .slot (i := i) .. => "Expr.slot" :: eE i
  | .thru (p := p) (i := i) .. => "Expr.thru" :: (eE p ++ eE i)
  | .ptrOf .. => ["Expr.ptrOf"]
  | .fnref .. => ["Expr.fnref"]
  | .oldG .. => ["Expr.oldG"]
  | .oldS (i := i) .. => "Expr.oldS" :: eE i
  | .widen (e := e) .. => "Expr.widen" :: eE e
  | .add a b => "Expr.add" :: (eE a ++ eE b)
  | .sub a b => "Expr.sub" :: (eE a ++ eE b)
  | .neg a => "Expr.neg" :: eE a
  | .mul a b => "Expr.mul" :: (eE a ++ eE b)
  | .div (a := a) (b := b) .. => "Expr.div" :: (eE a ++ eE b)
  | .rem (a := a) (b := b) .. => "Expr.rem" :: (eE a ++ eE b)
  | .sdiv (a := a) (b := b) .. => "Expr.sdiv" :: (eE a ++ eE b)
  | .srem (a := a) (b := b) .. => "Expr.srem" :: (eE a ++ eE b)
  | .getBytes (i := i) .. => "Expr.getBytes" :: eE i
  | .band (a := a) (b := b) .. => "Expr.band" :: (eE a ++ eE b)
  | .bor (a := a) (b := b) .. => "Expr.bor" :: (eE a ++ eE b)
  | .bxor (a := a) (b := b) .. => "Expr.bxor" :: (eE a ++ eE b)
  | .shl (a := a) (b := b) .. => "Expr.shl" :: (eE a ++ eE b)
  | .shr (a := a) (b := b) .. => "Expr.shr" :: (eE a ++ eE b)
  | .lt a b => "Expr.lt" :: (eE a ++ eE b)
  | .le a b => "Expr.le" :: (eE a ++ eE b)
  | .eq a b => "Expr.eq" :: (eE a ++ eE b)
  | .fllt a b => "Expr.fllt" :: (eE a ++ eE b)
  | .flle a b => "Expr.flle" :: (eE a ++ eE b)
  | .and a b => "Expr.and" :: (eE a ++ eE b)
  | .or a b => "Expr.or" :: (eE a ++ eE b)
  | .not a => "Expr.not" :: eE a
  | .none _ => ["Expr.none"]
  | .some e => "Expr.some" :: eE e
  | .istSome e => "Expr.istSome" :: eE e
  | .case (nutz := nutz) .. => "Expr.case" :: eN nutz
  | .why .. => ["Expr.why"]
  | .forallSlots (body := body) .. => "Expr.forallSlots" :: eE body
  | .existsSlots (body := body) .. => "Expr.existsSlots" :: eE body
  | .reaches (a := a) (b := b) .. => "Expr.reaches" :: (eE a ++ eE b)

def eN {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)} : NutzlastExpr D Γ Λ o → List String
  | .empty => ["NutzlastExpr.empty"]
  | .num e => "NutzlastExpr.num" :: eE e

end

/-- The members of an argument list. -/
def eA {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} : Args D Γ Λ τs → List String
  | .nil => ["Args.nil"]
  | .cons e rest => "Args.cons" :: (eE e ++ eA rest)

/-- The members of a returned value. -/
def eR {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} : ErgExpr D Γ Λ o → List String
  | .empty => ["ErgExpr.empty"]
  | .val e => "ErgExpr.val" :: eE e

mutual

/-- The members a statement uses. -/
def cS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → List String
  | .assignSlot (i := i) (e := e) .. => "Stmt.assignSlot" :: (eE i ++ eE e)
  | .assignThru (p := p) (i := i) (e := e) .. => "Stmt.assignThru" :: (eE p ++ eE i ++ eE e)
  | .assignGlob (e := e) .. => "Stmt.assignGlob" :: eE e
  | .putBytes (i := i) (e := e) .. => "Stmt.putBytes" :: (eE i ++ eE e)
  | .assignVar _ e => "Stmt.assignVar" :: eE e
  | .shift (i := i) .. => "Stmt.shift" :: eE i
  | .ite c t e => "Stmt.ite" :: (eE c ++ cB t ++ cB e)
  | .onOption o p a => "Stmt.onOption" :: (eE o ++ cB p ++ cB a)
  | .onTag v arms => "Stmt.onTag" :: (eE v ++ cArms arms)
  | .onWhy r arms => "Stmt.onWhy" :: (eE r ++ cGArms arms)
  | .call (args := args) .. => "Stmt.call" :: eA args
  | .callInd (p := p) (args := args) .. => "Stmt.callInd" :: (eE p ++ eA args)
  | .locks _ _ body => "Stmt.locks" :: cB body
  | .breaking _ body => "Stmt.breaking" :: cB body
  | .traverse _ inv body => "Stmt.traverse" :: (eE inv ++ cB body)
  | .retry _ bis body ueber => "Stmt.retry" :: (eE bis ++ cB body ++ cB ueber)
  | .forever _ inv body => "Stmt.forever" :: (eE inv ++ cB body)
  | .axiomCall (args := args) .. => "Stmt.axiomCall" :: eA args
  | .regWrite (e := e) .. => "Stmt.regWrite" :: eE e
  | .transition .. => ["Stmt.transition"]
  | .publish (e := e) .. => "Stmt.publish" :: eE e
  | .advances .. => ["Stmt.advances"]
  | .retires .. => ["Stmt.retires"]
  | .ret e _ => "Stmt.ret" :: eR e
  | .retWhy .. => ["Stmt.retWhy"]
  | .leave _ => ["Stmt.leave"]
  | .next _ => ["Stmt.next"]

/-- The members a block uses. -/
def cB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → List String
  | .nil => ["Block.nil"]
  | .cons s rest => "Block.cons" :: (cS s ++ cB rest)
  | .bind e rest => "Block.bind" :: (eE e ++ cB rest)
  | .bindCall (args := args) (rest := rest) .. => "Block.bindCall" :: (eA args ++ cB rest)
  | .bindCallInd (p := p) (args := args) (rest := rest) .. => "Block.bindCallInd" :: (eE p ++ eA args ++ cB rest)
  | .bindCallElse (args := args) (err := err) (rest := rest) .. => "Block.bindCallElse" :: (eA args ++ cE err ++ cB rest)
  | .bindAxiom (args := args) (rest := rest) .. => "Block.bindAxiom" :: (eA args ++ cB rest)
  | .bindAxiomElse (args := args) (err := err) (rest := rest) .. => "Block.bindAxiomElse" :: (eA args ++ cE err ++ cB rest)
  | .regRead (rest := rest) .. => "Block.regRead" :: cB rest
  | .regReadElse (zusage := z) (sonst := sonst) (rest := rest) .. => "Block.regReadElse" :: (eE z ++ cE sonst ++ cB rest)
  | .awaits (rest := rest) .. => "Block.awaits" :: cB rest
  | .exchange (neu := neu) (rest := rest) .. => "Block.exchange" :: (eE neu ++ cB rest)
  | .narrow e _ _ sonst rest => "Block.narrow" :: (eE e ++ cE sonst ++ cB rest)
  | .check c sonst rest => "Block.check" :: (eE c ++ cE sonst ++ cB rest)
  | .float _ a b _ _ rest => "Block.float" :: (eE a ++ eE b ++ cB rest)
  | .floatLit _ _ _ rest => "Block.floatLit" :: cB rest
  | .floatOf e _ _ rest => "Block.floatOf" :: (eE e ++ cB rest)
  | .floatNarrow e _ _ sonst rest => "Block.floatNarrow" :: (eE e ++ cE sonst ++ cB rest)

/-- The members the arms of a tagged match use. -/
def cArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List String
  | .nil => ["Arms.nil"]
  | .cons b rest => "Arms.cons" :: (cB b ++ cArms rest)

/-- The members the arms of a reason match use. -/
def cGArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List String
  | .nil => ["GrundArms.nil"]
  | .cons b rest => "GrundArms.cons" :: (cB b ++ cGArms rest)

/-- The members an end block uses. -/
def cE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → List String
  | .ret e _ => "Endblock.ret" :: eR e
  | .retWhy .. => ["Endblock.retWhy"]
  | .leave _ => ["Endblock.leave"]
  | .next _ => ["Endblock.next"]
  | .cons s rest => "Endblock.cons" :: (cS s ++ cE rest)
  | .bind e rest => "Endblock.bind" :: (eE e ++ cE rest)
  | .bindCall (args := args) (rest := rest) .. => "Endblock.bindCall" :: (eA args ++ cE rest)
  | .bindCallElse (args := args) (err := err) (rest := rest) .. => "Endblock.bindCallElse" :: (eA args ++ cE err ++ cE rest)
  | .bindAxiom (args := args) (rest := rest) .. => "Endblock.bindAxiom" :: (eA args ++ cE rest)
  | .bindAxiomElse (args := args) (err := err) (rest := rest) .. => "Endblock.bindAxiomElse" :: (eA args ++ cE err ++ cE rest)
  | .regRead (rest := rest) .. => "Endblock.regRead" :: cE rest
  | .regReadElse (zusage := z) (sonst := sonst) (rest := rest) .. => "Endblock.regReadElse" :: (eE z ++ cE sonst ++ cE rest)
  | .awaits (rest := rest) .. => "Endblock.awaits" :: cE rest
  | .bindCallInd (p := p) (args := args) (rest := rest) .. => "Endblock.bindCallInd" :: (eE p ++ eA args ++ cE rest)

end

/-- The `Ty` constructor a type is. -/
def tyName : Ty → String
  | .int .. => "Ty.int"
  | .bool => "Ty.bool"
  | .opt _ => "Ty.opt"
  | .sum _ => "Ty.sum"
  | .why _ => "Ty.why"
  | .never => "Ty.never"
  | .fl .. => "Ty.fl"
  | .fnptr _ => "Ty.fnptr"
  | .ptr .. => "Ty.ptr"

/-- The members a lowered program reaches: every function's body, and the types its parameters, results, table
    fields and statics have. -/
def mitglieder (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn) : List String :=
  let koerper := fs.flatMap fun f => cE (P.rumpf f)
  let typen := fs.flatMap fun f => (declOf u).params f ++ ((declOf u).erg f).toList
  let felder := (List.finRange u.tabs.length).flatMap fun t =>
    (List.finRange (fieldCount u t)).map fun f => typAt u t f
  let globs := (List.finRange u.globs.length).map fun g => (declOf u).gtyp g
  let axiome := (List.finRange u.axs.length).flatMap fun a => (declOf u).aparams a ++ ((declOf u).aerg a).toList
  koerper ++ (typen ++ felder ++ globs ++ axiome).map tyName

end Gabbro.Grammatik.Parser.Cover.Mitglieder
