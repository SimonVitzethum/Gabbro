/-
  File:      Grammatik/Gen/Abdeckung/Mitglieder.lean
  Subject:   WHAT A TERM CONTAINS, as the members of the model's register (`dokumente/llvm-modelldeckung.tsv`, the
             coverage denominator): one total function per family of the model, each constructor a clause that names
             itself and the declaration members its typing rule reads. The match is TOTAL, so a new constructor of
             the model stops the build here until it is named (the register and the generator move together).

             The names are the register's: `Expr.add`, `Stmt.locks`, `Ty.int`, `Deklaration.rang`, `RufPasst.hh`.
-/
import Grammatik.Gen.Erzeuger.Programm

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D]

/-- The constructor of a type. -/
def tyM : Ty → List String
  | .int .. => ["Ty.int"]
  | .bool => ["Ty.bool"]
  | .opt _ => ["Ty.opt"]
  | .sum _ => ["Ty.sum"]
  | .why _ => ["Ty.why"]
  | .never => ["Ty.never"]
  | .fl .. => ["Ty.fl"]
  | .fnptr _ => ["Ty.fnptr"]
  | .ptr .. => ["Ty.ptr"]
  | .ref _ => ["Ty.ref"]

/-- The constructor of a variable. -/
def varM : ∀ {Γ : Ctx} {τ : Ty}, Var Γ τ → List String
  | _, _, .here => ["Var.here"]
  | _, _, .there x => "Var.there" :: varM x

/-- The constructor of a float operation. -/
def gleitM : GleitOp → List String
  | .add => ["GleitOp.add"]
  | .sub => ["GleitOp.sub"]
  | .mul => ["GleitOp.mul"]
  | .div => ["GleitOp.div"]

/-- The members of a regs class. -/
def klasseM : Regklasse → List String
  | .r => ["Regklasse.r"]
  | .w => ["Regklasse.w"]
  | .rw => ["Regklasse.rw"]
  | .w1c => ["Regklasse.w1c"]
  | .rc => ["Regklasse.rc"]

/-- What a call's premise and the callee's signature put into play (`RufPasst`, `Signatur`, `Res`) at resources `Λ`. -/
def rufM (V : Vertrag D) (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) : List String :=
  (if (Aufz.tab (D := D)).any (fun t => S.schreibt t) then ["RufPasst.hw", "Signatur.schreibt"] else []) ++
  (if (Aufz.glob (D := D)).any (fun g => S.gschreibt g) then ["RufPasst.hg", "Signatur.gschreibt"] else []) ++
  (if S.konsumiert.isEmpty then [] else ["RufPasst.hk", "Signatur.konsumiert"]) ++
  (if S.haelt.isEmpty then [] else ["RufPasst.hh", "Signatur.haelt"]) ++
  (if Λ.any (fun r => match r with | .held L => decide (L ∉ S.haelt) | .marke .. => false) then ["RufPasst.hx"] else []) ++
  (if V.boden.isSome then ["RufPasst.hb"] else []) ++
  (if S.params.isEmpty then [] else ["Signatur.params"]) ++
  (if S.erg.isSome then ["Signatur.erg"] else []) ++
  (if S.gruende = 0 then [] else ["Signatur.gruende"]) ++
  (if S.produziert.isEmpty then [] else ["Signatur.produziert"]) ++
  (if S.boden.isSome then ["Signatur.boden"] else [])

/-- What a call through a function pointer puts into play: the callee conforms to the pointer type
    (`Deklaration.passt_ok`), and the conformance is the whole `SigPasst`. -/
def passtM : List String :=
  ["Deklaration.passt", "Deklaration.passt_ok", "SigPasst.params", "SigPasst.erg", "SigPasst.gruende",
   "SigPasst.schreibt", "SigPasst.gschreibt", "SigPasst.konsumiert", "SigPasst.produziert", "SigPasst.haelt",
   "SigPasst.extra", "SigPasst.boden"]

/-- The resources held. -/
def resM : List (Res D) → List String
  | [] => []
  | .held _ :: rest => "Res.held" :: resM rest
  | .marke .. :: rest => "Res.marke" :: resM rest

/-! ## Expressions -/

mutual
def exprM : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}, Expr D Γ Λ τ → List String
  | _, _, _, .lit _ => ["Expr.lit", "Ty.int"]
  | _, _, _, .tru => ["Expr.tru", "Ty.bool"]
  | _, _, _, .fls => ["Expr.fls", "Ty.bool"]
  | _, _, τ, .var x => "Expr.var" :: tyM τ ++ varM x
  | _, _, _, .glob g _ => "Expr.glob" :: tyM (D.gtyp g) ++ ["Deklaration.gtyp"] ++
      (if (D.gbraucht g).isEmpty then [] else ["Deklaration.gbraucht"]) ++ (if D.atomar g then ["Deklaration.atomar"] else [])
  | _, _, _, .slot t f i _ => "Expr.slot" :: tyM (D.typ t f) ++ ["Deklaration.count", "Deklaration.typ"] ++ exprM i
  | _, _, _, .thru p t _ f i _ => "Expr.thru" :: tyM (D.typ t f) ++ ["Deklaration.tabNr"] ++ exprM p ++ exprM i
  | _, _, _, .ptrOf .. => ["Expr.ptrOf", "Ty.ptr", "Deklaration.tabNr"]
  | _, _, _, .refEq a b => "Expr.refEq" :: "Ty.bool" :: exprM a ++ exprM b
  | _, _, _, .slotRef r t _ _ f _ => "Expr.slotRef" :: tyM (D.typ t f) ++ ["Deklaration.tabNr", "Deklaration.offen", "Deklaration.typ"] ++ exprM r
  | _, _, _, .fnref .. => ["Expr.fnref", "Ty.fnptr", "Deklaration.sig", "Deklaration.passt"]
  | _, _, _, .oldG g _ => "Expr.oldG" :: tyM (D.gtyp g)
  | _, _, _, .oldS t f i _ => "Expr.oldS" :: tyM (D.typ t f) ++ exprM i
  | _, _, _, .widen _ _ e => "Expr.widen" :: "Ty.int" :: exprM e
  | _, _, _, .add a b => "Expr.add" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .sub a b => "Expr.sub" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .neg a => "Expr.neg" :: "Ty.int" :: exprM a
  | _, _, _, .mul a b => "Expr.mul" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .div _ _ a b => "Expr.div" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .rem _ _ a b => "Expr.rem" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .sdiv _ a b => "Expr.sdiv" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .srem _ a b => "Expr.srem" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .getBytes _ _ _ _ i _ _ _ => "Expr.getBytes" :: "Ty.int" :: exprM i
  | _, _, _, .band _ _ a b => "Expr.band" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .bor _ _ _ _ _ a b => "Expr.bor" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .bxor _ _ _ _ _ a b => "Expr.bxor" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .shl _ _ _ _ _ a b => "Expr.shl" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .shr _ _ _ _ _ a b => "Expr.shr" :: "Ty.int" :: exprM a ++ exprM b
  | _, _, _, .lt a b => "Expr.lt" :: "Ty.bool" :: exprM a ++ exprM b
  | _, _, _, .le a b => "Expr.le" :: "Ty.bool" :: exprM a ++ exprM b
  | _, _, _, .eq a b => "Expr.eq" :: "Ty.bool" :: exprM a ++ exprM b
  | _, _, _, .fllt a b => "Expr.fllt" :: "Ty.bool" :: "Ty.fl" :: exprM a ++ exprM b
  | _, _, _, .flle a b => "Expr.flle" :: "Ty.bool" :: "Ty.fl" :: exprM a ++ exprM b
  | _, _, _, .and a b => "Expr.and" :: "Ty.bool" :: exprM a ++ exprM b
  | _, _, _, .or a b => "Expr.or" :: "Ty.bool" :: exprM a ++ exprM b
  | _, _, _, .not a => "Expr.not" :: "Ty.bool" :: exprM a
  | _, _, _, .none _ => ["Expr.none", "Ty.opt"]
  | _, _, _, .some e => "Expr.some" :: "Ty.opt" :: exprM e
  | _, _, _, .istSome e => "Expr.istSome" :: "Ty.bool" :: "Ty.opt" :: exprM e
  | _, _, _, .case _ _ nutz => "Expr.case" :: "Ty.sum" :: nutzM nutz
  | _, _, _, .why .. => ["Expr.why", "Ty.why"]
  | _, _, _, .forallSlots _ body _ => "Expr.forallSlots" :: "Ty.bool" :: exprM body
  | _, _, _, .existsSlots _ body _ => "Expr.existsSlots" :: "Ty.bool" :: exprM body
  | _, _, _, .reaches _ _ _ a b _ => "Expr.reaches" :: "Ty.bool" :: "Ty.opt" :: exprM a ++ exprM b

def nutzM : ∀ {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)}, NutzlastExpr D Γ Λ o → List String
  | _, _, _, .empty => ["NutzlastExpr.empty"]
  | _, _, _, .num e => "NutzlastExpr.num" :: exprM e
end

/-- The members of an argument list. -/
def argsM : ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty}, Args D Γ Λ τs → List String
  | _, _, _, .nil => ["Args.nil"]
  | _, _, _, .cons e rest => "Args.cons" :: exprM e ++ argsM rest

/-- The members of a result expression. -/
def ergM : ∀ {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty}, ErgExpr D Γ Λ o → List String
  | _, _, _, .empty => ["ErgExpr.empty"]
  | _, _, _, .val e => "ErgExpr.val" :: exprM e

/-! ## Statements, blocks, end blocks -/

variable {V : Vertrag D}

/-! ## Cells: a constructor in its context, a statement directly inside another -/

/-- The cell of a statement: the constructor, and with it the constructor in a loop body (`@loop`) and under a held
    lock (`@held`). -/
def zelle (l : Bool) (Λ : List (Res D)) (c : String) : List String :=
  c :: ((if l then [c ++ "@loop"] else []) ++
    (if Λ.any (fun r => match r with | .held _ => true | .marke .. => false) then [c ++ "@held"] else []))

/-- The nesting cells `outer>inner` of a container and the statements directly in its blocks. -/
def paare (outer : String) (inner : List String) : List String := inner.map fun i => outer ++ ">" ++ i

/-- The name of a statement. -/
def stmtName {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Stmt D V l Γ Λ Λ' → String
  | _, _, _, _, .assignSlot .. => "Stmt.assignSlot"
  | _, _, _, _, .assignThru .. => "Stmt.assignThru"
  | _, _, _, _, .assignSlotRef .. => "Stmt.assignSlotRef"
  | _, _, _, _, .assignGlob .. => "Stmt.assignGlob"
  | _, _, _, _, .putBytes .. => "Stmt.putBytes"
  | _, _, _, _, .assignVar .. => "Stmt.assignVar"
  | _, _, _, _, .shift .. => "Stmt.shift"
  | _, _, _, _, .ite .. => "Stmt.ite"
  | _, _, _, _, .onOption .. => "Stmt.onOption"
  | _, _, _, _, .onTag .. => "Stmt.onTag"
  | _, _, _, _, .onWhy .. => "Stmt.onWhy"
  | _, _, _, _, .call .. => "Stmt.call"
  | _, _, _, _, .callInd .. => "Stmt.callInd"
  | _, _, _, _, .locks .. => "Stmt.locks"
  | _, _, _, _, .breaking .. => "Stmt.breaking"
  | _, _, _, _, .traverse .. => "Stmt.traverse"
  | _, _, _, _, .retry .. => "Stmt.retry"
  | _, _, _, _, .forever .. => "Stmt.forever"
  | _, _, _, _, .axiomCall .. => "Stmt.axiomCall"
  | _, _, _, _, .regWrite .. => "Stmt.regWrite"
  | _, _, _, _, .transition .. => "Stmt.transition"
  | _, _, _, _, .publish .. => "Stmt.publish"
  | _, _, _, _, .advances .. => "Stmt.advances"
  | _, _, _, _, .retires .. => "Stmt.retires"
  | _, _, _, _, .ret .. => "Stmt.ret"
  | _, _, _, _, .retWhy .. => "Stmt.retWhy"
  | _, _, _, _, .leave .. => "Stmt.leave"
  | _, _, _, _, .next .. => "Stmt.next"

/-- The statements directly in the spine of a block. -/
def blockStmts {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Block D V l Γ Λ Λ' → List String
  | _, _, _, _, .nil => []
  | _, _, _, _, .cons s rest => stmtName s :: blockStmts rest
  | _, _, _, _, .bind _ rest => blockStmts rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .bindCallElse _ _ _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .regRead _ _ rest => blockStmts rest
  | _, _, _, _, .regReadElse _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .awaits _ _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .exchange _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .narrow _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .check _ _ rest => blockStmts rest
  | _, _, _, _, .float _ _ _ _ _ rest => blockStmts rest
  | _, _, _, _, .floatLit _ _ _ rest => blockStmts rest
  | _, _, _, _, .floatOf _ _ _ rest => blockStmts rest
  | _, _, _, _, .floatNarrow _ _ _ _ rest => blockStmts rest

/-- The statements directly in the spine of an end block. -/
def endStmts {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}, Endblock D V l Γ Λ → List String
  | _, _, _, .cons s rest => stmtName s :: endStmts rest
  | _, _, _, .bind _ rest => endStmts rest
  | _, _, _, .bindCall _ _ _ _ _ rest => endStmts rest
  | _, _, _, .bindCallElse _ _ _ _ _ err rest => endStmts rest
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => endStmts rest
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest => endStmts rest
  | _, _, _, .regRead _ _ rest => endStmts rest
  | _, _, _, .regReadElse _ _ _ _ rest => endStmts rest
  | _, _, _, .awaits _ _ _ _ _ rest => endStmts rest
  | _, _, _, .bindCallInd _ _ _ _ _ rest => endStmts rest
  | _, _, _, .ret .. => []
  | _, _, _, .retWhy .. => []
  | _, _, _, .leave .. => []
  | _, _, _, .next .. => []

/-- The statements directly in the arms of a tag match. -/
def armsStmts {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))},
    Arms D V l Γ Λ Λ' cs → List String
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, .cons b rest => blockStmts b ++ armsStmts rest

/-- The statements directly in the arms of a reason match. -/
def grundArmsStmts {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat},
    GrundArms D V l Γ Λ Λ' n → List String
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, .cons b rest => blockStmts b ++ grundArmsStmts rest

mutual
def stmtM : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Stmt D V l Γ Λ Λ' → List String
  | l, _, Λ, _, .assignSlot _ _ i e _ _ => zelle l Λ "Stmt.assignSlot" ++ ("Vertrag.schreibt" :: exprM i ++ exprM e ++ resM Λ)
  | l, _, Λ, _, .assignThru p _ _ _ i e _ _ => zelle l Λ "Stmt.assignThru" ++ ("Vertrag.schreibt" :: exprM p ++ exprM i ++ exprM e ++ resM Λ)
  | l, _, Λ, _, .assignSlotRef r _ _ _ _ e _ _ => zelle l Λ "Stmt.assignSlotRef" ++ ("Vertrag.schreibt" :: "Deklaration.offen" :: exprM r ++ exprM e ++ resM Λ)
  | l, _, Λ, _, .assignGlob _ e _ _ => zelle l Λ "Stmt.assignGlob" ++ ("Vertrag.gschreibt" :: exprM e ++ resM Λ)
  | l, _, Λ, _, .putBytes _ _ _ _ i _ _ e _ _ => zelle l Λ "Stmt.putBytes" ++ (exprM i ++ exprM e ++ resM Λ)
  | l, _, Λ, _, .assignVar x e => zelle l Λ "Stmt.assignVar" ++ (varM x ++ exprM e ++ resM Λ)
  | l, _, Λ, _, .shift _ _ _ i _ _ _ _ _ _ => zelle l Λ "Stmt.shift" ++ ("Deklaration.erlaubt" :: exprM i ++ resM Λ)
  | l, _, Λ, _, .ite c t e => zelle l Λ "Stmt.ite" ++ (exprM c ++ blockM t ++ blockM e ++ resM Λ ++ paare "Stmt.ite" (blockStmts t ++ blockStmts e))
  | l, _, Λ, _, .onOption o p a => zelle l Λ "Stmt.onOption" ++ (exprM o ++ blockM p ++ blockM a ++ resM Λ ++ paare "Stmt.onOption" (blockStmts p ++ blockStmts a))
  | l, _, Λ, _, .onTag v arms => zelle l Λ "Stmt.onTag" ++ (exprM v ++ armsM arms ++ resM Λ ++ paare "Stmt.onTag" (armsStmts arms))
  | l, _, Λ, _, .onWhy r arms => zelle l Λ "Stmt.onWhy" ++ (exprM r ++ grundArmsM arms ++ resM Λ ++ paare "Stmt.onWhy" (grundArmsStmts arms))
  | l, _, Λ, _, .call f args _ _ => zelle l Λ "Stmt.call" ++ ("Deklaration.sigNr" :: argsM args ++ rufM V (D.signatur f) Λ ++ resM Λ)
  | l, _, Λ, _, .callInd p args _ _ => zelle l Λ "Stmt.callInd" ++ ("Deklaration.sigNr" :: passtM ++ exprM p ++ argsM args ++ resM Λ)
  | l, _, Λ, _, .locks _ _ body => zelle l Λ "Stmt.locks" ++ ("Deklaration.rang" :: blockM body ++ resM Λ ++ paare "Stmt.locks" (blockStmts body))
  | l, _, Λ, _, .breaking _ body => zelle l Λ "Stmt.breaking" ++ ("Deklaration.traeger" :: blockM body ++ resM Λ ++ paare "Stmt.breaking" (blockStmts body))
  | l, _, Λ, _, .traverse _ inv body => zelle l Λ "Stmt.traverse" ++ (exprM inv ++ blockM body ++ resM Λ ++ paare "Stmt.traverse" (blockStmts body))
  | l, _, Λ, _, .retry _ bis body ueb => zelle l Λ "Stmt.retry" ++ (exprM bis ++ blockM body ++ blockM ueb ++ resM Λ ++ paare "Stmt.retry" (blockStmts body ++ blockStmts ueb))
  | l, _, Λ, _, .forever _ inv body => zelle l Λ "Stmt.forever" ++ ("Deklaration.Annahme" :: exprM inv ++ blockM body ++ resM Λ ++ paare "Stmt.forever" (blockStmts body))
  | l, _, Λ, _, .axiomCall _ args _ _ _ _ _ => zelle l Λ "Stmt.axiomCall" ++ ("Deklaration.aparams" :: "Deklaration.aschreibt" :: argsM args ++ resM Λ)
  | l, _, Λ, _, .regWrite r _ e => zelle l Λ "Stmt.regWrite" ++ ("Deklaration.rklasse" :: klasseM (D.rklasse r) ++ exprM e ++ resM Λ)
  | l, _, Λ, _, .transition r _ m _ _ _ _ =>
    zelle l Λ "Stmt.transition" ++ ("Deklaration.spiegel" :: klasseM (D.rklasse r) ++ klasseM (D.rklasse m) ++ resM Λ)
  | l, _, Λ, _, .publish _ e _ _ _ _ => zelle l Λ "Stmt.publish" ++ ("Deklaration.nutzlast" :: exprM e ++ resM Λ)
  | l, _, Λ, _, .advances .. => zelle l Λ "Stmt.advances" ++ ("Deklaration.stufen" :: "Res.marke" :: resM Λ)
  | l, _, Λ, _, .retires .. => zelle l Λ "Stmt.retires" ++ ("Deklaration.Annahme" :: "Res.marke" :: resM Λ)
  | l, _, Λ, _, .ret e _ => zelle l Λ "Stmt.ret" ++ (ergM e ++ resM Λ)
  | l, _, Λ, _, .retWhy .. => zelle l Λ "Stmt.retWhy" ++ (resM Λ)
  | l, _, Λ, _, .leave _ => zelle l Λ "Stmt.leave" ++ (resM Λ)
  | l, _, Λ, _, .next _ => zelle l Λ "Stmt.next" ++ (resM Λ)

def blockM : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Block D V l Γ Λ Λ' → List String
  | _, _, _, _, .nil => ["Block.nil"]
  | _, _, _, _, .cons s rest => "Block.cons" :: stmtM s ++ blockM rest
  | _, _, _, _, .bind e rest => "Block.bind" :: exprM e ++ blockM rest
  | l, _, Λ, _, .bindCall f args _ _ _ rest => "Block.bindCall" :: argsM args ++ rufM V (D.signatur f) Λ ++ blockM rest
  | l, _, Λ, _, .bindCallInd p args _ _ _ rest => "Block.bindCallInd" :: passtM ++ exprM p ++ argsM args ++ blockM rest
  | l, _, Λ, _, .bindCallElse f args _ _ _ err rest =>
    zelle l Λ "Block.bindCallElse" ++ (argsM args ++ rufM V (D.signatur f) Λ ++ endM err ++ blockM rest ++ paare "Block.bindCallElse" (endStmts err))
  | _, _, _, _, .bindAxiom _ args _ _ _ _ _ rest => "Block.bindAxiom" :: argsM args ++ blockM rest
  | _, _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
    "Block.bindAxiomElse" :: "Deklaration.agruende" :: argsM args ++ endM err ++ blockM rest ++ paare "Block.bindAxiomElse" (endStmts err)
  | _, _, _, _, .regRead r _ rest => "Block.regRead" :: klasseM (D.rklasse r) ++ blockM rest
  | _, _, _, _, .regReadElse r _ z sonst rest =>
    "Block.regReadElse" :: "Deklaration.rzusage" :: klasseM (D.rklasse r) ++ exprM z ++ endM sonst ++ blockM rest ++ paare "Block.regReadElse" (endStmts sonst)
  | _, _, _, _, .awaits _ _ _ _ _ rest => "Block.awaits" :: blockM rest
  | _, _, _, _, .exchange _ neu _ _ rest => "Block.exchange" :: exprM neu ++ blockM rest
  | _, _, _, _, .narrow e _ _ sonst rest => "Block.narrow" :: exprM e ++ endM sonst ++ blockM rest ++ paare "Block.narrow" (endStmts sonst)
  | _, _, _, _, .check c sonst rest => "Block.check" :: exprM c ++ endM sonst ++ blockM rest ++ paare "Block.check" (endStmts sonst)
  | _, _, _, _, .float op a b _ _ rest => "Block.float" :: "Ty.fl" :: gleitM op ++ exprM a ++ exprM b ++ blockM rest
  | _, _, _, _, .floatLit _ _ _ rest => "Block.floatLit" :: "Ty.fl" :: blockM rest
  | _, _, _, _, .floatOf e _ _ rest => "Block.floatOf" :: "Ty.fl" :: exprM e ++ blockM rest
  | _, _, _, _, .floatNarrow e _ _ sonst rest => "Block.floatNarrow" :: "Ty.fl" :: exprM e ++ endM sonst ++ blockM rest ++ paare "Block.floatNarrow" (endStmts sonst)

def endM : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}, Endblock D V l Γ Λ → List String
  | _, _, _, .ret e _ => "Endblock.ret" :: ergM e
  | _, _, _, .retWhy .. => ["Endblock.retWhy"]
  | _, _, _, .leave _ => ["Endblock.leave"]
  | _, _, _, .next _ => ["Endblock.next"]
  | _, _, _, .cons s rest => "Endblock.cons" :: stmtM s ++ endM rest
  | _, _, _, .bind e rest => "Endblock.bind" :: exprM e ++ endM rest
  | _, _, _, .bindCall _ args _ _ _ rest => "Endblock.bindCall" :: argsM args ++ endM rest
  | _, _, _, .bindCallElse _ args _ _ _ err rest =>
    "Endblock.bindCallElse" :: "Deklaration.gruende" :: argsM args ++ endM err ++ endM rest
  | _, _, _, .bindAxiom _ args _ _ _ _ _ rest => "Endblock.bindAxiom" :: argsM args ++ endM rest
  | _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
    "Endblock.bindAxiomElse" :: argsM args ++ endM err ++ endM rest
  | _, _, _, .regRead r _ rest => "Endblock.regRead" :: klasseM (D.rklasse r) ++ endM rest
  | _, _, _, .regReadElse r _ z sonst rest =>
    "Endblock.regReadElse" :: "Deklaration.rzusage" :: klasseM (D.rklasse r) ++ exprM z ++ endM sonst ++ endM rest
  | _, _, _, .awaits _ _ _ _ _ rest => "Endblock.awaits" :: endM rest
  | _, _, _, .bindCallInd p args _ _ _ rest => "Endblock.bindCallInd" :: passtM ++ exprM p ++ argsM args ++ endM rest

def armsM : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))},
    Arms D V l Γ Λ Λ' cs → List String
  | _, _, _, _, _, .nil => ["Arms.nil"]
  | _, _, _, _, _, .cons b rest => "Arms.cons" :: blockM b ++ armsM rest

def grundArmsM : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat},
    GrundArms D V l Γ Λ Λ' n → List String
  | _, _, _, _, _, .nil => ["GrundArms.nil"]
  | _, _, _, _, _, .cons b rest => "GrundArms.cons" :: blockM b ++ grundArmsM rest
end

/-- The members of the contract of a function (`Vertrag`). -/
def vertragM (V : Vertrag D) : List String :=
  (if (Aufz.tab (D := D)).any (fun t => V.schreibt t) then ["Vertrag.schreibt"] else []) ++
  (if (Aufz.glob (D := D)).any (fun g => V.gschreibt g) then ["Vertrag.gschreibt"] else []) ++
  (if V.erg.isSome then ["Vertrag.erg"] else []) ++ (if V.gruende = 0 then [] else ["Vertrag.gruende"]) ++
  (if V.haelt.isEmpty then [] else ["Vertrag.haelt"]) ++ (if V.produziert.isEmpty then [] else ["Vertrag.produziert"]) ++
  (if V.boden.isSome then ["Vertrag.boden"] else [])

/-- **The members a skeleton contains**: its bodies, the contracts of its functions, the handler flag. -/
def hautM (h : Haut D) : List String :=
  ["Programm.rumpf"] ++ ((Aufz.fn (D := D)).flatMap fun f => endM (h.rumpf f) ++ vertragM (vertragVon D f)) ++
  (if (Aufz.fn (D := D)).any h.unterbricht then ["Programm.unterbricht"] else [])

/-- **The members of a program with its contracts**: the skeleton and the contract expressions. -/
def progM (P : Programm D) : List String :=
  hautM P.haut ++ ["Programm.requires", "Programm.ensures"] ++ ((Aufz.fn (D := D)).flatMap fun f => exprM (P.requires f) ++ exprM (P.ensures f)) ++
  (if (Aufz.inv (D := D)).isEmpty then [] else ["Programm.invariante"]) ++ ((Aufz.inv (D := D)).flatMap fun i => exprM (P.invariante i))

end Gabbro.Grammatik.Gen
