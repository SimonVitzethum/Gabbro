/- Part 3 of 5 of `KostenG` (split by instrumente/teile/lean-teilen.py; the umbrella `KostenG.lean` imports all parts). -/
public import Grammatik.Logik.Fortschritt.KostenG.T3Basis
import all Grammatik.Logik.Fortschritt.KostenG.T3Basis
module
public import Grammatik.Logik.Fortschritt.KostenG.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
mutual
/-- **The checker's number**, `kosten.rs::anweisung`/`block`/`ruf` read
    over the Lean syntax (meaningful where `spiegelS` holds). -/
def kostenKS (c : D.Fn → Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Nat
  -- `Zuweisung`: `1 + ausdruck(wert)` -- the target place is not read (F1)
  | .assignSlot _ _ _ e _ _ => 1 + kostenExpr e
  | .assignThru _ _ _ _ _ e _ _ => 1 + kostenExpr e
  | .assignSlotRef _ _ _ _ _ e _ _ => 1 + kostenExpr e
  | .assignGlob _ e _ _ => 1 + kostenExpr e
  | .putBytes _ _ _ _ _ _ _ e _ _ => 1 + kostenExpr e
  | .assignVar _ e => 1 + kostenExpr e
  | .shift .. => 1
  -- `Wenn`: conditions plus the maximum over the arms, the branch free
  | .ite b t e => kostenExpr b + max (kostenKB c t) (kostenKB c e)
  -- `Match`: subject plus the maximum over the arms
  | .onOption o p a => kostenExpr o + max (kostenKB c p) (kostenKB c a)
  | .onTag v arms => kostenExpr v + kostenKArms c arms
  | .onWhy r arms => kostenExpr r + kostenKGArms c arms
  -- `ruf`: declared costs plus arguments
  | .call g args _ _ => kostenArgs args + c g
  | .callInd _ args _ _ => kostenArgs args
  -- `Sperrt`, `Bricht`: the body
  | .locks _ _ body => kostenKB c body
  | .breaking _ body => kostenKB c body
  -- `Traverse`: body times domain bound
  | .traverse t _ body => (D.count t).toNat * kostenKB c body
  | .consumeTraverse t _ _ _ _ _ body => (D.count t).toNat * kostenKB c body
  | .retry .. => 0
  | .forever .. => 0
  | .axiomCall _ args _ _ _ _ _ => kostenArgs args
  | .regWrite _ _ e => 1 + kostenExpr e
  | .transition .. => 0
  | .publish _ e _ _ _ _ => 1 + kostenExpr e
  | .advances .. => 0
  | .retires .. => 0
  -- `Return(Some e)`: the expression; `Return(None)`, `Leave`, `Next`: `0`
  | .ret e _ => kostenErg e
  | .retWhy .. => 0
  | .retScoped e _ => kostenErg e
  | .retWhyScoped .. => 0
  | .leave _ => 0
  | .next _ => 0

def kostenKB (c : D.Fn → Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Nat
  | .nil => 0
  | .cons s rest => kostenKS c s + kostenKB c rest
  -- `Let`: `1 + ausdruck(wert)`; over a call, the call
  | .bind e rest => 1 + kostenExpr e + kostenKB c rest
  | .bindCall g args _ _ _ rest => 1 + kostenArgs args + c g + kostenKB c rest
  | .bindCallInd _ _ _ _ _ rest => kostenKB c rest
  -- `LetSonst` over a call: `1 + ruf + block(sonst)`, summed
  | .bindCallElse g args _ _ _ err rest =>
      1 + kostenArgs args + c g + kostenKE c err + kostenKB c rest
  | .bindAxiom _ _ _ _ _ _ _ rest => kostenKB c rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => kostenKE c err + kostenKB c rest
  -- `Let x = R`: `1 +` one load
  | .regRead _ _ rest => 2 + kostenKB c rest
  -- `LetSonst` over a place: `1 + 1 + block(sonst)`; the predicate is not read (F4)
  | .regReadElse _ _ _ sonst rest => 2 + kostenKE c sonst + kostenKB c rest
  -- `AwaitLoad`: `1`
  | .awaits _ _ _ _ _ rest => 1 + kostenKB c rest
  -- `Exchange` update: `1 + block(rumpf)`
  | .exchange _ neu _ _ rest => 1 + kostenExpr neu + kostenKB c rest
  -- `Narrow`: `1 + max(0, sonst)`; the subject is not read (F5)
  | .narrow _ _ _ sonst rest => 1 + kostenKE c sonst + kostenKB c rest
  | .narrowRequired _ _ _ rest => 1 + kostenKB c rest
  -- a named refusal: `if !c { sonst }` with an always-leaving arm -- the
  -- two-way rule of `block`: condition plus the maximum
  | .check b sonst rest => kostenExpr b + max (kostenKE c sonst) (kostenKB c rest)
  -- float `let`s: `1 + ausdruck(wert)`
  | .float _ a b _ _ rest => 2 + kostenExpr a + kostenExpr b + kostenKB c rest
  | .floatLit _ _ _ rest => 1 + kostenKB c rest
  | .floatOf e _ _ rest => 2 + kostenExpr e + kostenKB c rest
  | .floatNarrow _ _ _ sonst rest => 1 + kostenKE c sonst + kostenKB c rest

def kostenKArms (c : D.Fn → Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil => 0
  | .cons b rest => max (kostenKB c b) (kostenKArms c rest)

def kostenKGArms (c : D.Fn → Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil => 0
  | .cons b rest => max (kostenKB c b) (kostenKGArms c rest)

def kostenKE (c : D.Fn → Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret e _ => kostenErg e
  | .retWhy .. => 0
  | .retScoped e _ => kostenErg e
  | .retWhyScoped .. => 0
  | .leave _ => 0
  | .next _ => 0
  | .cons s rest => kostenKS c s + kostenKE c rest
  | .bind e rest => 1 + kostenExpr e + kostenKE c rest
  | .bindCall g args _ _ _ rest => 1 + kostenArgs args + c g + kostenKE c rest
  | .bindCallElse g args _ _ _ err rest =>
      1 + kostenArgs args + c g + kostenKE c err + kostenKE c rest
  | .bindAxiom _ _ _ _ _ _ _ rest => kostenKE c rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => kostenKE c err + kostenKE c rest
  | .regRead _ _ rest => 2 + kostenKE c rest
  | .regReadElse _ _ _ sonst rest => 2 + kostenKE c sonst + kostenKE c rest
  | .awaits _ _ _ _ _ rest => 1 + kostenKE c rest
  | .bindCallInd _ _ _ _ _ rest => kostenKE c rest
  | .narrow .. => 0
  | .narrowRequired .. => 0
  | .retScoped e _ => kostenErg e
  | .retWhyScoped .. => 0
  | .exchange .. => 0
  | .ite .. => 0
end
mutual
/-- **The remainder**: G's dispatch steps plus what the checker does not
    read (F1, F4, F5, F6). No callee table: a call's callee cost is the
    same on both sides. -/
def zusatzS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Nat
  | .assignSlot _ _ i _ _ _ => kostenExpr i
  | .assignThru p _ _ _ i _ _ _ => kostenExpr p + kostenExpr i
  | .assignSlotRef r _ _ _ _ _ _ _ => kostenExpr r
  | .assignGlob .. => 0
  | .putBytes _ _ _ _ i _ _ _ _ _ => kostenExpr i
  | .assignVar .. => 0
  | .shift _ _ _ i _ _ _ _ _ _ => kostenExpr i
  | .ite _ t e => 1 + max (zusatzB t) (zusatzB e)
  | .onOption _ p a => 2 + max (zusatzB p) (zusatzB a)
  | .onTag _ arms => 2 + zusatzArms arms
  | .onWhy _ arms => 1 + zusatzGArms arms
  | .call .. => 1
  | .callInd .. => 0
  | .locks _ _ body => 2 + zusatzB body
  | .breaking _ body => 1 + zusatzB body
  | .traverse t inv body => 2 + (D.count t).toNat * (zusatzB body + kostenExpr inv + 2)
  | .consumeTraverse t member edge inv _ mass body =>
      2 + (D.count t).toNat * (zusatzB body + kostenExpr member + kostenExpr edge +
        kostenExpr inv + kostenExpr mass + 2)
  | .retry .. => 0
  | .forever .. => 0
  | .axiomCall .. => 0
  | .regWrite .. => 0
  | .transition .. => 0
  | .publish .. => 0
  | .advances .. => 0
  | .retires .. => 0
  | .ret .. => 1
  | .retWhy .. => 1
  | .retScoped .. => 1
  | .retWhyScoped .. => 1
  | .leave _ => 1
  | .next _ => 1

def zusatzB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Nat
  | .nil => 1
  | .cons s rest => zusatzS s + zusatzB rest
  | .bind _ rest => 1 + zusatzB rest
  | .bindCall _ _ _ _ _ rest => 1 + zusatzB rest
  | .bindCallInd .. => 0
  | .bindCallElse _ _ _ _ _ err rest => 3 + zusatzSonst err + zusatzB rest
  | .bindAxiom .. => 0
  | .bindAxiomElse .. => 0
  | .regRead _ _ rest => zusatzB rest
  | .regReadElse _ _ z sonst rest => 2 + kostenExpr z + zusatzSonst sonst + zusatzB rest
  | .awaits _ _ _ _ _ rest => 1 + zusatzB rest
  | .exchange _ _ _ _ rest => 1 + zusatzB rest
  | .narrow e _ _ sonst rest => 3 + kostenExpr e + zusatzSonst sonst + zusatzB rest
  | .narrowRequired e _ _ rest => 3 + kostenExpr e + zusatzB rest
  | .check _ sonst rest => 1 + max (zusatzSonst sonst + 1) (zusatzB rest)
  | .float _ _ _ _ _ rest => zusatzB rest
  | .floatLit _ _ _ rest => 1 + zusatzB rest
  | .floatOf _ _ _ rest => zusatzB rest
  | .floatNarrow e _ _ sonst rest => 3 + kostenExpr e + zusatzSonst sonst + zusatzB rest

def zusatzArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil => 0
  | .cons b rest => max (zusatzB b) (zusatzArms rest)

def zusatzGArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil => 0
  | .cons b rest => max (zusatzB b) (zusatzGArms rest)

def zusatzE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Nat
  | .ret .. => 1
  | .retWhy .. => 1
  | .retScoped .. => 1
  | .retWhyScoped .. => 1
  | .leave _ => 1
  | .next _ => 1
  | .cons s rest => entfZ s + zusatzS s + zusatzE rest
  | .bind _ rest => zusatzE rest
  | .bindCall _ _ _ _ _ rest => 4 + zusatzSonst rest
  | .bindCallElse _ _ _ _ _ err rest => 6 + zusatzSonst err + zusatzSonst rest
  | .bindAxiom .. => 0
  | .bindAxiomElse .. => 0
  | .regRead _ _ rest => 3 + zusatzSonst rest
  | .regReadElse _ _ z sonst rest => 5 + kostenExpr z + zusatzSonst sonst + zusatzSonst rest
  | .awaits _ _ _ _ _ rest => 4 + zusatzSonst rest
  | .bindCallInd .. => 0
  | .narrow .. => 0
  | .narrowRequired .. => 0
  | .retScoped .. => 1
  | .retWhyScoped .. => 1
  | .exchange .. => 0
  | .ite .. => 0

/-- The remainder of an `else` branch run as a block (`kostenSonst`). -/
def zusatzSonst {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Nat
  | .ret .. => 2
  | .retWhy .. => 2
  | .retScoped .. => 2
  | .retWhyScoped .. => 2
  | .leave _ => 2
  | .next _ => 2
  | .cons s rest => zusatzS s + zusatzSonst rest
  | .bind _ rest => 1 + zusatzSonst rest
  | .bindCall _ _ _ _ _ rest => 1 + zusatzSonst rest
  | .bindCallElse _ _ _ _ _ err rest => 3 + zusatzSonst err + zusatzSonst rest
  | .bindAxiom .. => 0
  | .bindAxiomElse .. => 0
  | .regRead _ _ rest => zusatzSonst rest
  | .regReadElse _ _ z sonst rest => 2 + kostenExpr z + zusatzSonst sonst + zusatzSonst rest
  | .awaits _ _ _ _ _ rest => 1 + zusatzSonst rest
  | .bindCallInd .. => 0
  | .narrow .. => 0
  | .narrowRequired .. => 0
  | .retScoped .. => 2
  | .retWhyScoped .. => 2
  | .exchange .. => 0
  | .ite .. => 0
end

