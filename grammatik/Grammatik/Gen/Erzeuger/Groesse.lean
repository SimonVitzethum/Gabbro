/-
  File:      Grammatik/Gen/Erzeuger/Groesse.lean
  Subject:   The SIZE of the model's expressions, statements, blocks, end blocks, arms, arguments: the measure of
             every completeness statement. Every node counts one; every free number counts what the numeric
             scheme (`Zahlen`) charges for it; every index into an enumeration of the declaration (a table, a
             field, a lock, a function) is a free finite choice and counts nothing, because the declaration is
             finite and the generator takes all of them; what the typing determines (the ranges a sum or a
             product computes, the held resources after a call, a callee's parameter types) counts nothing.
-/
import Grammatik.Gen.Erzeuger.Gestuft

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Zahlen]

/-- The size of a pair of integers. -/
def groessePaar (p : Int × Int) : Nat := Zahlen.kostP p

mutual
def groesseExpr : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}, Expr D Γ Λ τ → Nat
  | _, _, _, .lit n => 1 + Zahlen.kostW n
  | _, _, _, .tru => 1
  | _, _, _, .fls => 1
  | _, _, _, .var x => 1 + groesseVar x
  | _, _, _, .glob _ _ => 1
  | _, _, _, .slot _ _ i _ => 1 + groesseExpr i
  | _, _, _, .thru p _ _ _ i _ => 1 + groesseExpr p + groesseExpr i
  | _, _, _, .ptrOf _ n _ _ => 1 + Zahlen.kostN n
  | _, _, _, .fnref _ _ _ => 1
  | _, _, _, .refStart n => 1 + Zahlen.kostN n
  | _, _, _, .refNext r => 1 + groesseExpr r
  | _, _, _, .refEq a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .slotRef r _ _ _ _ _ => 1 + groesseExpr r
  | _, _, _, .oldG _ _ => 1
  | _, _, _, .oldS _ _ i _ => 1 + groesseExpr i
  | _, _, _, @Expr.widen _ lo' _ _ hi' _ _ _ _ e => 1 + Zahlen.kost lo' + Zahlen.kost hi' + groesseExpr e
  | _, _, _, .add a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .sub a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .neg a => 1 + groesseExpr a
  | _, _, _, .mul a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .div _ _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .rem _ _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .sdiv _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .srem _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .getBytes _ _ _ n i _ _ _ => 1 + Zahlen.kostN n + groesseExpr i
  | _, _, _, .band _ _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .bor w _ _ _ _ a b => 1 + Zahlen.kostN w + groesseExpr a + groesseExpr b
  | _, _, _, .bxor w _ _ _ _ a b => 1 + Zahlen.kostN w + groesseExpr a + groesseExpr b
  | _, _, _, .shl w _ _ _ _ a b => 1 + Zahlen.kostN w + groesseExpr a + groesseExpr b
  | _, _, _, .shr w _ _ _ _ a b => 1 + Zahlen.kostN w + groesseExpr a + groesseExpr b
  | _, _, _, .lt a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .le a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .eq a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .fllt a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .flle a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .and a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .or a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .not a => 1 + groesseExpr a
  | _, _, _, .none n => 1 + Zahlen.kost n
  | _, _, _, @Expr.some _ _ _ n e => 1 + Zahlen.kost n + groesseExpr e
  | _, _, _, .istSome e => 1 + groesseExpr e
  | _, _, _, .case cs _ nutz => 1 + Zahlen.kostS cs + groesseNutz nutz
  | _, _, _, .why n _ => 1 + Zahlen.kostN n
  | _, _, _, .forallSlots _ body _ => 1 + groesseExpr body
  | _, _, _, .existsSlots _ body _ => 1 + groesseExpr body
  | _, _, _, .reaches _ _ _ a b _ => 1 + groesseExpr a + groesseExpr b

def groesseNutz : ∀ {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)}, NutzlastExpr D Γ Λ o → Nat
  | _, _, _, .empty => 1
  | _, _, _, .num e => 1 + groesseExpr e
end

/-- The size of an argument list. -/
def groesseArgs : ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty}, Args D Γ Λ τs → Nat
  | _, _, _, .nil => 1
  | _, _, _, .cons e rest => 1 + groesseExpr e + groesseArgs rest

/-- The size of a result expression. -/
def groesseErg : ∀ {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty}, ErgExpr D Γ Λ o → Nat
  | _, _, _, .empty => 1
  | _, _, _, .val e => 1 + groesseExpr e

variable {V : Vertrag D}

mutual
def groesseStmt : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Stmt D V l Γ Λ Λ' → Nat
  | _, _, _, _, .assignSlot _ _ i e _ _ => 1 + groesseExpr i + groesseExpr e
  | _, _, _, _, .assignThru p _ _ _ i e _ _ => 1 + groesseExpr p + groesseExpr i + groesseExpr e
  | _, _, _, _, .assignSlotRef r _ _ _ _ e _ _ => 1 + groesseExpr r + groesseExpr e
  | _, _, _, _, .assignGlob _ e _ _ => 1 + groesseExpr e
  | _, _, _, _, .putBytes _ _ _ n i _ _ e _ _ => 1 + Zahlen.kostN n + groesseExpr i + groesseExpr e
  | _, _, _, _, .assignVar x e => 1 + groesseVar x + groesseExpr e
  | _, _, _, _, .shift _ _ _ i von nach _ _ _ _ => 1 + groesseExpr i + Zahlen.kost von + Zahlen.kost nach
  | _, _, _, _, .ite c t e => 1 + groesseExpr c + groesseBlock t + groesseBlock e
  | _, _, _, _, .onOption (n := n) o p a => 1 + Zahlen.kostT (Ty.index n) + groesseExpr o + groesseBlock p + groesseBlock a
  | _, _, _, _, .onTag v arms => 1 + groesseExpr v + groesseArms arms
  | _, _, _, _, .onWhy r arms => 1 + groesseExpr r + groesseGrundArms arms
  | _, _, _, _, .call _ args _ _ => 1 + groesseArgs args
  | _, _, _, _, .callInd p args _ _ => 1 + groesseExpr p + groesseArgs args
  | _, _, _, _, .locks _ _ body => 1 + groesseBlock body
  | _, _, _, _, .breaking _ body => 1 + groesseBlock body
  | _, _, _, _, .traverse _ inv body => 1 + groesseExpr inv + groesseBlock body
  | _, _, _, _, .retry n bis body ueb =>
    1 + Zahlen.kostN n + groesseExpr bis + groesseBlock body + groesseBlock ueb
  | _, _, _, _, .forever _ inv body => 1 + groesseExpr inv + groesseBlock body
  | _, _, _, _, .axiomCall _ args _ _ _ _ _ => 1 + groesseArgs args
  | _, _, _, _, .regWrite _ _ e => 1 + groesseExpr e
  | _, _, _, _, .transition _ _ _ _ _ maske bits => 1 + Zahlen.kostW maske + Zahlen.kostW bits
  | _, _, _, _, .publish _ e _ _ _ _ => 1 + groesseExpr e
  | _, _, _, _, .advances _ _ _ _ => 1
  | _, _, _, _, .retires _ _ _ _ => 1
  | _, _, _, _, .ret e _ => 1 + groesseErg e
  | _, _, _, _, .retWhy _ _ => 1
  | _, _, _, _, .leave _ => 1
  | _, _, _, _, .next _ => 1

def groesseBlock : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Block D V l Γ Λ Λ' → Nat
  | _, _, _, _, .nil => 1
  | _, _, _, _, .cons s rest => 1 + groesseStmt s + groesseBlock rest
  | _, _, _, _, .bind (τ := τ) e rest => 1 + Zahlen.kostT τ + groesseExpr e + groesseBlock rest
  | _, _, _, _, .bindCall _ args _ _ _ rest => 1 + groesseArgs args + groesseBlock rest
  | _, _, _, _, .bindCallInd p args _ _ _ rest => 1 + groesseExpr p + groesseArgs args + groesseBlock rest
  | _, _, _, _, .bindCallElse _ args _ _ _ err rest => 1 + groesseArgs args + groesseEnd err + groesseBlock rest
  | _, _, _, _, .bindAxiom _ args _ _ _ _ _ rest => 1 + groesseArgs args + groesseBlock rest
  | _, _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
    1 + groesseArgs args + groesseEnd err + groesseBlock rest
  | _, _, _, _, .regRead _ _ rest => 1 + groesseBlock rest
  | _, _, _, _, .regReadElse _ _ z sonst rest => 1 + groesseExpr z + groesseEnd sonst + groesseBlock rest
  | _, _, _, _, .awaits _ _ _ _ _ rest => 1 + groesseBlock rest
  | _, _, _, _, .exchange _ neu _ _ rest => 1 + groesseExpr neu + groesseBlock rest
  | _, _, _, _, .narrow e lo' hi' sonst rest =>
    1 + groesseExpr e + Zahlen.kost lo' + Zahlen.kost hi' + Zahlen.kostT (.int lo' hi') + groesseEnd sonst +
      groesseBlock rest
  | _, _, _, _, .check c sonst rest => 1 + groesseExpr c + groesseEnd sonst + groesseBlock rest
  | _, _, _, _, .float _ a b lo hi rest =>
    1 + groesseExpr a + groesseExpr b + groessePaar lo + groessePaar hi + Zahlen.kostT (.fl lo hi) + groesseBlock rest
  | _, _, _, _, .floatLit q lo hi rest =>
    1 + groessePaar q + groessePaar lo + groessePaar hi + Zahlen.kostT (.fl lo hi) + groesseBlock rest
  | _, _, _, _, .floatOf e lo hi rest =>
    1 + groesseExpr e + groessePaar lo + groessePaar hi + Zahlen.kostT (.fl lo hi) + groesseBlock rest
  | _, _, _, _, .floatNarrow e lo hi sonst rest =>
    1 + groesseExpr e + groessePaar lo + groessePaar hi + Zahlen.kostT (.fl lo hi) + groesseEnd sonst +
      groesseBlock rest

def groesseEnd : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}, Endblock D V l Γ Λ → Nat
  | _, _, _, .ret e _ => 1 + groesseErg e
  | _, _, _, .retWhy _ _ => 1
  | _, _, _, .leave _ => 1
  | _, _, _, .next _ => 1
  | _, _, _, .cons s rest => 1 + groesseStmt s + groesseEnd rest
  | _, _, _, .bind (τ := τ) e rest => 1 + Zahlen.kostT τ + groesseExpr e + groesseEnd rest
  | _, _, _, .bindCall _ args _ _ _ rest => 1 + groesseArgs args + groesseEnd rest
  | _, _, _, .bindCallElse _ args _ _ _ err rest => 1 + groesseArgs args + groesseEnd err + groesseEnd rest
  | _, _, _, .bindAxiom _ args _ _ _ _ _ rest => 1 + groesseArgs args + groesseEnd rest
  | _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest => 1 + groesseArgs args + groesseEnd err + groesseEnd rest
  | _, _, _, .regRead _ _ rest => 1 + groesseEnd rest
  | _, _, _, .regReadElse _ _ z sonst rest => 1 + groesseExpr z + groesseEnd sonst + groesseEnd rest
  | _, _, _, .awaits _ _ _ _ _ rest => 1 + groesseEnd rest
  | _, _, _, .bindCallInd p args _ _ _ rest => 1 + groesseExpr p + groesseArgs args + groesseEnd rest

def groesseArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))},
    Arms D V l Γ Λ Λ' cs → Nat
  | _, _, _, _, _, .nil => 1
  | _, _, _, _, _, .cons b rest => 1 + groesseBlock b + groesseArms rest

def groesseGrundArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat},
    GrundArms D V l Γ Λ Λ' n → Nat
  | _, _, _, _, _, .nil => 1
  | _, _, _, _, _, .cons b rest => 1 + groesseBlock b + groesseGrundArms rest
end

end Gabbro.Grammatik.Gen
