/-
  File:      Grammatik/Gen/Erzeuger/Groesse.lean
  Subject:   The SIZE of the model's statements, blocks, end blocks, arms, arguments (the measure of the
             completeness statement). Every node counts one; every free number (a bound, a count, a transition
             endpoint, a retry budget) counts its magnitude; what the typing determines (the held resources
             after a call, a callee's parameter types) counts nothing, because it is read off the declaration.
-/
import Grammatik.Gen.Erzeuger.Ausdruck

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The magnitude of a pair of integers. -/
def groessePaar (p : Int × Int) : Nat := p.1.natAbs + p.2.natAbs

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
  | _, _, _, _, .assignGlob _ e _ _ => 1 + groesseExpr e
  | _, _, _, _, .putBytes _ _ _ n i _ _ e _ _ => 1 + n + groesseExpr i + groesseExpr e
  | _, _, _, _, .assignVar x e => 1 + groesseVar x + groesseExpr e
  | _, _, _, _, .shift _ _ _ i von nach _ _ _ _ => 1 + groesseExpr i + von.natAbs + nach.natAbs
  | _, _, _, _, .ite c t e => 1 + groesseExpr c + groesseBlock t + groesseBlock e
  | _, _, _, _, .onOption o p a => 1 + groesseExpr o + groesseBlock p + groesseBlock a
  | _, _, _, _, .onTag v arms => 1 + groesseExpr v + groesseArms arms
  | _, _, _, _, .onWhy r arms => 1 + groesseExpr r + groesseGrundArms arms
  | _, _, _, _, .call _ args _ _ => 1 + groesseArgs args
  | _, _, _, _, .callInd p args _ _ => 1 + groesseExpr p + groesseArgs args
  | _, _, _, _, .locks _ _ body => 1 + groesseBlock body
  | _, _, _, _, .breaking _ body => 1 + groesseBlock body
  | _, _, _, _, .traverse _ inv body => 1 + groesseExpr inv + groesseBlock body
  | _, _, _, _, .retry n bis body ueb => 1 + n + groesseExpr bis + groesseBlock body + groesseBlock ueb
  | _, _, _, _, .forever _ inv body => 1 + groesseExpr inv + groesseBlock body
  | _, _, _, _, .axiomCall _ args _ _ _ _ _ => 1 + groesseArgs args
  | _, _, _, _, .regWrite _ _ e => 1 + groesseExpr e
  | _, _, _, _, .transition _ _ _ _ _ maske bits => 1 + maske.natAbs + bits.natAbs
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
  | _, _, _, _, .bind e rest => 1 + groesseExpr e + groesseBlock rest
  | _, _, _, _, .bindCall _ args _ _ _ rest => 1 + groesseArgs args + groesseBlock rest
  | _, _, _, _, .bindCallInd p args _ _ _ rest => 1 + groesseExpr p + groesseArgs args + groesseBlock rest
  | _, _, _, _, .bindCallElse _ args _ _ _ err rest => 1 + groesseArgs args + groesseEnd err + groesseBlock rest
  | _, _, _, _, .bindAxiom _ args _ _ _ _ _ rest => 1 + groesseArgs args + groesseBlock rest
  | _, _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
    1 + groesseArgs args + groesseEnd err + groesseBlock rest
  | _, _, _, _, .regRead _ _ rest => 1 + groesseBlock rest
  | _, _, _, _, .regReadElse _ _ z sonst rest => 1 + groesseExpr z + groesseEnd sonst + groesseBlock rest
  | _, _, _, _, .awaits _ _ _ _ rest => 1 + groesseBlock rest
  | _, _, _, _, .exchange _ neu _ _ rest => 1 + groesseExpr neu + groesseBlock rest
  | _, _, _, _, .narrow e lo' hi' sonst rest =>
    1 + groesseExpr e + lo'.natAbs + hi'.natAbs + groesseEnd sonst + groesseBlock rest
  | _, _, _, _, .check c sonst rest => 1 + groesseExpr c + groesseEnd sonst + groesseBlock rest
  | _, _, _, _, .float _ a b lo hi rest =>
    1 + groesseExpr a + groesseExpr b + groessePaar lo + groessePaar hi + groesseBlock rest
  | _, _, _, _, .floatLit q lo hi rest => 1 + groessePaar q + groessePaar lo + groessePaar hi + groesseBlock rest
  | _, _, _, _, .floatOf e lo hi rest => 1 + groesseExpr e + groessePaar lo + groessePaar hi + groesseBlock rest
  | _, _, _, _, .floatNarrow e lo hi sonst rest =>
    1 + groesseExpr e + groessePaar lo + groessePaar hi + groesseEnd sonst + groesseBlock rest

def groesseEnd : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}, Endblock D V l Γ Λ → Nat
  | _, _, _, .ret e _ => 1 + groesseErg e
  | _, _, _, .retWhy _ _ => 1
  | _, _, _, .leave _ => 1
  | _, _, _, .next _ => 1
  | _, _, _, .cons s rest => 1 + groesseStmt s + groesseEnd rest
  | _, _, _, .bind e rest => 1 + groesseExpr e + groesseEnd rest
  | _, _, _, .bindCall _ args _ _ _ rest => 1 + groesseArgs args + groesseEnd rest
  | _, _, _, .bindAxiom _ args _ _ _ _ _ rest => 1 + groesseArgs args + groesseEnd rest
  | _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest => 1 + groesseArgs args + groesseEnd err + groesseEnd rest

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
