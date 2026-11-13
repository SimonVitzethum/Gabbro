/-
  File:      stage0/Stage0/Senke/Bild/Gleich/AxFrei.lean
  Subject:   **No foreign call** (package P1 of the closed calls of the image theorem, the oracle split). The oracle is
             consulted in three ways: foreign calls (`Orakel.wirkt`, the forms `axiomCall`, `axiomCallElse`,
             `bindAxiom`, `bindAxiomElse`, `bindAxiomOpt`, `bindAxiomOptElse`), register reads (`Orakel.regLies`) and
             visibility (`Orakel.sichtbar`). The register and visibility answers are read-blind under the named
             hardware assumption `RegLokal` (`Ruf/Hardware.lean`); the foreign answers are read-blind only for a
             read-blind oracle. `axFrei` is the decidable syntactic check "no foreign-call form", so that the
             substitution theorem (`Ersetzung.lean`) needs the foreign half only where a foreign call occurs.
-/
module
public import Grammatik.Kern.Semantik.Semantik
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

mutual

/-- The statement carries no foreign-call form. -/
def Stmt.axFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.axFrei && e.axFrei
  | .onOption _ p a => p.axFrei && a.axFrei
  | .onTag _ arms => arms.axFrei
  | .onWhy _ arms => arms.axFrei
  | .locks _ _ body => body.axFrei
  | .breaking _ body => body.axFrei
  | .traverse _ _ body => body.axFrei
  | .consumeTraverse _ _ _ _ _ _ body => body.axFrei
  | .retry _ _ body ueber => body.axFrei && ueber.axFrei
  | .forever _ _ body => body.axFrei
  | .axiomCall .. => false
  | .axiomCallElse .. => false
  | .callIndElse _ _ _ _ _ err => err.axFrei
  | _ => true

/-- The block carries no foreign-call form. -/
def Block.axFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.axFrei && rest.axFrei
  | .bind _ rest => rest.axFrei
  | .bindCall _ _ _ _ _ rest => rest.axFrei
  | .bindCallInd _ _ _ _ _ rest => rest.axFrei
  | .bindCallIndElse _ _ _ _ _ err rest => err.axFrei && rest.axFrei
  | .bindCallElse _ _ _ _ _ err rest => err.axFrei && rest.axFrei
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .regRead _ _ rest => rest.axFrei
  | .regReadElse _ _ _ sonst rest => sonst.axFrei && rest.axFrei
  | .awaits _ _ _ _ _ rest => rest.axFrei
  | .exchange _ _ _ _ rest => rest.axFrei
  | .narrow _ _ _ sonst rest => sonst.axFrei && rest.axFrei
  | .narrowRequired _ _ _ rest => rest.axFrei
  | .check _ sonst rest => sonst.axFrei && rest.axFrei
  | .float _ _ _ _ _ rest => rest.axFrei
  | .floatLit _ _ _ rest => rest.axFrei
  | .floatOf _ _ _ rest => rest.axFrei
  | .floatNarrow _ _ _ sonst rest => sonst.axFrei && rest.axFrei

/-- The terminal block carries no foreign-call form. -/
def Endblock.axFrei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.axFrei && rest.axFrei
  | .bind _ rest => rest.axFrei
  | .bindCall _ _ _ _ _ rest => rest.axFrei
  | .bindCallElse _ _ _ _ _ err rest => err.axFrei && rest.axFrei
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .regRead _ _ rest => rest.axFrei
  | .regReadElse _ _ _ sonst rest => sonst.axFrei && rest.axFrei
  | .awaits _ _ _ _ _ rest => rest.axFrei
  | .bindCallInd _ _ _ _ _ rest => rest.axFrei
  | .bindCallIndElse _ _ _ _ _ err rest => err.axFrei && rest.axFrei
  | .narrow _ _ _ sonst rest => sonst.axFrei && rest.axFrei
  | .narrowRequired _ _ _ rest => rest.axFrei
  | .exchange _ _ _ _ rest => rest.axFrei
  | .ite _ t e => t.axFrei && e.axFrei
  | .float _ _ _ _ _ rest => rest.axFrei
  | .floatLit _ _ _ rest => rest.axFrei
  | .floatOf _ _ _ rest => rest.axFrei
  | .floatNarrow _ _ _ sonst rest => sonst.axFrei && rest.axFrei

/-- The arms carry no foreign-call form. -/
def Arms.axFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.axFrei && rest.axFrei

/-- The reason arms carry no foreign-call form. -/
def GrundArms.axFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.axFrei && rest.axFrei

end

/-- **A program without foreign calls**: no body carries a foreign-call form. Decidable per program. -/
def FremdFrei (P : Programm D) : Prop :=
  ∀ g : D.Fn, (P.rumpf g).axFrei = true

end Gabbro.Grammatik

namespace Gabbro.Stage0.Senke.BildLauf

/-- The left half of a true conjunction, beside a second alternative. -/
theorem frei_links {a b : Bool} {W : Prop} (h : (a && b) = true ∨ W) : a = true ∨ W := by
  rcases h with h | h
  · left
    cases a <;> cases b <;> simp_all
  · exact Or.inr h

/-- The right half of a true conjunction, beside a second alternative. -/
theorem frei_rechts {a b : Bool} {W : Prop} (h : (a && b) = true ∨ W) : b = true ∨ W := by
  rcases h with h | h
  · left
    cases a <;> cases b <;> simp_all
  · exact Or.inr h

end Gabbro.Stage0.Senke.BildLauf
