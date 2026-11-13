/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Ziele.lean
  Subject:   Package P1 of the closed calls of the image theorem, part 4: what the substitution proves for each
             syntactic class (`StmtLG`, `BlockLG`, `EndeLG`, `ArmsLG`, `GrundLG`: the two runs under `R₁` and `R₂`
             from `≈` worlds and the same environment have related outcomes), and, per constructor, what it needs of
             the direct sub-terms (`StmtKinder`, `BlockKinder`, `EndeKinder`). The case proofs (`Faelle*.lean`) take
             the children's statements as premises; the mutual recursion (`Ersetzung.lean`) supplies them. The
             arm lists are closed here.
-/
module
public import Stage0.Senke.Bild.Gleich.Verbrauch
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

section Ziele

variable (O : Orakel D) (passes : Nat) (Er : Fehlermarke D → Prop)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

/-- A statement under the two handlers, from `≈` worlds. -/
def StmtLG {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : Prop :=
  ∀ (σ₁ σ₂ : World D) (ρ : Env D Γ), WeltGleich σ₁ σ₂ →
    AusLG Er (execStmt O passes R₁ s σ₁ ρ) (execStmt O passes R₂ s σ₂ ρ)

/-- A block under the two handlers, from `≈` worlds. -/
def BlockLG {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ₁ σ₂ : World D) (ρ : Env D Γ), WeltGleich σ₁ σ₂ →
    AusLG Er (execBlock O passes R₁ b σ₁ ρ) (execBlock O passes R₂ b σ₂ ρ)

/-- A terminal block under the two handlers, from `≈` worlds. -/
def EndeLG {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) : Prop :=
  ∀ (σ₁ σ₂ : World D) (ρ : Env D Γ), WeltGleich σ₁ σ₂ →
    EndLG Er (execEnd O passes R₁ b σ₁ ρ) (execEnd O passes R₂ b σ₂ ρ)

/-- Tag arms under the two handlers, for every tag value, from `≈` worlds. -/
def ArmsLG {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (a : Arms D V l Γ Λ Λ' cs) : Prop :=
  ∀ (v : Wert D (.sum cs)) (σ₁ σ₂ : World D) (ρ : Env D Γ), WeltGleich σ₁ σ₂ →
    AusLG Er (execArms O passes R₁ a v σ₁ ρ) (execArms O passes R₂ a v σ₂ ρ)

/-- Reason arms under the two handlers, for every reason, from `≈` worlds. -/
def GrundLG {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} (a : GrundArms D V l Γ Λ Λ' n) : Prop :=
  ∀ (r : Fin n) (σ₁ σ₂ : World D) (ρ : Env D Γ), WeltGleich σ₁ σ₂ →
    AusLG Er (execGrund O passes R₁ a r σ₁ ρ) (execGrund O passes R₂ a r σ₂ ρ)

/-- What a statement's case needs of its direct sub-terms. -/
@[reducible] def StmtKinder {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Prop
  | .ite _ t e => BlockLG O passes Er R₁ R₂ t ∧ BlockLG O passes Er R₁ R₂ e
  | .onOption _ p a => BlockLG O passes Er R₁ R₂ p ∧ BlockLG O passes Er R₁ R₂ a
  | .onTag _ arms => ArmsLG O passes Er R₁ R₂ arms
  | .onWhy _ arms => GrundLG O passes Er R₁ R₂ arms
  | .locks _ _ body => BlockLG O passes Er R₁ R₂ body
  | .breaking _ body => BlockLG O passes Er R₁ R₂ body
  | .traverse _ _ body => BlockLG O passes Er R₁ R₂ body
  | .consumeTraverse _ _ _ _ _ _ body => BlockLG O passes Er R₁ R₂ body
  | .retry _ _ body u => BlockLG O passes Er R₁ R₂ body ∧ BlockLG O passes Er R₁ R₂ u
  | .forever _ _ body => BlockLG O passes Er R₁ R₂ body
  | .axiomCallElse _ _ _ _ _ _ _ _ err => EndeLG O passes Er R₁ R₂ err
  | .callIndElse _ _ _ _ _ err => EndeLG O passes Er R₁ R₂ err
  | _ => True

/-- What a block's case needs of its direct sub-terms. -/
@[reducible] def BlockKinder {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Prop
  | .nil => True
  | .cons s rest => StmtLG O passes Er R₁ R₂ s ∧ BlockLG O passes Er R₁ R₂ rest
  | .bind _ rest => BlockLG O passes Er R₁ R₂ rest
  | .bindCall _ _ _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .bindCallInd _ _ _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .bindCallElse _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ BlockLG O passes Er R₁ R₂ rest
  | .bindAxiom _ _ _ _ _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ BlockLG O passes Er R₁ R₂ rest
  | .regRead _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .regReadElse _ _ _ sonst rest => EndeLG O passes Er R₁ R₂ sonst ∧ BlockLG O passes Er R₁ R₂ rest
  | .awaits _ _ _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .exchange _ _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .narrow _ _ _ sonst rest => EndeLG O passes Er R₁ R₂ sonst ∧ BlockLG O passes Er R₁ R₂ rest
  | .check _ sonst rest => EndeLG O passes Er R₁ R₂ sonst ∧ BlockLG O passes Er R₁ R₂ rest
  | .float _ _ _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .floatLit _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .floatOf _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .floatNarrow _ _ _ sonst rest => EndeLG O passes Er R₁ R₂ sonst ∧ BlockLG O passes Er R₁ R₂ rest
  | .narrowRequired _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => BlockLG O passes Er R₁ R₂ rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ BlockLG O passes Er R₁ R₂ rest
  | .bindCallIndElse _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ BlockLG O passes Er R₁ R₂ rest

/-- What a terminal block's case needs of its direct sub-terms. -/
@[reducible] def EndeKinder {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Prop
  | .cons s rest => StmtLG O passes Er R₁ R₂ s ∧ EndeLG O passes Er R₁ R₂ rest
  | .bind _ rest => EndeLG O passes Er R₁ R₂ rest
  | .bindCall _ _ _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .bindCallElse _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ EndeLG O passes Er R₁ R₂ rest
  | .bindAxiom _ _ _ _ _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ EndeLG O passes Er R₁ R₂ rest
  | .regRead _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .regReadElse _ _ _ sonst rest => EndeLG O passes Er R₁ R₂ sonst ∧ EndeLG O passes Er R₁ R₂ rest
  | .awaits _ _ _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .bindCallInd _ _ _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .narrow _ _ _ sonst rest => EndeLG O passes Er R₁ R₂ sonst ∧ EndeLG O passes Er R₁ R₂ rest
  | .exchange _ _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .ite _ t e => EndeLG O passes Er R₁ R₂ t ∧ EndeLG O passes Er R₁ R₂ e
  | .narrowRequired _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ EndeLG O passes Er R₁ R₂ rest
  | .bindCallIndElse _ _ _ _ _ err rest => EndeLG O passes Er R₁ R₂ err ∧ EndeLG O passes Er R₁ R₂ rest
  | .float _ _ _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .floatLit _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .floatOf _ _ _ rest => EndeLG O passes Er R₁ R₂ rest
  | .floatNarrow _ _ _ sonst rest => EndeLG O passes Er R₁ R₂ sonst ∧ EndeLG O passes Er R₁ R₂ rest
  | _ => True

end Ziele

/-! ## The arm lists -/

section Arme

variable {O : Orakel D} {passes : Nat} {Er : Fehlermarke D → Prop}
  {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {V : Vertrag D}
  {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

theorem arms_nil_lg : ArmsLG O passes Er R₁ R₂ (Arms.nil : Arms D V l Γ Λ Λ []) := by
  intro v
  obtain ⟨⟨k, hk⟩, _⟩ := v
  exact (Nat.not_lt_zero k hk).elim

theorem arms_cons_lg {c : Option Ty} {cs : List (Option Ty)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {rest : Arms D V l Γ Λ Λ' cs} (ihb : BlockLG O passes Er R₁ R₂ b) (ihr : ArmsLG O passes Er R₁ R₂ rest) :
    ArmsLG O passes Er R₁ R₂ (Arms.cons b rest) := by
  intro v σ₁ σ₂ ρ h
  match v with
  | ⟨⟨0, _⟩, nutz⟩ =>
      simp only [execArms]
      exact (ihb _ _ _ h).schrumpfArm
  | ⟨⟨i + 1, hi⟩, nutz⟩ =>
      simp only [execArms]
      exact ihr _ _ _ _ h

theorem grund_nil_lg : GrundLG O passes Er R₁ R₂ (GrundArms.nil : GrundArms D V l Γ Λ Λ 0) := by
  intro r
  exact r.elim0

theorem grund_cons_lg {n : Nat} {b : Block D V l Γ Λ Λ'} {rest : GrundArms D V l Γ Λ Λ' n}
    (ihb : BlockLG O passes Er R₁ R₂ b) (ihr : GrundLG O passes Er R₁ R₂ rest) :
    GrundLG O passes Er R₁ R₂ (GrundArms.cons b rest) := by
  intro r σ₁ σ₂ ρ h
  match r with
  | ⟨0, _⟩ =>
      simp only [execGrund]
      exact ihb _ _ _ h
  | ⟨i + 1, hi⟩ =>
      simp only [execGrund]
      exact ihr _ _ _ _ h

end Arme

end Gabbro.Stage0.Senke.BildLauf
