module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Leer

set_option linter.unusedSectionVars false

variable (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  (hU : ∀ L σ, U L σ = σ)
include hU

mutual

theorem Stmt.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtH (SperrInv.leer D) O U passes R s σ ρ = execStmt O passes R s σ ρ
  | .ite c t e, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer t, Block.execH_leer e] <;> rfl
  | .onOption o p a, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer p, Block.execH_leer a] <;> rfl
  | .onTag v arms, σ, ρ => by
      simp only [execStmtH, execStmt, Arms.execH_leer arms] <;> rfl
  | .onWhy r arms, σ, ρ => by
      simp only [execStmtH, execStmt]
      exact GrundArms.execH_leer arms _ _ _
  | .locks L hr body, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer body, hU, freiH_leer] <;> rfl
  | .breaking i body, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer body] <;> rfl
  | .traverse t inv body, σ, ρ => by
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_leer body σ ρ]
  | .consumeTraverse t member edge inv bound mass body, σ, ρ => by
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_leer body σ ρ]
  | .retry n bis body ueber, σ, ρ => by
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R body σ ρ) =
          (fun σ ρ => execBlock O passes R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_leer body σ ρ,
        show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R ueber σ ρ) =
          (fun σ ρ => execBlock O passes R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_leer ueber σ ρ]
  | .forever a inv body, σ, ρ => by
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_leer body σ ρ]
  | .assignSlot .., _, _ => rfl
  | .assignThru .., _, _ | .assignSlotRef .., _, _ => rfl
  | .assignGlob .., _, _ => rfl
  | .putBytes .., _, _ => rfl
  | .assignVar .., _, _ => rfl
  | .shift .., _, _ => rfl
  | .call .., _, _ => rfl
  | .callInd .., _, _ => rfl
  | .axiomCall .., _, _ => rfl
  | .regWrite .., _, _ => rfl
  | .transition .., _, _ => rfl
  | .publish .., _, _ => rfl
  | .advances .., _, _ => rfl
  | .retires .., _, _ => rfl
  | .ret .., _, _ => rfl
  | .retWhy .., _, _ => rfl
  | .retScoped .., _, _ => rfl
  | .retWhyScoped .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl

theorem Block.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockH (SperrInv.leer D) O U passes R b σ ρ = execBlock O passes R b σ ρ
  | .nil, _, _ => rfl
  | .cons s rest, σ, ρ => by
      simp only [execBlockH, execBlock, Stmt.execH_leer s, Block.execH_leer rest] <;> rfl
  | .bind e rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindCall f args he hp hr rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindCallElse f args he hp hr err rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer err] <;> rfl
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer err] <;> rfl
  | .bindAxiomOpt e a args he _ _ _ rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindAxiomOptElse e a args he _ _ _ _ err rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer err] <;> rfl
  | .regRead r hk rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .regReadElse r hk zusage sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .awaits g payload hp hL hat rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .exchange g neu hw hL rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .narrowRequired e lo' hi' rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .check c sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .float op a b lo hi rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .floatLit q lo hi rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .floatOf e lo hi rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .floatNarrow e lo hi sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl

theorem Endblock.execH_leer {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → ∀ (σ : World D) (ρ : Env D Γ),
      execEndH (SperrInv.leer D) O U passes R b σ ρ = execEnd O passes R b σ ρ
  | .ret .., _, _ => rfl
  | .retWhy .., _, _ => rfl
  | .retScoped .., _, _ => rfl
  | .retWhyScoped .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl
  | .cons s rest, σ, ρ => by
      simp only [execEndH, execEnd, Stmt.execH_leer s, Endblock.execH_leer rest] <;> rfl
  | .bind e rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .bindCall f args he hp hr rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .bindCallElse f args he hp hr err rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest, Endblock.execH_leer err] <;> rfl
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest, Endblock.execH_leer err] <;> rfl
  | .bindAxiomOpt e a args he _ _ _ rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .bindAxiomOptElse e a args he _ _ _ _ err rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest, Endblock.execH_leer err] <;> rfl
  | .regRead r hk rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .regReadElse r hk zusage sonst rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .awaits g payload hp hL hat rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .narrowRequired e lo' hi' rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .exchange g neu hw hL rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .ite c t e, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer t, Endblock.execH_leer e] <;> rfl

theorem Arms.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsH (SperrInv.leer D) O U passes R a v σ ρ = execArms O passes R a v σ ρ
  | .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      simp only [execArmsH, execArms, Block.execH_leer b] <;> rfl
  | .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ => by
      simp only [execArmsH, execArms]
      exact Arms.execH_leer rest _ σ ρ

theorem GrundArms.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrundH (SperrInv.leer D) O U passes R a r σ ρ = execGrund O passes R a r σ ρ
  | .nil, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨0, _⟩, σ, ρ => by
      simp only [execGrundH, execGrund, Block.execH_leer b] <;> rfl
  | .cons _ rest, ⟨i + 1, h⟩, σ, ρ => by
      simp only [execGrundH, execGrund]
      exact GrundArms.execH_leer rest _ σ ρ

end

end Leer
/-! ### A body without `locks` means the same in both semantics -/

section Ohne

variable {V : Vertrag D}

mutual

/-- The statement contains no `locks` block. -/
def Stmt.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ohneLocks && e.ohneLocks
  | .onOption _ p a => p.ohneLocks && a.ohneLocks
  | .onTag _ arms => arms.ohneLocks
  | .onWhy _ arms => arms.ohneLocks
  | .locks .. => false
  | .breaking _ body => body.ohneLocks
  | .traverse _ _ body => body.ohneLocks
  | .consumeTraverse _ _ _ _ _ _ body => body.ohneLocks
  | .retry _ _ body ueber => body.ohneLocks && ueber.ohneLocks
  | .forever _ _ body => body.ohneLocks
  | .axiomCallElse _ _ _ _ _ _ _ _ err => err.ohneLocks
  | _ => true

def Block.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ohneLocks && rest.ohneLocks
  | .bind _ rest => rest.ohneLocks
  | .bindCall _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallInd _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallElse _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ohneLocks
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rest.ohneLocks
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .regRead _ _ rest => rest.ohneLocks
  | .regReadElse _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .awaits _ _ _ _ _ rest => rest.ohneLocks
  | .exchange _ _ _ _ rest => rest.ohneLocks
  | .narrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .narrowRequired _ _ _ rest => rest.ohneLocks
  | .check _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .float _ _ _ _ _ rest => rest.ohneLocks
  | .floatLit _ _ _ rest => rest.ohneLocks
  | .floatOf _ _ _ rest => rest.ohneLocks
  | .floatNarrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks

def Endblock.ohneLocks {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.ohneLocks && rest.ohneLocks
  | .bind _ rest => rest.ohneLocks
  | .bindCall _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallElse _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ohneLocks
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rest.ohneLocks
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .regRead _ _ rest => rest.ohneLocks
  | .regReadElse _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .awaits _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallInd _ _ _ _ _ rest => rest.ohneLocks
  | .narrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .narrowRequired _ _ _ rest => rest.ohneLocks
  | .exchange _ _ _ _ rest => rest.ohneLocks
  | .ite _ t e => t.ohneLocks && e.ohneLocks

def Arms.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ohneLocks && rest.ohneLocks

def GrundArms.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ohneLocks && rest.ohneLocks

end

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

end Ohne
end Gabbro.Grammatik
