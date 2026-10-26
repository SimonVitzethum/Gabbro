/- Part 2 of 4 of `SperreSem` (split by instrumente/teile/lean-teilen.py; the umbrella `SperreSem.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T1

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
  | .exchange g neu hw hL rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl
  | .ite c t e, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer t, Endblock.execH_leer e] <;> rfl

theorem Arms.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
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
  | .retry _ _ body ueber => body.ohneLocks && ueber.ohneLocks
  | .forever _ _ body => body.ohneLocks
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
  | .regRead _ _ rest => rest.ohneLocks
  | .regReadElse _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .awaits _ _ _ _ _ rest => rest.ohneLocks
  | .exchange _ _ _ _ rest => rest.ohneLocks
  | .narrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .check _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .float _ _ _ _ _ rest => rest.ohneLocks
  | .floatLit _ _ _ rest => rest.ohneLocks
  | .floatOf _ _ _ rest => rest.ohneLocks
  | .floatNarrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks

def Endblock.ohneLocks {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.ohneLocks && rest.ohneLocks
  | .bind _ rest => rest.ohneLocks
  | .bindCall _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallElse _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ohneLocks
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .regRead _ _ rest => rest.ohneLocks
  | .regReadElse _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .awaits _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallInd _ _ _ _ _ rest => rest.ohneLocks
  | .narrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .exchange _ _ _ _ rest => rest.ohneLocks
  | .ite _ t e => t.ohneLocks && e.ohneLocks

def Arms.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
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

mutual

theorem Stmt.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.ohneLocks = true → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtH S O U passes R s σ ρ = execStmt O passes R s σ ρ
  | .ite c t e, h, σ, ρ => by
      simp only [Stmt.ohneLocks, Bool.and_eq_true] at h
      simp only [execStmtH, execStmt, Block.execH_ohne t h.1, Block.execH_ohne e h.2] <;> rfl
  | .onOption o p a, h, σ, ρ => by
      simp only [Stmt.ohneLocks, Bool.and_eq_true] at h
      simp only [execStmtH, execStmt, Block.execH_ohne p h.1, Block.execH_ohne a h.2] <;> rfl
  | .onTag v arms, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      exact Arms.execH_ohne arms h _ _ _
  | .onWhy r arms, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      exact GrundArms.execH_ohne arms h _ _ _
  | .locks .., h, _, _ => by simp [Stmt.ohneLocks] at h
  | .breaking i body, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt, Block.execH_ohne body h]
  | .traverse t inv body, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH S O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_ohne body h σ ρ]
  | .retry n bis body ueber, h, σ, ρ => by
      simp only [Stmt.ohneLocks, Bool.and_eq_true] at h
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH S O U passes R body σ ρ) =
          (fun σ ρ => execBlock O passes R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_ohne body h.1 σ ρ,
        show (fun σ ρ => execBlockH S O U passes R ueber σ ρ) =
          (fun σ ρ => execBlock O passes R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_ohne ueber h.2 σ ρ]
  | .forever a inv body, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH S O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_ohne body h σ ρ]
  | .assignSlot .., _, _, _ => rfl
  | .assignThru .., _, _, _ | .assignSlotRef .., _, _, _ => rfl
  | .assignGlob .., _, _, _ => rfl
  | .putBytes .., _, _, _ => rfl
  | .assignVar .., _, _, _ => rfl
  | .shift .., _, _, _ => rfl
  | .call .., _, _, _ => rfl
  | .callInd .., _, _, _ => rfl
  | .axiomCall .., _, _, _ => rfl
  | .regWrite .., _, _, _ => rfl
  | .transition .., _, _, _ => rfl
  | .publish .., _, _, _ => rfl
  | .advances .., _, _, _ => rfl
  | .retires .., _, _, _ => rfl
  | .ret .., _, _, _ => rfl
  | .retWhy .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl

theorem Block.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.ohneLocks = true → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockH S O U passes R b σ ρ = execBlock O passes R b σ ρ
  | .nil, _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Stmt.execH_ohne s h.1, Block.execH_ohne rest h.2] <;> rfl
  | .bind e rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h]
  | .bindCall f args he hp hr rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .bindCallInd p args he hp hr rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .bindCallElse f args he hp hr err rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne err h.1] <;> rfl
  | .bindAxiom a args he hw hg hd hgd rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne err h.1] <;> rfl
  | .regRead r hk rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .regReadElse r hk zusage sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .awaits g payload hp hL hat rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .exchange g neu hw hL rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h]
  | .narrow e lo' hi' sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .check c sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .float op a b lo hi rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .floatLit q lo hi rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .floatOf e lo hi rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .floatNarrow e lo hi sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl

theorem Endblock.execH_ohne {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.ohneLocks = true → ∀ (σ : World D) (ρ : Env D Γ),
      execEndH S O U passes R b σ ρ = execEnd O passes R b σ ρ
  | .ret .., _, _, _ => rfl
  | .retWhy .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks, Bool.and_eq_true] at h
      simp only [execEndH, execEnd, Stmt.execH_ohne s h.1, Endblock.execH_ohne rest h.2] <;> rfl
  | .bind e rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h]
  | .bindCall f args he hp hr rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h] <;> rfl
  | .bindCallElse f args he hp hr err rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks, Bool.and_eq_true] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h.2, Endblock.execH_ohne err h.1] <;> rfl
  | .bindAxiom a args he hw hg hd hgd rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h] <;> rfl
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks, Bool.and_eq_true] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h.2, Endblock.execH_ohne err h.1] <;> rfl
  | .regRead r hk rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h] <;> rfl
  | .regReadElse r hk zusage sonst rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks, Bool.and_eq_true] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .awaits g payload hp hL hat rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h] <;> rfl
  | .bindCallInd p args he hp hr rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h] <;> rfl
  | .narrow e lo' hi' sonst rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks, Bool.and_eq_true] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .exchange g neu hw hL rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h]
  | .ite c t e, h, σ, ρ => by
      simp only [Endblock.ohneLocks, Bool.and_eq_true] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne t h.1, Endblock.execH_ohne e h.2] <;> rfl

theorem Arms.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → a.ohneLocks = true →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsH S O U passes R a v σ ρ = execArms O passes R a v σ ρ
  | .nil, _, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, h, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      simp only [Arms.ohneLocks, Bool.and_eq_true] at h
      simp only [execArmsH, execArms, Block.execH_ohne b h.1]
  | .cons _ rest, h, ⟨⟨i + 1, hi⟩, nutz⟩, σ, ρ => by
      simp only [Arms.ohneLocks, Bool.and_eq_true] at h
      simp only [execArmsH, execArms]
      exact Arms.execH_ohne rest h.2 _ σ ρ

theorem GrundArms.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → a.ohneLocks = true → ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrundH S O U passes R a r σ ρ = execGrund O passes R a r σ ρ
  | .nil, _, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, h, ⟨0, _⟩, σ, ρ => by
      simp only [GrundArms.ohneLocks, Bool.and_eq_true] at h
      simp only [execGrundH, execGrund, Block.execH_ohne b h.1]
  | .cons _ rest, h, ⟨i + 1, hi⟩, σ, ρ => by
      simp only [GrundArms.ohneLocks, Bool.and_eq_true] at h
      simp only [execGrundH, execGrund]
      exact GrundArms.execH_ohne rest h.2 _ σ ρ

end

end Ohne
/-- **A leaf means the same in both semantics** (a leaf contains no `locks`). -/
theorem execStmtH_blatt (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (σ : World D) (ρ : Env D Γ) :
    execStmtH S O U passes R s σ ρ = execStmt O passes R s σ ρ := by
  cases s <;> first | rfl | (simp [Stmt.istBlatt] at hb)

/-! ## 2a. Frame results WITH the reason channel

  `ZErg` (`ZielOrtSem.lean`) knows a return, a `logik` outcome and
  "anything else": a REASON exit (`retGrund`) of the frame's own function
  was `sonst`, so the replay said nothing about the world at a reason
  return. `ZErgG` adds `grund σ r` (2026-09-14, for the invariants owed at
  reason returns, `ZielOrtInvGrund.lean`); the lock-invariant replay
  (`semH`, `KopfS`) predicts in `ZErgG`, the older replays keep `ZErg`. -/

/-- What a frame's residue still produces: a return, a reason exit, a logic
    failure, or anything else. -/
inductive ZErgG (V : Vertrag D) where
  | zurueck (σ : World D) (v : ErgVal D V.erg)
  | why (σ : World D) (r : Fin V.gruende)
  | logik (e : Logik D)
  | sonst

namespace ZErgG

variable {V : Vertrag D}

/-- Frame results that agree up to the trace. -/
def gleich : ZErgG V → ZErgG V → Prop
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .why σ r, .why σ' r' => SG σ σ' ∧ r = r'
  | .logik e, .logik e' => e = e'
  | .sonst, .sonst => True
  | _, _ => False

theorem gleich_refl (r : ZErgG V) : r.gleich r := by
  cases r <;> simp [gleich, SG]

theorem gleich_symm {r r' : ZErgG V} (h : r.gleich r') : r'.gleich r := by
  cases r <;> cases r' <;> simp_all [gleich, SG]

theorem gleich_trans {r r' r'' : ZErgG V} (h1 : r.gleich r') (h2 : r'.gleich r'') :
    r.gleich r'' := by
  cases r <;> cases r' <;> cases r'' <;> simp_all [gleich, SG]

theorem gleich_of_eq {r r' : ZErgG V} (h : r = r') : r.gleich r' := by
  subst h; exact gleich_refl _

/-- `a.folgt b`: the result `a` is predicted by `b` -- `b` predicts nothing
    (`sonst`), or `a` agrees with `b` up to the trace. -/
def folgt (a b : ZErgG V) : Prop := b = .sonst ∨ a.gleich b

theorem folgt_refl (a : ZErgG V) : a.folgt a := Or.inr (gleich_refl a)

theorem folgt_of_gleich {a b : ZErgG V} (h : a.gleich b) : a.folgt b := Or.inr h

theorem folgt_of_eq {a b : ZErgG V} (h : a = b) : a.folgt b := by subst h; exact folgt_refl a

theorem folgt_sonst (a : ZErgG V) : a.folgt .sonst := Or.inl rfl

theorem gleich_sonst_links {b : ZErgG V} (h : gleich .sonst b) : b = .sonst := by
  cases b <;> simp_all [gleich]

theorem folgt_trans {a b c : ZErgG V} (h1 : a.folgt b) (h2 : b.folgt c) : a.folgt c := by
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · rcases h1 with h1 | h1
    · subst h1
      exact Or.inl (gleich_sonst_links h2)
    · exact Or.inr (gleich_trans h1 h2)

theorem folgt_zurueck {a : ZErgG V} {σ : World D} {v : ErgVal D V.erg}
    (h : a.folgt (.zurueck σ v)) : a.gleich (.zurueck σ v) := by
  rcases h with h | h
  · cases h
  · exact h

theorem folgt_grund {a : ZErgG V} {σ : World D} {r : Fin V.gruende}
    (h : a.folgt (.why σ r)) : a.gleich (.why σ r) := by
  rcases h with h | h
  · cases h
  · exact h

theorem folgt_logik {a : ZErgG V} {e : Logik D} (h : a.folgt (.logik e)) :
    a.gleich (.logik e) := by
  rcases h with h | h
  · cases h
  · exact h

end ZErgG
/-- The frame result of an end outcome, reasons kept. -/
def zErgG {V : Vertrag D} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → ZErgG V
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
  | .logik e => .logik e
  | _ => .sonst

theorem zErgG_schrumpf {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    (o : EndAusgang V l (τ :: Γ)) : zErgG o.schrumpf = zErgG o := by
  cases o <;> rfl

theorem zErgG_gleich_logik {V : Vertrag D} {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {e : Logik D} (h : (zErgG o).gleich (.logik e)) : o = .logik e := by
  cases o <;> simp_all [zErgG, ZErgG.gleich]

theorem zErgG_gleich_zurueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {σ : World D} {v : ErgVal D V.erg} (h : (zErgG o).gleich (.zurueck σ v)) :
    ∃ σ', o = .zurueck σ' v ∧ SG σ' σ := by
  cases o with
  | zurueck σ' v' =>
      obtain ⟨hs, hv⟩ := h
      subst hv
      exact ⟨σ', rfl, hs⟩
  | _ => simp [zErgG, ZErgG.gleich] at h


end Gabbro.Grammatik
