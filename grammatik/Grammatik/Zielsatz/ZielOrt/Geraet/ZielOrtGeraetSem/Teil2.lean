module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Mono
variable {K K' : Nat → Bool} {Rg Rg' : D.Reg → Bool} (hKK : ∀ n, K n = true → K' n = true)
include hKK

mutual

theorem Stmt.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.gOk K Rg = true → (∀ r ∈ s.regs, Rg' r = true) →
      s.gOk K' Rg' = true
  | .ite _ t e, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono t h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono e h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .onOption _ p a, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono p h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono a h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .onTag _ arms, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Arms.gOk_mono arms h hr
  | .onWhy _ arms, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact GrundArms.gOk_mono arms h hr
  | .locks _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .breaking _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .traverse _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .consumeTraverse _ _ _ _ _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .retry _ _ body ueber, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono body h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono ueber h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .forever _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .callInd .., h, _ => by
      simp only [Stmt.gOk] at h ⊢
      exact hKK _ h
  | .assignSlot .., _, _ => rfl
  | .assignThru .., _, _ | .assignSlotRef .., _, _ => rfl
  | .assignGlob .., _, _ => rfl
  | .putBytes .., _, _ => rfl
  | .assignVar .., _, _ => rfl
  | .shift .., _, _ => rfl
  | .call .., _, _ => rfl
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

theorem Block.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.gOk K Rg = true → (∀ r ∈ b.regs, Rg' r = true) →
      b.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons s rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Stmt.gOk_mono s h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bind _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .bindCall _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .bindCallInd _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true] at h hr ⊢
      exact ⟨hKK _ h.1, Block.gOk_mono rest h.2 hr⟩
  | .bindCallElse _ _ _ _ _ err rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .regRead r _ rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_cons] at h hr ⊢
      exact ⟨hr r (Or.inl rfl), Block.gOk_mono rest h.2 (fun r' h' => hr r' (Or.inr h'))⟩
  | .regReadElse r _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_cons, List.mem_append]
        at h hr ⊢
      exact ⟨hr r (Or.inl rfl),
        Endblock.gOk_mono sonst h.2.1 (fun r' h' => hr r' (Or.inr (Or.inl h'))),
        Block.gOk_mono rest h.2.2 (fun r' h' => hr r' (Or.inr (Or.inr h')))⟩
  | .awaits _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .exchange _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .narrow _ _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .narrowRequired _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .check _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .float _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .floatLit _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .floatOf _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .floatNarrow _ _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem Endblock.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.gOk K Rg = true → (∀ r ∈ e.regs, Rg' r = true) →
      e.gOk K' Rg' = true
  | .ret .., _, _ => rfl
  | .retWhy .., _, _ => rfl
  | .retScoped .., _, _ => rfl
  | .retWhyScoped .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl
  | .cons s rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Stmt.gOk_mono s h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bind _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindCall _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindCallElse _ _ _ _ _ err rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .regRead r _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_cons] at h hr ⊢
      exact ⟨hr r (Or.inl rfl), Endblock.gOk_mono rest h.2 (fun r' h' => hr r' (Or.inr h'))⟩
  | .regReadElse r _ _ sonst rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_cons, List.mem_append]
        at h hr ⊢
      exact ⟨hr r (Or.inl rfl),
        Endblock.gOk_mono sonst h.2.1 (fun r' h' => hr r' (Or.inr (Or.inl h'))),
        Endblock.gOk_mono rest h.2.2 (fun r' h' => hr r' (Or.inr (Or.inr h')))⟩
  | .awaits _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .bindCallInd _ _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true] at h hr ⊢
      exact ⟨hKK _ h.1, Endblock.gOk_mono rest h.2 hr⟩
  | .narrow _ _ _ sonst rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .narrowRequired _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .exchange _ _ _ _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr
  | .ite _ t e, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono e h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono t h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem Arms.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → a.gOk K Rg = true → (∀ r ∈ a.regs, Rg' r = true) →
      a.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons b rest, h, hr => by
      simp only [Arms.gOk, Arms.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono b h.1 (fun r h' => hr r (Or.inl h')),
        Arms.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem GrundArms.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → a.gOk K Rg = true →
      (∀ r ∈ a.regs, Rg' r = true) → a.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons b rest, h, hr => by
      simp only [GrundArms.gOk, GrundArms.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono b h.1 (fun r h' => hr r (Or.inl h')),
        GrundArms.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

end

end Mono
end Gabbro.Grammatik
