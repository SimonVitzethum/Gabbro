module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section AusAlt
variable {K : Nat → Bool}

mutual

theorem Stmt.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.kOk = true → s.vOk K = true
  | .ite _ t e, h => by
      simp only [Stmt.kOk, Stmt.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk t h.1, Block.vOk_of_kOk e h.2⟩
  | .onOption _ p a, h => by
      simp only [Stmt.kOk, Stmt.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk p h.1, Block.vOk_of_kOk a h.2⟩
  | .onTag _ arms, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact Arms.vOk_of_kOk arms h
  | .onWhy _ arms, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact GrundArms.vOk_of_kOk arms h
  | .locks _ _ body, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact Block.vOk_of_kOk body h
  | .breaking _ body, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact Block.vOk_of_kOk body h
  | .traverse .., h => by simp only [Stmt.kOk, Bool.false_eq_true] at h
  | .consumeTraverse .., h => by simp only [Stmt.kOk, Bool.false_eq_true] at h
  | .retry .., h => by simp only [Stmt.kOk, Bool.false_eq_true] at h
  | .forever .., h => by simp only [Stmt.kOk, Bool.false_eq_true] at h
  | .callInd .., h => by simp only [Stmt.kOk, Bool.false_eq_true] at h
  | .callIndElse .., h => by simp only [Stmt.kOk, Bool.false_eq_true] at h
  | .assignSlot .., _ => rfl
  | .assignThru .., _ | .assignThruOwn .., _ | .assignSlotRef .., _ => rfl
  | .assignGlob .., _ => rfl
  | .putBytes .., _ => rfl
  | .assignVar .., _ => rfl
  | .shift .., _ => rfl
  | .call .., _ => rfl
  | .axiomCall .., _ => rfl
  | .regWrite .., _ => rfl
  | .transition .., _ => rfl
  | .publish .., _ => rfl
  | .advances .., _ => rfl
  | .retires .., _ => rfl
  | .ret .., _ => rfl
  | .retWhy .., _ => rfl
  | .retScoped .., _ => rfl
  | .retWhyScoped .., h => by simp only [Stmt.kOk, Endblock.kOk, Bool.false_eq_true] at h
  | .leave .., _ => rfl
  | .next .., _ => rfl

theorem Block.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.kOk = true → b.vOk K = true
  | .nil, _ => rfl
  | .cons s rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_of_kOk s h.1, Block.vOk_of_kOk rest h.2⟩
  | .bind _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .bindCall _ _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .bindCallInd .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .bindCallIndElse .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .bindCallElse .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .bindAxiom .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .bindAxiomElse .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .regRead .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .regReadElse .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .awaits .., h => by simp only [Block.kOk, Bool.false_eq_true] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩
  | .narrowRequired _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .check _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩
  | .float _ _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .floatLit _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .floatOf _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩

theorem Endblock.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.kOk = true → e.vOk K = true
  | .ret .., _ => rfl
  | .retWhy .., _ => rfl
  | .retScoped .., _ => rfl
  | .retWhyScoped .., h => by simp only [Stmt.kOk, Endblock.kOk, Bool.false_eq_true] at h
  | .leave .., _ => rfl
  | .next .., _ => rfl
  | .cons s rest, h => by
      simp only [Endblock.kOk, Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_of_kOk s h.1, Endblock.vOk_of_kOk rest h.2⟩
  | .bind _ rest, h => by
      simp only [Endblock.kOk, Endblock.vOk] at h ⊢
      exact Endblock.vOk_of_kOk rest h
  | .bindCall _ _ _ _ _ rest, h => by
      simp only [Endblock.kOk, Endblock.vOk] at h ⊢
      exact Endblock.vOk_of_kOk rest h
  | .bindAxiom .., h => by simp only [Endblock.kOk, Bool.false_eq_true] at h
  | .bindAxiomElse .., h => by simp only [Endblock.kOk, Bool.false_eq_true] at h
  | .regRead .., h => by simp only [Endblock.kOk, Bool.false_eq_true] at h
  | .regReadElse .., h => by simp only [Endblock.kOk, Bool.false_eq_true] at h
  | .awaits .., h => by simp only [Endblock.kOk, Bool.false_eq_true] at h
  | .bindCallInd .., h => by simp only [Endblock.kOk, Bool.false_eq_true] at h
  | .bindCallIndElse .., h => by simp only [Endblock.kOk, Bool.false_eq_true] at h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Endblock.kOk, Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Endblock.vOk_of_kOk rest h.2⟩
  | .narrowRequired _ _ _ rest, h => by
      simp only [Endblock.kOk, Endblock.vOk] at h ⊢
      exact Endblock.vOk_of_kOk rest h
  | .exchange _ _ _ _ rest, h => by
      simp only [Endblock.kOk, Endblock.vOk] at h ⊢
      exact Endblock.vOk_of_kOk rest h
  | .ite _ t e, h => by
      simp only [Endblock.kOk, Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk e h.2, Endblock.vOk_of_kOk t h.1⟩

theorem Arms.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → a.kOk = true → a.vOk K = true
  | .nil, _ => rfl
  | .cons b rest, h => by
      simp only [Arms.kOk, Arms.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk b h.1, Arms.vOk_of_kOk rest h.2⟩

theorem GrundArms.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → a.kOk = true → a.vOk K = true
  | .nil, _ => rfl
  | .cons b rest, h => by
      simp only [GrundArms.kOk, GrundArms.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk b h.1, GrundArms.vOk_of_kOk rest h.2⟩

end

end AusAlt
/-- The old fragment check implies the new one. -/
theorem programmImFragmentV_of (P : Programm D) (fs : List D.Fn)
    (h : programmImFragment P fs = true) : programmImFragmentV P fs = true :=
  List.all_eq_true.mpr fun f hf =>
    Endblock.vOk_of_kOk _ ((List.all_eq_true.mp h) f hf)

/-! ## 2. The one-sided comparison of frame results -/

/-- `a.folgt b`: the result `a` is predicted by `b` -- `b` predicts nothing
    (`sonst`), or `a` agrees with `b` up to the trace. -/
def ZErg.folgt {V : Vertrag D} (a b : ZErg V) : Prop := b = .sonst ∨ a.gleich b

namespace ZErg

variable {V : Vertrag D}

theorem folgt_refl (a : ZErg V) : a.folgt a := Or.inr (ZErg.gleich_refl a)

theorem folgt_of_gleich {a b : ZErg V} (h : a.gleich b) : a.folgt b := Or.inr h

theorem folgt_of_eq {a b : ZErg V} (h : a = b) : a.folgt b := by subst h; exact folgt_refl a

theorem folgt_sonst (a : ZErg V) : a.folgt .sonst := Or.inl rfl

theorem gleich_sonst_links {b : ZErg V} (h : ZErg.gleich .sonst b) : b = .sonst := by
  cases b <;> simp_all [ZErg.gleich]

theorem folgt_trans {a b c : ZErg V} (h1 : a.folgt b) (h2 : b.folgt c) : a.folgt c := by
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · rcases h1 with h1 | h1
    · subst h1
      exact Or.inl (gleich_sonst_links h2)
    · exact Or.inr (ZErg.gleich_trans h1 h2)

theorem folgt_zurueck {a : ZErg V} {σ : World D} {v : ErgVal D V.erg}
    (h : a.folgt (.zurueck σ v)) : a.gleich (.zurueck σ v) := by
  rcases h with h | h
  · cases h
  · exact h

theorem folgt_logik {a : ZErg V} {e : Logik D} (h : a.folgt (.logik e)) :
    a.gleich (.logik e) := by
  rcases h with h | h
  · cases h
  · exact h

end ZErg
/-! ## 3. The frame semantics of every residue -/


end Gabbro.Grammatik
