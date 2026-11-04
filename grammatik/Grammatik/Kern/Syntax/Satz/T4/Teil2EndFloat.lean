module
public import Grammatik.Kern.Syntax.Satz.T4.Teil2Context
@[expose] public section
namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
section Rumpf
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hR : GutR R) (hO : GutO O)
include hR hO
set_option linter.unusedSectionVars false
set_option hygiene false in
local macro "scopes_gut" : tactic => `(tactic| first
  | exact hscope
  | (have hsc := hscope
     dsimp only [Stmt.ScopesOk, Block.ScopesOk, Endblock.ScopesOk, Arms.ScopesOk, GrundArms.ScopesOk] at hsc
     simp only [Stmt.scopesOk, Block.scopesOk, Endblock.scopesOk, Arms.scopesOk, GrundArms.scopesOk, Bool.and_eq_true] at hsc
     first | exact hsc | exact hsc.1 | exact hsc.2 | exact hsc.2.1 | exact hsc.2.2 | exact hsc.1.1 | exact hsc.1.2))
theorem end_gutB_float (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int × Int} (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.BodenOk bo → rest.ScopesOk → ResidHeld V Λ → HeldB bo Λ σ.haelt →
      GutEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ) (hbo : (Endblock.float op a b lo hi rest).BodenOk bo) (hscope : (Endblock.float op a b lo hi rest).ScopesOk)
    (hresid : ResidHeld V Λ) (hh : HeldB bo Λ σ.haelt) :
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.float op a b lo hi rest) σ ρ) := by
  intro σ' h
  simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append a.orte_darf b.orte_darf) hh.heldIn; generalize hv : gleitPasst lo hi (gleitRechne op (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = ov at h ⊢; cases ov with
  | some v => exact (GutEnd.vor hl (ihrest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
  | none => simp only [EndAusgang.welt, reduceCtorEq] at h

theorem end_gutB_floatLit (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q : Int × Int) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.BodenOk bo → rest.ScopesOk → ResidHeld V Λ → HeldB bo Λ σ.haelt →
      GutEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ) (hbo : (Endblock.floatLit q lo hi rest).BodenOk bo) (hscope : (Endblock.floatLit q lo hi rest).ScopesOk)
    (hresid : ResidHeld V Λ) (hh : HeldB bo Λ σ.haelt) :
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.floatLit q lo hi rest) σ ρ) := by
  intro σ' h
  simp only [execEnd] at h ⊢; generalize hv : gleitPasst lo hi (bruch q) = ov at h ⊢; cases ov with
  | some v => exact (ihrest σ _ (by boden_tac) (by scopes_gut) hresid hh).schrumpf σ' h
  | none => simp only [EndAusgang.welt, reduceCtorEq] at h

theorem end_gutB_floatOf (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int} (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.BodenOk bo → rest.ScopesOk → ResidHeld V Λ → HeldB bo Λ σ.haelt →
      GutEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ) (hbo : (Endblock.floatOf e lo hi rest).BodenOk bo) (hscope : (Endblock.floatOf e lo hi rest).ScopesOk)
    (hresid : ResidHeld V Λ) (hh : HeldB bo Λ σ.haelt) :
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.floatOf e lo hi rest) σ ρ) := by
  intro σ' h
  simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; generalize hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = ov at h ⊢; cases ov with
  | some v => exact (GutEnd.vor hl (ihrest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
  | none => simp only [EndAusgang.welt, reduceCtorEq] at h

theorem end_gutB_floatNarrow (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int × Int} (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
    (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.BodenOk bo → rest.ScopesOk → ResidHeld V Λ → HeldB bo Λ σ.haelt →
      GutEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (ihsonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.BodenOk bo → sonst.ScopesOk → ResidHeld V Λ → HeldB bo Λ σ.haelt →
      GutEnd V.schreibt V.gschreibt σ (execEnd O passes R sonst σ ρ))
    (σ : World D) (ρ : Env D Γ) (hbo : (Endblock.floatNarrow e lo hi sonst rest).BodenOk bo) (hscope : (Endblock.floatNarrow e lo hi sonst rest).ScopesOk)
    (hresid : ResidHeld V Λ) (hh : HeldB bo Λ σ.haelt) :
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.floatNarrow e lo hi sonst rest) σ ρ) := by
  intro σ' h
  simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; generalize hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = ov at h ⊢; cases ov with
  | some v => exact (GutEnd.vor hl (ihrest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
  | none => exact (GutEnd.vor hl (ihsonst _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h

end Rumpf
end Gabbro.Grammatik
