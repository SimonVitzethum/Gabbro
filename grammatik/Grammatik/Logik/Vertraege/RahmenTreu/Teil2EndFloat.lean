module

public import Grammatik.Logik.Vertraege.RahmenTreu.Tactics
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2BindBlock
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2BindEnd
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil4

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
section Rumpf
variable (O : Orakel D)
variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : TreuR R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

theorem end_treu_float (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int × Int} (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk → HeldB bo Λ σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ) (hscope : (Endblock.float op a b lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.float op a b lo hi rest) σ ρ) := by
  intro σ' h
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execEnd] at h ⊢
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (a.orte ++ b.orte)
  generalize hv : gleitPasst lo hi (gleitRechne op (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = ov at h ⊢
  cases ov with
  | some v => exact (TreuEnd.vor hl (ihrest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
  | none => simp only [EndAusgang.welt, reduceCtorEq] at h

theorem end_treu_floatLit (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q : Int × Int) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk → HeldB bo Λ σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ) (hscope : (Endblock.floatLit q lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.floatLit q lo hi rest) σ ρ) := by
  intro σ' h
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execEnd] at h ⊢
  generalize hv : gleitPasst lo hi (bruch q) = ov at h ⊢
  cases ov with
  | some v => exact (ihrest σ _ hscope_rest hh).schrumpf σ' h
  | none => simp only [EndAusgang.welt, reduceCtorEq] at h

theorem end_treu_floatOf (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int} (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk → HeldB bo Λ σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ) (hscope : (Endblock.floatOf e lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.floatOf e lo hi rest) σ ρ) := by
  intro σ' h
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execEnd] at h ⊢
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  generalize hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = ov at h ⊢
  cases ov with
  | some v => exact (TreuEnd.vor hl (ihrest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
  | none => simp only [EndAusgang.welt, reduceCtorEq] at h

theorem end_treu_floatNarrow (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 : Int × Int} (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
    (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ihrest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk → HeldB bo Λ σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R rest σ ρ))
    (ihsonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk → HeldB bo Λ σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R sonst σ ρ))
    (σ : World D) (ρ : Env D Γ) (hscope : (Endblock.floatNarrow e lo hi sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R (Endblock.floatNarrow e lo hi sonst rest) σ ρ) := by
  intro σ' h
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execEnd] at h ⊢
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  generalize hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = ov at h ⊢
  cases ov with
  | some v => exact (TreuEnd.vor hl (ihrest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
  | none => exact (TreuEnd.vor hl (ihsonst _ ρ hscope_sonst (hl.heldB hh))) σ' h

end Rumpf
end Gabbro.Grammatik
