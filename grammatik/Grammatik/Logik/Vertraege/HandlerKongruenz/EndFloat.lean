module
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil7
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}
section KongruenzDiszTest
variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}
  (hR : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
    HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
    RufUnter Er (R₁ g σ ρ) (R₂ g σ ρ))
  (hT₁ : TreuR R₁) (hO : TreuO O)
include hR hT₁ hO
set_option linter.unusedSectionVars false

theorem end_float_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int × Int}
    (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
    (lo hi : Int × Int) (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ rest σ ρ) (execEnd O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.float op a b lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    EndUnter Er (execEnd O passes R₁ (Endblock.float op a b lo hi rest) σ ρ)
      (execEnd O passes R₂ (Endblock.float op a b lo hi rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execEnd]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (a.orte ++ b.orte)
  generalize hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
      simp only [hv] at ⊢
      exact heq.schrumpf


theorem end_floatLit_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (q lo hi : Int × Int) (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ rest σ ρ) (execEnd O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.floatLit q lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    EndUnter Er (execEnd O passes R₁ (Endblock.floatLit q lo hi rest) σ ρ)
      (execEnd O passes R₂ (Endblock.floatLit q lo hi rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execEnd]
  generalize hv : gleitPasst lo hi (bruch q) = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest σ _ hscope_rest hh
      simp only [hv] at ⊢
      exact heq.schrumpf


theorem end_floatOf_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {l1 h1 : Int}
    (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
    (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ rest σ ρ) (execEnd O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.floatOf e lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    EndUnter Er (execEnd O passes R₁ (Endblock.floatOf e lo hi rest) σ ρ)
      (execEnd O passes R₂ (Endblock.floatOf e lo hi rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execEnd]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  generalize hv : gleitPasst lo hi
      (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
      simp only [hv] at ⊢
      exact heq.schrumpf


theorem end_floatNarrow_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {l1 h1 : Int × Int}
    (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
    (sonst : Endblock D V l Γ Λ) (rest : Endblock D V l (.fl lo hi :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ rest σ ρ) (execEnd O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.floatNarrow e lo hi sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    EndUnter Er (execEnd O passes R₁ (Endblock.floatNarrow e lo hi sonst rest) σ ρ)
      (execEnd O passes R₂ (Endblock.floatNarrow e lo hi sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execEnd]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  generalize hv : gleitPasst lo hi
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
      simp only [hv] at ⊢
      exact heq.schrumpf
  | none =>
      simp only [hv] at ⊢
      have heq := ih_sonst _ ρ hscope_sonst (hl.heldB hh)
      simp only [hv] at ⊢
      exact heq


end KongruenzDiszTest
end Gabbro.Grammatik
