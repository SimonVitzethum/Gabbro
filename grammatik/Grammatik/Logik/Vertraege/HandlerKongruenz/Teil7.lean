/-
  File:      Grammatik/HandlerKongruenz/Teil7.lean
  Subject:   **CONGRUENCE UNDER AN ERROR SET: DECISION ARMS** -- the
              `narrow`/`check`/float arms (both sorts) and the end-block
              register read as standalone theorems taking the mutual IHs as
              premises.
-/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.RahmenTreu.Tactics
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1
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

theorem block_narrow_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int}
    (e : Expr D Γ Λ (.int lo hi)) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.int lo' hi' :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.narrow e lo' hi' sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.narrow e lo' hi' sonst rest) σ ρ)
      (execBlock O passes R₂ (Block.narrow e lo' hi' sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execBlock]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;>
    simp only [hc, dif_pos, dif_neg] at ⊢
  · exact (ih_rest _ _ hscope_rest (hl.heldB hh)).schrumpf
  · exact (ih_sonst _ _ hscope_sonst (hl.heldB hh)).zuAusgang

theorem block_check_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D Γ), rest.ScopesOk → HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.check c sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.check c sonst rest) σ ρ)
      (execBlock O passes R₂ (Block.check c sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execBlock]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
  by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;>
    simp only [hc, ite_true, ite_false, Bool.true_eq_true, Bool.false_eq_true] at ⊢
  · exact ih_rest _ ρ hscope_rest (hl.heldB hh)
  · exact (ih_sonst _ _ hscope_sonst (hl.heldB hh)).zuAusgang

theorem block_float_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int}
    (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.float op a b lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.float op a b lo hi rest) σ ρ)
      (execBlock O passes R₂ (Block.float op a b lo hi rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execBlock]
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

theorem block_floatLit_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (q lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.floatLit q lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.floatLit q lo hi rest) σ ρ)
      (execBlock O passes R₂ (Block.floatLit q lo hi rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execBlock]
  generalize hv : gleitPasst lo hi (bruch q) = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest σ _ hscope_rest hh
      simp only [hv] at ⊢
      exact heq.schrumpf

theorem block_floatOf_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int}
    (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.floatOf e lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.floatOf e lo hi rest) σ ρ)
      (execBlock O passes R₂ (Block.floatOf e lo hi rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execBlock]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  generalize hv : gleitPasst lo hi
      (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
      simp only [hv] at ⊢
      exact heq.schrumpf

theorem block_floatNarrow_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
    (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.floatNarrow e lo hi sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.floatNarrow e lo hi sonst rest) σ ρ)
      (execBlock O passes R₂ (Block.floatNarrow e lo hi sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execBlock]
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
      exact heq.zuAusgang

theorem end_narrow_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {lo hi lo' hi' : Int}
    (e : Expr D Γ Λ (.int lo hi)) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.int lo' hi' :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.int lo' hi' :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ rest σ ρ) (execEnd O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.narrow e lo' hi' sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    EndUnter Er (execEnd O passes R₁ (Endblock.narrow e lo' hi' sonst rest) σ ρ)
      (execEnd O passes R₂ (Endblock.narrow e lo' hi' sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execEnd]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;>
    simp only [hc, dif_pos, dif_neg] at ⊢
  · exact (ih_rest _ _ hscope_rest (hl.heldB hh)).schrumpf
  · exact ih_sonst _ _ hscope_sonst (hl.heldB hh)

end KongruenzDiszTest

section KongruenzDiszArms

variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}
  (hR : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
    HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
    RufUnter Er (R₁ g σ ρ) (R₂ g σ ρ))
  (hT₁ : TreuR R₁) (hO : TreuO O)
include hR hT₁ hO
set_option linter.unusedSectionVars false

mutual
/-- **Option arms under two gatedly-related handlers.** -/
theorem arms_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (ih_block : ∀ {Γ' : Ctx} {Λ'' Λ''' : List (Res D)}
      (b : Block D V l Γ' Λ'' Λ''') (σ : World D) (ρ : Env D Γ'),
      b.ScopesOk → HeldB bo Λ'' σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ b σ ρ) (execBlock O passes R₂ b σ ρ)) :
    ∀ (a : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    a.ScopesOk → HeldB bo Λ σ.haelt →
    AusgangUnter Er (execArms O passes R₁ a v σ ρ) (execArms O passes R₂ a v σ ρ)
  | .nil, ⟨⟨k, hk⟩, _⟩, _, _, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ, hscope, hh => by
      have hscope_b : b.ScopesOk := by scopes_treu
      simp only [execArms]
      have heq := ih_block b σ (armEnv (Fall.toNutzlast _ _ _ _ nutz) ρ)
        hscope_b hh
      rw [heq]
  | .cons b rest, ⟨⟨i + 1, hk⟩, nutz⟩, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execArms]
      exact arms_unter bo hbV ih_block rest _ σ ρ hscope_rest hh
/-- **Reason arms under two gatedly-related handlers.** -/
theorem grundArms_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (ih_block : ∀ {Γ' : Ctx} {Λ'' Λ''' : List (Res D)}
      (b : Block D V l Γ' Λ'' Λ''') (σ : World D) (ρ : Env D Γ'),
      b.ScopesOk → HeldB bo Λ'' σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ b σ ρ) (execBlock O passes R₂ b σ ρ)) :
    ∀ (a : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    a.ScopesOk → HeldB bo Λ σ.haelt →
    AusgangUnter Er (execGrund O passes R₁ a r σ ρ) (execGrund O passes R₂ a r σ ρ)
  | .nil, r, _, _, _, _ => r.elim0
  | .cons b rest, ⟨0, _⟩, σ, ρ, hscope, hh => by
      have hscope_b : b.ScopesOk := by scopes_treu
      simp only [execGrund]
      exact ih_block b σ ρ hscope_b hh
  | .cons b rest, ⟨i + 1, hk⟩, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execGrund]
      exact grundArms_unter bo hbV ih_block rest _ σ ρ hscope_rest hh
end

end KongruenzDiszArms
end Gabbro.Grammatik