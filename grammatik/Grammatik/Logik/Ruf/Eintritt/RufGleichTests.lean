/-
  File:      Grammatik/RufGleichTests.lean
  Subject:   **RUN EQUALITY FOR DECISION AND FLOAT ARMS** -- the
              `callIndElse` statement arm and the `narrow`/`check`/float
              arms of the joint induction as standalone theorems taking
              the mutual IHs as premises. Kept in their own file so the
              mutual block stays below the size limit.
-/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.RahmenTreu.Tactics
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2
public import Grammatik.Logik.Ruf.Eintritt.RufGleichSchleife
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}
section GleichTests
variable (O : Orakel D)
variable (passes : Nat)
variable (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hAgr : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
  HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
  R₁ g σ ρ = R₂ g σ ρ)
variable (hT₁ : TreuR R₁) (hO : TreuO O)
include hAgr hT₁ hO
set_option linter.unusedSectionVars false

/-! ## The indirect else-call statement arm -/

theorem stmt_callIndElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : 0 < (D.sigNr n).gruende)
    (err : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.sigNr n).gruende :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Stmt.callIndElse p args he hp hr err).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execStmt O passes R₁ (Stmt.callIndElse p args he hp hr err) σ ρ =
      execStmt O passes R₂ (Stmt.callIndElse p args he hp hr err) σ ρ := by
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
  simp only [execStmt, indSonst]
  generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p
      (σ.lese Λ (p.orte ++ args.orte)) ρ = w
  obtain ⟨g, hg⟩ := w
  dsimp only
  replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
  have hentry : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g))
      (σ.lese Λ (p.orte ++ args.orte)).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  have hEqCall : R₁ g (σ.lese Λ (p.orte ++ args.orte))
        (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
          (σ.lese Λ (p.orte ++ args.orte)) ρ)) =
      R₂ g (σ.lese Λ (p.orte ++ args.orte))
        (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
          (σ.lese Λ (p.orte ++ args.orte)) ρ)) :=
    hAgr g _ _ hentry
  rw [hEqCall]
  cases hx : R₂ g (σ.lese Λ (p.orte ++ args.orte))
      (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
        (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
  | ok σ' v => rfl
  | why σ' r =>
      have h2 := hT₁ g _ _ hentry σ' (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have gcall : Treu V.schreibt V.gschreibt (σ.lese Λ (p.orte ++ args.orte)) σ' :=
        (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
      have g1 := hl.trans gcall
      have heq := ih_err σ' _ hscope_err
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      simp only [hx] at ⊢
      rw [heq]
  | logik e => rfl
  | hardware e => rfl

/-! ## Decision and float arms (Block) -/

theorem block_narrow_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int}
    (e : Expr D Γ Λ (.int lo hi)) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.int lo' hi' :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      execEnd O passes R₁ sonst σ ρ = execEnd O passes R₂ sonst σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.narrow e lo' hi' sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.narrow e lo' hi' sonst rest) σ ρ =
      execBlock O passes R₂ (Block.narrow e lo' hi' sonst rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execBlock]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;>
    simp only [hc, dif_pos, dif_neg] at ⊢
  · have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
    rw [heq]
  · have heq := ih_sonst _ ρ hscope_sonst (hl.heldB hh)
    rw [heq]

theorem block_check_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D Γ), rest.ScopesOk → HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      execEnd O passes R₁ sonst σ ρ = execEnd O passes R₂ sonst σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.check c sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.check c sonst rest) σ ρ =
      execBlock O passes R₂ (Block.check c sonst rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execBlock]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
  by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;>
    simp only [hc, ite_true, ite_false, Bool.true_eq_true, Bool.false_eq_true] at ⊢
  · have heq := ih_rest _ ρ hscope_rest (hl.heldB hh)
    rw [heq]
  · have heq := ih_sonst _ ρ hscope_sonst (hl.heldB hh)
    rw [heq]

theorem block_float_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int}
    (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.float op a b lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.float op a b lo hi rest) σ ρ =
      execBlock O passes R₂ (Block.float op a b lo hi rest) σ ρ := by
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
      rw [heq]

theorem block_floatLit_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (q lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.floatLit q lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.floatLit q lo hi rest) σ ρ =
      execBlock O passes R₂ (Block.floatLit q lo hi rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execBlock]
  generalize hv : gleitPasst lo hi (bruch q) = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest σ _ hscope_rest hh
      rw [heq]

theorem block_floatOf_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int}
    (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.floatOf e lo hi rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.floatOf e lo hi rest) σ ρ =
      execBlock O passes R₂ (Block.floatOf e lo hi rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execBlock]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  generalize hv : gleitPasst lo hi
      (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = ov at ⊢
  cases ov with
  | some v =>
      simp only [hv] at ⊢
      have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
      rw [heq]

theorem block_floatNarrow_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
    (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.fl lo hi :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      execEnd O passes R₁ sonst σ ρ = execEnd O passes R₂ sonst σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.floatNarrow e lo hi sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.floatNarrow e lo hi sonst rest) σ ρ =
      execBlock O passes R₂ (Block.floatNarrow e lo hi sonst rest) σ ρ := by
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
      rw [heq]
  | none =>
      simp only [hv] at ⊢
      have heq := ih_sonst _ ρ hscope_sonst (hl.heldB hh)
      rw [heq]

end GleichTests
end Gabbro.Grammatik
