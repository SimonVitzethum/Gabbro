/-
  File:      Grammatik/RufGleichBindEnd.lean
  Subject:   **RUN EQUALITY FOR `Endblock` BIND ARMS** -- the long `bind`
              arms of the joint induction over terminal blocks, mirroring
              `RahmenTreu/Teil2BindEnd`. Each takes the mutual induction
              hypotheses it needs as explicit premises.
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

variable {D : Deklaration} {V : vertrag D}
section GleichBindEnd
variable (O : Orakel D)
variable (passes : Nat)
variable (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hAgr : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
  HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
  R₁ g σ ρ = R₂ g σ ρ)
variable (hT₁ : TreuR R₁) (hO : TreuO O)
include hAgr hT₁ hO
set_option linter.unusedSectionVars false

/-! ## End bind arms -/

theorem end_cons_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λm : List (Res D)}
    (s : Stmt D V l Γ Λ Λm) (rest : Endblock D V l Γ Λm)
    (ih_s : ∀ (σ : World D) (ρ : Env D Γ), s.ScopesOk → HeldB bo Λ σ.haelt →
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D Γ), rest.ScopesOk → HeldB bo Λm σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.cons s rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.cons s rest) σ ρ =
      execEnd O passes R₂ (Endblock.cons s rest) σ ρ := by
  have hscope_s : s.ScopesOk := by scopes_treu
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have heq := ih_s σ ρ hscope_s hh
  simp only [execEnd]
  rw [heq]
  cases hx : execStmt O passes R₂ s σ ρ with
  | ok σ' ρ' =>
      have hT : Treu V.schreibt V.gschreibt σ σ' := by
        have hT0 := stmt_treu O passes R₁ hT₁ hO bo hbV s σ ρ hscope_s hh σ'
          (by rw [heq, hx]; rfl)
        simpa [heq, hx] using hT0
      exact ih_rest σ' ρ' hscope_rest
        (HeldB.of_iff s.held_iff (hT.heldB hh))
  | zurueck σ' v => rfl
  | why σ' r => rfl
  | leave hl σ' ρ' => rfl
  | next hl σ' ρ' => rfl
  | logik e => rfl
  | hardware e => rfl

theorem end_bindCall_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Endblock D V l (τ :: Γ) (nach D f Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindCall f args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindCall f args he hp hr rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindCall f args he hp hr rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f))
      (σ.lese Λ args.orte).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  have hEqCall : R₁ f (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      R₂ f (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) :=
    hAgr f _ _ hentry
  simp only [execEnd]
  rw [hEqCall]
  cases hx : R₂ f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ1 v =>
      have h2 := hT₁ f _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      have heq := ih_rest σ1 _ hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      simp only [hx] at ⊢
      rw [heq]
  | why σ1 r => rfl
  | logik e => rfl
  | hardware e => rfl

theorem end_bindCallElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Endblock D V l (τ :: Γ) (nach D f Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.gruende f) :: Γ)), err.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindCallElse f args he hp hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindCallElse f args he hp hr err rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindCallElse f args he hp hr err rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f))
      (σ.lese Λ args.orte).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  have hEqCall : R₁ f (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      R₂ f (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) :=
    hAgr f _ _ hentry
  simp only [execEnd]
  rw [hEqCall]
  cases hx : R₂ f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ1 v =>
      have h2 := hT₁ f _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      have heq := ih_rest σ1 _ hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      simp only [hx] at ⊢
      rw [heq]
  | why σ1 r =>
      have h2 := hT₁ f _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have gcall : Treu V.schreibt V.gschreibt (σ.lese Λ args.orte) σ1 :=
        (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
      have g1 := hl.trans gcall
      have heq := ih_err σ1 _ hscope_err
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      simp only [hx] at ⊢
      rw [heq]
  | logik e => rfl
  | hardware e => rfl

theorem end_bindCallInd_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : (D.sigNr n).gruende = 0)
    (rest : Endblock D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindCallInd p args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindCallInd p args he hp hr rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindCallInd p args he hp hr rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
  simp only [execEnd]
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
  | ok σ1 v =>
      have h2 := hT₁ g _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      have heq := ih_rest σ1 _ hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      simp only [hx] at ⊢
      rw [heq]
  | why σ1 r => rfl
  | logik e => rfl
  | hardware e => rfl

theorem end_bindCallIndElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : 0 < (D.sigNr n).gruende)
    (err : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (rest : Endblock D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.sigNr n).gruende :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindCallIndElse p args he hp hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindCallIndElse p args he hp hr err rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindCallIndElse p args he hp hr err rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  simp only [execEnd, indSonstE]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
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
  | ok σ1 v =>
      have h2 := hT₁ g _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      have heq := ih_rest σ1 _ hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      simp only [hx] at ⊢
      rw [heq]
  | why σ1 r =>
      have h2 := hT₁ g _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have gcall : Treu V.schreibt V.gschreibt
          (σ.lese Λ (p.orte ++ args.orte)) σ1 :=
        (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
      have g1 := hl.trans gcall
      have heq := ih_err σ1 _ hscope_err
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      simp only [hx] at ⊢
      rw [heq]
  | logik e => rfl
  | hardware e => rfl

theorem end_bindAxiom_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Endblock D V l (τ :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindAxiom a args he hw hg hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindAxiom a args he hw hg hd hgd rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindAxiom a args he hw hg hd hgd rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  simp only [execEnd]
  cases hx : axiomAntwort O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ1 ov =>
      cases ov with
      | none => rfl
      | some v =>
          have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          rw [hx] at h1
          simp only [hx] at ⊢
          have g1 := hl.trans (Treu.weiter hw hg h1)
          have heq := ih_rest σ1 _ hscope_rest (g1.heldB hh)
          rw [heq]

theorem end_bindAxiomElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hr : 0 < D.agruende a)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ)
    (rest : Endblock D V l (τ :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.agruende a) :: Γ)), err.ScopesOk →
      HeldB bo Λ σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindAxiomElse a args he hr hw hg hd hgd err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  simp only [execEnd]
  cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ1 ov =>
      rcases ov with _ | v | r
      · rfl
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [hx] at h1
        simp only [hx] at ⊢
        have g1 := hl.trans (Treu.weiter hw hg h1)
        have heq := ih_rest σ1 _ hscope_rest (g1.heldB hh)
        rw [heq]
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [hx] at h1
        simp only [hx] at ⊢
        have g1 := hl.trans (Treu.weiter hw hg h1)
        have heq := ih_err σ1 _ hscope_err (g1.heldB hh)
        rw [heq]

theorem end_bindAxiomOpt_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Endblock D V l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (ErgCtx Γ e)), rest.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindAxiomOpt e a args he hp hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindAxiomOpt e a args he hp hd hgd rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindAxiomOpt e a args he hp hd hgd rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have ihr := fun σ ρ => ih_rest σ ρ hscope_rest
  cases e with
  | none =>
      simp only [execEnd, EndAusgang.weiterOpt]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          cases ov with
          | none => rfl
          | some v =>
              have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
                (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
              rw [hx] at h1
              simp only [hx] at ⊢
              have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
              have heq := ihr σ1 _
                (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
              rw [heq]
  | some τ =>
      simp only [execEnd, EndAusgang.weiterOpt]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          cases ov with
          | none => rfl
          | some v =>
              have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
                (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
              rw [hx] at h1
              simp only [hx] at ⊢
              have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
              have heq := ihr σ1 _
                (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
              simp only [hx] at ⊢
              rw [heq]

theorem end_bindAxiomOptElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
    (err : Endblock D V l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
    (rest : Endblock D V l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (ErgCtx Γ e)), rest.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      execEnd O passes R₁ rest σ ρ = execEnd O passes R₂ rest σ ρ)
    (ih_err : ∀ (σ : World D) (ρ : Env D (reasonTy (D.agruende a) :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.bindAxiomOptElse e a args he hp hd hgd hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execEnd O passes R₁ (Endblock.bindAxiomOptElse e a args he hp hd hgd hr err rest) σ ρ =
      execEnd O passes R₂ (Endblock.bindAxiomOptElse e a args he hp hd hgd hr err rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have ihr := fun σ ρ => ih_rest σ ρ hscope_rest
  have ihe := fun σ ρ => ih_err σ ρ hscope_err
  cases e with
  | none =>
      simp only [execEnd, EndAusgang.weiterOpt]
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          rcases ov with _ | v | r
          · rfl
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := ihr σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
            rw [heq]
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := (ihe σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf
            simp only [hx] at ⊢
            rw [heq]
  | some τ =>
      simp only [execEnd, EndAusgang.weiterOpt]
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          rcases ov with _ | v | r
          · rfl
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := (ihr σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf
            simp only [hx] at ⊢
            rw [heq]
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := (ihe σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf
            simp only [hx] at ⊢
            rw [heq]

end GleichBindEnd
end Gabbro.Grammatik
