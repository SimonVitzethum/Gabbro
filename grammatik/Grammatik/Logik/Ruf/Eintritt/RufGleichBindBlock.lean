/-
  File:      Grammatik/RufGleichBindBlock.lean
  Subject:   **RUN EQUALITY FOR `Block` BIND ARMS** -- the long `bind` arms
              of the joint induction as standalone theorems, mirroring
              `RahmenTreu/Teil2BindBlock`. Each takes the mutual induction
              hypotheses it needs as explicit premises, so the mutual block
              stays whole and each arm becomes one application.
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
section GleichBind
variable (O : Orakel D)
variable (passes : Nat)
variable (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hAgr : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
  HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
  R₁ g σ ρ = R₂ g σ ρ)
variable (hT₁ : TreuR R₁) (hO : TreuO O)
include hAgr hT₁ hO
set_option linter.unusedSectionVars false

/-! ## Block bind arms -/

theorem block_cons_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' Λm : List (Res D)}
    (s : Stmt D V l Γ Λ Λm) (rest : Block D V l Γ Λm Λ')
    (ih_s : ∀ (σ : World D) (ρ : Env D Γ), s.ScopesOk → HeldB bo Λ σ.haelt →
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D Γ), rest.ScopesOk → HeldB bo Λm σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.cons s rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.cons s rest) σ ρ =
      execBlock O passes R₂ (Block.cons s rest) σ ρ := by
  have hscope_s : s.ScopesOk := by scopes_treu
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have heq := ih_s σ ρ hscope_s hh
  simp only [execBlock]
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

theorem block_bindCall_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCall f args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.bindCall f args he hp hr rest) σ ρ =
      execBlock O passes R₂ (Block.bindCall f args he hp hr rest) σ ρ := by
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
  simp only [execBlock]
  rw [hEqCall]
  cases hx : R₂ f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ1 v =>
      have h2 := hT₁ f _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      have heq := ih_rest σ1 (.cons (ergWert he v) ρ) hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      rw [heq]
  | why σ1 r => rfl
  | logik e => rfl
  | hardware e => rfl

theorem block_bindCallInd_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : (D.sigNr n).gruende = 0)
    (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallInd p args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.bindCallInd p args he hp hr rest) σ ρ =
      execBlock O passes R₂ (Block.bindCallInd p args he hp hr rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
  simp only [execBlock]
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
      have heq := ih_rest σ1 (.cons (ergWert (ergSig hg he) v) ρ) hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      rw [heq]
  | why σ1 r => rfl
  | logik e => rfl
  | hardware e => rfl

theorem block_bindCallElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.gruende f) :: Γ)), err.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallElse f args he hp hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.bindCallElse f args he hp hr err rest) σ ρ =
      execBlock O passes R₂ (Block.bindCallElse f args he hp hr err rest) σ ρ := by
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
  simp only [execBlock]
  rw [hEqCall]
  cases hx : R₂ f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ1 v =>
      have h2 := hT₁ f _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      have heq := ih_rest σ1 (.cons (ergWert he v) ρ) hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      rw [heq]
  | why σ1 r =>
      have h2 := hT₁ f _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have gcall : Treu V.schreibt V.gschreibt (σ.lese Λ args.orte) σ1 :=
        (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
      have g1 := hl.trans gcall
      have heq := ih_err σ1 (.cons r ρ) hscope_err
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      rw [heq]
  | logik e => rfl
  | hardware e => rfl

theorem block_bindCallIndElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : 0 < (D.sigNr n).gruende)
    (err : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.sigNr n).gruende :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallIndElse p args he hp hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.bindCallIndElse p args he hp hr err rest) σ ρ =
      execBlock O passes R₂ (Block.bindCallIndElse p args he hp hr err rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  simp only [execBlock, indSonst]
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
      have heq := ih_rest σ1 (.cons (ergWert (ergSig hg he) v) ρ) hscope_rest
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      rw [heq]
  | why σ1 r =>
      have h2 := hT₁ g _ _ hentry σ1 (by rw [hEqCall, hx]; rfl)
      rw [hEqCall, hx] at h2
      have gcall : Treu V.schreibt V.gschreibt
          (σ.lese Λ (p.orte ++ args.orte)) σ1 :=
        (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
      have g1 := hl.trans gcall
      have heq := ih_err σ1 (.cons (grundSig hg r) ρ) hscope_err
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
      rw [heq]
  | logik e => rfl
  | hardware e => rfl

theorem block_bindAxiom_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiom a args he hw hg hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.bindAxiom a args he hw hg hd hgd rest) σ ρ =
      execBlock O passes R₂ (Block.bindAxiom a args he hw hg hd hgd rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  simp only [execBlock]
  cases hx : axiomAntwort O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ1 ov =>
      cases ov with
      | none => rfl
      | some v =>
          have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          rw [hx] at h1
          have g1 := hl.trans (Treu.weiter hw hg h1)
          have heq := ih_rest σ1 (.cons (ergWert he v) ρ) hscope_rest (g1.heldB hh)
          rw [heq]

theorem block_bindAxiomElse_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hr : 0 < D.agruende a)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.agruende a) :: Γ)), err.ScopesOk →
      HeldB bo Λ σ.haelt →
      execEnd O passes R₁ err σ ρ = execEnd O passes R₂ err σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomElse a args he hr hw hg hd hgd err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ =
      execBlock O passes R₂ (Block.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  simp only [execBlock]
  cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ1 ov =>
      rcases ov with _ | v | r
      · rfl
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [← axiomAntwortSonst_fst, hx] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        have heq := ih_rest σ1 (.cons (ergWert he v) ρ) hscope_rest (g1.heldB hh)
        rw [heq]
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [← axiomAntwortSonst_fst, hx] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        have heq := ih_err σ1 (.cons r ρ) hscope_err (g1.heldB hh)
        rw [heq]

theorem block_bindAxiomOpt_gleich (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (ErgCtx Γ e)), rest.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      execBlock O passes R₁ rest σ ρ = execBlock O passes R₂ rest σ ρ)
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomOpt e a args he hp hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    execBlock O passes R₁ (Block.bindAxiomOpt e a args he hp hd hgd rest) σ ρ =
      execBlock O passes R₂ (Block.bindAxiomOpt e a args he hp hd hgd rest) σ ρ := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have ihr := fun σ ρ => ih_rest σ ρ hscope_rest
  cases e with
  | none =>
      simp only [execBlock, Ausgang.weiterOpt]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          cases ov with
          | none => rfl
          | some v =>
              have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
                (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
              rw [hx] at h1
              have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
              have heq := ihr σ1 (ergEnv none (he ▸ v) ρ)
                (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
              rw [heq]
  | some τ =>
      simp only [execBlock, Ausgang.weiterOpt]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          cases ov with
          | none => rfl
          | some v =>
              have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
                (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
              rw [hx] at h1
              have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
              have heq := ih_rest σ1 (ergEnv (some τ) (he ▸ v) ρ) hscope_rest
                (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
              rw [heq]

end GleichBind
end Gabbro.Grammatik
