/-
  File:      Grammatik/HandlerKongruenz/Teil4.lean
  Subject:   **CONGRUENCE UNDER AN ERROR SET: `Block` ARMS** -- the long
              `bind` arms of the fused induction as standalone theorems
              taking the mutual IHs as premises. Mirror of the `Teil2Basis`
              arms with the handler premise gated by `HeldB` and the
              discipline threaded through.
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
section KongruenzDiszBind
variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}
  (hR : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
    HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
    RufUnter Er (R₁ g σ ρ) (R₂ g σ ρ))
  (hT₁ : TreuR R₁) (hO : TreuO O)
include hR hT₁ hO

theorem block_cons_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' Λm : List (Res D)}
    (s : Stmt D V l Γ Λ Λm) (rest : Block D V l Γ Λm Λ')
    (ih_s : ∀ (σ : World D) (ρ : Env D Γ), s.ScopesOk → HeldB bo Λ σ.haelt →
      AusgangUnter Er (execStmt O passes R₁ s σ ρ) (execStmt O passes R₂ s σ ρ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D Γ), rest.ScopesOk → HeldB bo Λm σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.cons s rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.cons s rest) σ ρ)
      (execBlock O passes R₂ (Block.cons s rest) σ ρ) := by
  have hscope_s : s.ScopesOk := by scopes_treu
  have hscope_rest : rest.ScopesOk := by scopes_treu
  simp only [execBlock]
  rcases ih_s σ ρ hscope_s hh with h | ⟨m, h1, hE⟩
  · rw [h]
    cases hx : execStmt O passes R₂ s σ ρ with
    | ok σ' ρ' =>
        have hT : Treu V.schreibt V.gschreibt σ σ' := by
          have hT0 := stmt_treu O passes R₁ hT₁ hO bo hbV s σ ρ hscope_s hh σ'
            (by rw [h, hx]; rfl)
          simpa [h, hx] using hT0
        exact ih_rest σ' ρ' hscope_rest
          (HeldB.of_iff s.held_iff (hT.heldB hh))
    | zurueck σ' v => exact AusgangUnter.refl _
    | why σ' r => exact AusgangUnter.refl _
    | leave hl σ' ρ' => exact AusgangUnter.refl _
    | next hl σ' ρ' => exact AusgangUnter.refl _
    | logik e => exact AusgangUnter.refl _
    | hardware e => exact AusgangUnter.refl _
  · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

theorem block_bindCall_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCall f args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.bindCall f args he hp hr rest) σ ρ)
      (execBlock O passes R₂ (Block.bindCall f args he hp hr rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f))
      (σ.lese Λ args.orte).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  simp only [execBlock]
  rcases hR f _ _ hentry with h | ⟨m, h1, hE⟩
  · rw [h]
    cases hx : R₂ f (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | ok σ1 v =>
        have h2 := hT₁ f _ _ hentry σ1 (by rw [h, hx]; rfl)
        rw [h, hx] at h2
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
        have heq := ih_rest σ1 _ hscope_rest
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        simp only [hx] at ⊢
        exact heq.schrumpf
    | why σ1 r => exact AusgangUnter.refl _
    | logik e => exact AusgangUnter.refl _
    | hardware e => exact AusgangUnter.refl _
  · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

theorem block_bindCallInd_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : (D.sigNr n).gruende = 0)
    (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ))
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallInd p args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.bindCallInd p args he hp hr rest) σ ρ)
      (execBlock O passes R₂ (Block.bindCallInd p args he hp hr rest) σ ρ) := by
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
  rcases hR g _ _ hentry with h | ⟨m, h1, hE⟩
  · rw [h]
    cases hx : R₂ g (σ.lese Λ (p.orte ++ args.orte))
        (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
          (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
    | ok σ1 v =>
        have h2 := hT₁ g _ _ hentry σ1 (by rw [h, hx]; rfl)
        rw [h, hx] at h2
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
        have heq := ih_rest σ1 _ hscope_rest
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        simp only [hx] at ⊢
        exact heq.schrumpf
    | why σ1 r => exact AusgangUnter.refl _
    | logik e => exact AusgangUnter.refl _
    | hardware e => exact AusgangUnter.refl _
  · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

theorem block_bindCallElse_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.gruende f) :: Γ)), err.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      EndUnter Er (execEnd O passes R₁ err σ ρ) (execEnd O passes R₂ err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallElse f args he hp hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.bindCallElse f args he hp hr err rest) σ ρ)
      (execBlock O passes R₂ (Block.bindCallElse f args he hp hr err rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f))
      (σ.lese Λ args.orte).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  simp only [execBlock]
  rcases hR f _ _ hentry with h | ⟨m, h1, hE⟩
  · rw [h]
    cases hx : R₂ f (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | ok σ1 v =>
        have h2 := hT₁ f _ _ hentry σ1 (by rw [h, hx]; rfl)
        rw [h, hx] at h2
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
        have heq := ih_rest σ1 _ hscope_rest
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        simp only [hx] at ⊢
        exact heq.schrumpf
    | why σ1 r =>
        have h2 := hT₁ f _ _ hentry σ1 (by rw [h, hx]; rfl)
        rw [h, hx] at h2
        have gcall : Treu V.schreibt V.gschreibt (σ.lese Λ args.orte) σ1 :=
          (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
        have g1 := hl.trans gcall
        have heq := ih_err σ1 _ hscope_err
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        simp only [hx] at ⊢
        exact heq.schrumpf.zuAusgang
    | logik e => exact AusgangUnter.refl _
    | hardware e => exact AusgangUnter.refl _
  · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

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
  · exact (ih_sonst _ ρ hscope_sonst (hl.heldB hh)).zuAusgang

theorem block_bindCallIndElse_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : 0 < (D.sigNr n).gruende)
    (err : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.sigNr n).gruende :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      EndUnter Er (execEnd O passes R₁ err σ ρ) (execEnd O passes R₂ err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallIndElse p args he hp hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er
      (execBlock O passes R₁ (Block.bindCallIndElse p args he hp hr err rest) σ ρ)
      (execBlock O passes R₂ (Block.bindCallIndElse p args he hp hr err rest) σ ρ) := by
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
  rcases hR g _ _ hentry with h | ⟨m, h1, hE⟩
  · rw [h]
    cases hx : R₂ g (σ.lese Λ (p.orte ++ args.orte))
        (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
          (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
    | ok σ1 v =>
        have h2 := hT₁ g _ _ hentry σ1 (by rw [h, hx]; rfl)
        rw [h, hx] at h2
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
        have heq := ih_rest σ1 _ hscope_rest
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        simp only [hx] at ⊢
        exact heq.schrumpf
    | why σ1 r =>
        have h2 := hT₁ g _ _ hentry σ1 (by rw [h, hx]; rfl)
        rw [h, hx] at h2
        have gcall : Treu V.schreibt V.gschreibt
            (σ.lese Λ (p.orte ++ args.orte)) σ1 :=
          (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
        have g1 := hl.trans gcall
        have heq := ih_err σ1 _ hscope_err
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        simp only [hx] at ⊢
        exact heq.schrumpf.zuAusgang
    | logik e => exact AusgangUnter.refl _
    | hardware e => exact AusgangUnter.refl _
  · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

theorem block_bindAxiom_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiom a args he hw hg hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.bindAxiom a args he hw hg hd hgd rest) σ ρ)
      (execBlock O passes R₂ (Block.bindAxiom a args he hw hg hd hgd rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  simp only [execBlock]
  cases hx : axiomAntwort O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ1 ov =>
      cases ov with
      | none => exact AusgangUnter.refl _
      | some v =>
          have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          rw [hx] at h1
          simp only [hx] at ⊢
          have g1 := hl.trans (Treu.weiter hw hg h1)
          have heq := ih_rest σ1 _ hscope_rest (g1.heldB hh)
          simp only [hx] at ⊢
          exact heq.schrumpf

theorem block_bindAxiomElse_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
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
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.agruende a) :: Γ)), err.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ err σ ρ) (execEnd O passes R₂ err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomElse a args he hr hw hg hd hgd err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er
      (execBlock O passes R₁ (Block.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ)
      (execBlock O passes R₂ (Block.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  simp only [execBlock]
  cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ1 ov =>
      rcases ov with _ | v | r
      · exact AusgangUnter.refl _
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [hx] at h1
        simp only [hx] at ⊢
        have g1 := hl.trans (Treu.weiter hw hg h1)
        have heq := ih_rest σ1 _ hscope_rest (g1.heldB hh)
        simp only [hx] at ⊢
        exact heq.schrumpf
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [hx] at h1
        simp only [hx] at ⊢
        have g1 := hl.trans (Treu.weiter hw hg h1)
        have heq := ih_err σ1 _ hscope_err (g1.heldB hh)
        simp only [hx] at ⊢
        exact heq.schrumpf.zuAusgang

theorem block_bindAxiomOpt_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (ErgCtx Γ e)), rest.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomOpt e a args he hp hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.bindAxiomOpt e a args he hp hd hgd rest) σ ρ)
      (execBlock O passes R₂ (Block.bindAxiomOpt e a args he hp hd hgd rest) σ ρ) := by
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
          | none => exact AusgangUnter.refl _
          | some v =>
              have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
                (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
              rw [hx] at h1
              simp only [hx] at ⊢
              have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
              have heq := ihr σ1 _
                (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
              exact heq
  | some τ =>
      simp only [execBlock, Ausgang.weiterOpt]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          cases ov with
          | none => exact AusgangUnter.refl _
          | some v =>
              have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
                (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
              rw [hx] at h1
              simp only [hx] at ⊢
              have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
              have heq := ihr σ1 _
                (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
              simp only [hx] at ⊢
              exact heq.schrumpf

theorem stmt_callIndElse_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : 0 < (D.sigNr n).gruende)
    (err : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.sigNr n).gruende :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      EndUnter Er (execEnd O passes R₁ err σ ρ) (execEnd O passes R₂ err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Stmt.callIndElse p args he hp hr err).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execStmt O passes R₁ (Stmt.callIndElse p args he hp hr err) σ ρ)
      (execStmt O passes R₂ (Stmt.callIndElse p args he hp hr err) σ ρ) := by
  have hscope_err : err.ScopesOk := by scopes_treu
  simp only [execStmt, indSonst]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
  generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p
      (σ.lese Λ (p.orte ++ args.orte)) ρ = w
  obtain ⟨g, hg⟩ := w
  dsimp only
  replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
  have hentry : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g))
      (σ.lese Λ (p.orte ++ args.orte)).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  rcases hR g _ _ hentry with h | ⟨m, h1, hE⟩
  · rw [h]
    cases hx : R₂ g (σ.lese Λ (p.orte ++ args.orte))
        (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
          (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
    | ok σ' v => exact AusgangUnter.refl _
    | why σ' r =>
        have h2 := hT₁ g _ _ hentry σ' (by rw [h, hx]; rfl)
        rw [h, hx] at h2
        have gcall : Treu V.schreibt V.gschreibt
            (σ.lese Λ (p.orte ++ args.orte)) σ' :=
          (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
        have g1 := hl.trans gcall
        have heq := ih_err σ' _ hscope_err
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        simp only [hx] at ⊢
        exact heq.schrumpf.zuAusgang
    | logik e => exact AusgangUnter.refl _
    | hardware e => exact AusgangUnter.refl _
  · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

end KongruenzDiszBind
end Gabbro.Grammatik
