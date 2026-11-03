/-
  File:      Grammatik/HandlerKongruenz/Teil6.lean
  Subject:   **THE FUSED RUN-EQUALITY INDUCTION** -- statements, blocks,
              terminal blocks and arms in one mutual block: two handlers
              that agree on disciplined entries (or fail early with a
              first-side mark) give runs that agree or fail early, from a
              disciplined entry.

  WHY IT EXISTS. Part 4 (`RufLogika.lean`) must relate the model's own
  call `rufAt` to its gated patched form where the entry discipline
  holds only at the outer entry; inner entries inherit it along the run,
  which this induction maintains. Long arms delegate to `Teil4.lean`,
  `Teil5.lean` and `Teil7.lean`.
-/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.RahmenTreu.Tactics
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil3
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil4
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil5
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil7
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil8
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : vertrag D}

/-- **The gated handler premise**: at entries meeting the callee-entry
    discipline the two handlers agree, or both answer an error and the two
    marks stand in `Er`. -/
def HandlerUnterDisz (Er : Fehlermarke D → Prop)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
    HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
    RufUnter Er (R₁ g σ ρ) (R₂ g σ ρ)

section KongruenzDisz
variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}
  (hR : HandlerUnterDisz Er R₁ R₂) (hT₁ : TreuR R₁) (hO : TreuO O)
include hR hT₁ hO
set_option linter.unusedSectionVars false

mutual
/-- **A statement under two gatedly-related handlers.** -/
theorem stmt_unter (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), s.ScopesOk →
    HeldB bo Λ σ.haelt →
    AusgangUnter Er (execStmt O passes R₁ s σ ρ) (execStmt O passes R₂ s σ ρ)
  | .ite c t e, σ, ρ, hscope, hh => by
      have hscope_t : t.ScopesOk := by scopes_treu
      have hscope_e : e.ScopesOk := by scopes_treu
      simp only [execStmt]
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;>
        simp only [hc, ite_true, ite_false] at ⊢
      · exact AusgangUnter.ite
          (block_unter bo hbV t _ _ hscope_t (hl.heldB hh))
          (block_unter bo hbV e _ _ hscope_e (hl.heldB hh))
      · exact AusgangUnter.ite
          (block_unter bo hbV t _ _ hscope_t (hl.heldB hh))
          (block_unter bo hbV e _ _ hscope_e (hl.heldB hh))
  | .onOption o p a, σ, ρ, hscope, hh => by
      have hscope_p : p.ScopesOk := by scopes_treu
      have hscope_a : a.ScopesOk := by scopes_treu
      simp only [execStmt]
      cases hv : (eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ : Option _) with
      | none => exact (block_unter bo hbV a _ ρ hscope_a hh).schrumpfArm none
      | some k =>
          have heq := block_unter bo hbV p _ (.cons k ρ) hscope_p hh
          simp only [hv] at ⊢
          exact heq.schrumpf
  | .onTag v arms, σ, ρ, hscope, hh => by
      have hscope_a : arms.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact arms_unter bo hbV
        (fun b σ ρ hs hh => block_unter bo hbV b σ ρ hs hh)
        arms _ _ _ hscope_a hh
  | .onWhy r arms, σ, ρ, hscope, hh => by
      have hscope_a : arms.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact grundArms_unter bo hbV
        (fun b σ ρ hs hh => block_unter bo hbV b σ ρ hs hh)
        arms _ _ _ hscope_a hh
  | .locks L hr body, σ, ρ, hscope, hh => by
      have hscope_body : body.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact (block_unter bo hbV body (σ.nimmt L) ρ hscope_body (heldB_locks L hh)).mapWelt
  | .breaking i body, σ, ρ, hscope, hh => by
      have hscope_body : body.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact block_unter bo hbV body σ ρ hscope_body hh
  | .traverse t inv body, σ, ρ, hscope, hh => by
      have hscope_body : body.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact traverseLauf_unter O passes R₁ R₂ bo body
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (fun σ ρ hs₁ hs₂ hh => block_unter bo hbV body σ ρ hs₁ hh)
        (fun σ ρ hs hh => block_treu O passes R₁ hT₁ hO bo hbV body σ ρ hs hh)
        (fun σ ρ _ => treu_lese σ Λ inv.orte) hscope_body hscope_body
        (alleIndizes (D.count t)) σ ρ hh
  | .consumeTraverse t member edge inv bound mass body, σ, ρ, hscope, hh => by
      have hscope_body : body.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact verbrauchLauf_unter O passes R₁ R₂ bo t body
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (verbrauchSel t member edge)
        (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n))
        bound
        (fun σ ρ hs₁ hs₂ hh => block_unter bo hbV body σ ρ hs₁ hh)
        (fun σ ρ hs hh => block_treu O passes R₁ hT₁ hO bo hbV body σ ρ hs hh)
        (fun σ ρ _ => treu_lese σ Λ inv.orte)
        (fun σ ρ _ => treu_lese σ Λ (member.orte ++ edge.orte))
        (fun σ ρ _ => treu_lese σ Λ mass.orte) hscope_body hscope_body
        ((D.count t).toNat + bound.toNat + 1) σ ρ hh
  | .retry n bis body ueber, σ, ρ, hscope, hh => by
      have hscope_body : body.ScopesOk := by scopes_treu
      have hscope_ueber : ueber.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact retryLauf_unter O passes R₁ R₂ bo body
        (fun σ ρ => let σ := σ.lese Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
        ueber
        (fun σ ρ hs₁ hs₂ hh => block_unter bo hbV body σ ρ hs₁ hh)
        (fun σ ρ hs hh => block_treu O passes R₁ hT₁ hO bo hbV body σ ρ hs hh)
        (fun σ ρ hs₁ hs₂ hh => block_unter bo hbV ueber σ ρ hs₁ hh)
        (fun σ ρ _ => treu_lese σ Λ bis.orte)
        hscope_body hscope_body hscope_ueber hscope_ueber n σ ρ hh
  | .forever a inv body, σ, ρ, hscope, hh => by
      have hscope_body : body.ScopesOk := by scopes_treu
      simp only [execStmt]
      exact foreverLauf_unter O passes R₁ R₂ bo a body
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (fun σ ρ hs₁ hs₂ hh => block_unter bo hbV body σ ρ hs₁ hh)
        (fun σ ρ hs hh => block_treu O passes R₁ hT₁ hO bo hbV body σ ρ hs hh)
        (fun σ ρ _ => treu_lese σ Λ inv.orte) hscope_body hscope_body passes σ ρ hh
  | .call g args hp hr, σ, ρ, hscope, hh => by
      simp only [execStmt]
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hentry : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g))
          (σ.lese Λ args.orte).haelt :=
        heldB_ruf hp hbV (hl.heldB hh)
      rcases hR g _ _ hentry with h | ⟨m, h1, hE⟩
      · rw [h]; exact AusgangUnter.refl _
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .callInd p args hp hr, σ, ρ, hscope, hh => by
      simp only [execStmt]
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
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) <;>
          exact AusgangUnter.refl _
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .callIndElse p args he hp hr err, σ, ρ, hscope, hh =>
      stmt_callIndElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        p args he hp hr err
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .assignSlot .., _, _, _, _ => exact AusgangUnter.refl _
  | .assignThru .., _, _, _, _ | .assignSlotRef .., _, _, _, _ => exact AusgangUnter.refl _
  | .assignGlob .., _, _, _, _ => exact AusgangUnter.refl _
  | .putBytes .., _, _, _, _ => exact AusgangUnter.refl _
  | .assignVar .., _, _, _, _ => exact AusgangUnter.refl _
  | .shift .., _, _, _, _ => exact AusgangUnter.refl _
  | .axiomCall .., _, _, _, _ => exact AusgangUnter.refl _
  | .axiomCallElse _ a args _ hp _ _ _ err, σ, ρ, hscope, hh => by
      have hscope_err : err.ScopesOk := by scopes_treu
      simp only [execStmt]
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ2 ov =>
          rcases ov with _ | v | r
          · exact AusgangUnter.refl _
          · exact AusgangUnter.refl _
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := end_unter bo hbV err σ2 _ hscope_err (g1.heldB hh)
            simp only [hx] at ⊢
            exact heq.schrumpf.zuAusgang
  | .regWrite .., _, _, _, _ => exact AusgangUnter.refl _
  | .transition .., _, _, _, _ => exact AusgangUnter.refl _
  | .publish .., _, _, _, _ => exact AusgangUnter.refl _
  | .advances .., _, _, _, _ => exact AusgangUnter.refl _
  | .retires .., _, _, _, _ => exact AusgangUnter.refl _
  | .ret .., _, _, _, _ => exact AusgangUnter.refl _
  | .retWhy .., _, _, _, _ => exact AusgangUnter.refl _
  | .retScoped .., _, _, _, _ => exact AusgangUnter.refl _
  | .retWhyScoped .., _, _, _, _ => exact AusgangUnter.refl _
  | .leave .., _, _, _, _ => exact AusgangUnter.refl _
  | .next .., _, _, _, _ => exact AusgangUnter.refl _
/-- **A block under two gatedly-related handlers.** -/
theorem block_unter (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), b.ScopesOk →
    HeldB bo Λ σ.haelt →
    AusgangUnter Er (execBlock O passes R₁ b σ ρ) (execBlock O passes R₂ b σ ρ)
  | .nil, _, _, _, _ => exact AusgangUnter.refl _
  | .cons s rest, σ, ρ, hscope, hh =>
      block_cons_unter O passes R₁ R₂ hR hT₁ hO bo hbV s rest
        (fun σ ρ hs hh => stmt_unter bo hbV s σ ρ hs hh)
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bind e rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      have heq := block_unter bo hbV rest _ _ hscope_rest (hl.heldB hh)
      simp only [execBlock]
      exact heq.schrumpf
  | .bindCall g args he hp hr rest, σ, ρ, hscope, hh =>
      block_bindCall_unter O passes R₁ R₂ hR hT₁ hO bo hbV g args he hp hr rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindCallInd p args he hp hr rest, σ, ρ, hscope, hh =>
      block_bindCallInd_unter O passes R₁ R₂ hR hT₁ hO bo hbV p args he hp hr rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hscope, hh =>
      block_bindCallIndElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        p args he hp hr err rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .bindCallElse g args he hp hr err rest, σ, ρ, hscope, hh =>
      block_bindCallElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        g args he hp hr err rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hscope, hh =>
      block_bindAxiom_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        a args he hw hg hd hgd rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hscope, hh =>
      block_bindAxiomElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        a args he hr hw hg hd hgd err rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hscope, hh =>
      block_bindAxiomOpt_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e a args he hp hd hgd rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hscope, hh =>
      block_bindAxiomOptElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e a args he hp hd hgd hr err rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .regRead r hr rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => exact AusgangUnter.refl _
      | some v =>
          have heq := block_unter bo hbV rest _ (.cons v ρ) hscope_rest hh
          simp only [hx] at ⊢
          exact heq.schrumpf
  | .regReadElse r hr zusage sonst rest, σ, ρ, hscope, hh =>
      block_regReadElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        r hr zusage sonst rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV sonst σ ρ hs hh)
        σ ρ hscope hh
  | .awaits g hg hw hL hat rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock]
      by_cases hs : O.sichtbar g (σ.fragt (.inr (.inr g))) = true
      · rw [if_pos hs, if_pos hs]
        have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ hat.orte
        have heq := block_unter bo hbV rest _ _ hscope_rest (hl.heldB hh)
        exact heq.schrumpf
      · rw [if_neg hs, if_neg hs]; exact AusgangUnter.refl _
  | .exchange g neu hw hL rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (.inr g :: neu.orte)
      have g1 := hl.trans (treu_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw)
      have heq := block_unter bo hbV rest _ _ hscope_rest (g1.heldB hh)
      simp only [execBlock]
      exact heq.schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ, hscope, hh =>
      block_narrow_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e lo' hi' sonst rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV sonst σ ρ hs hh)
        σ ρ hscope hh
  | .narrowRequired e lo' hi' rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock]
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;>
        simp only [hc, dif_pos, dif_neg] at ⊢
      · exact (block_unter bo hbV rest _ _ hscope_rest (hl.heldB hh)).schrumpf
  | .check c sonst rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_sonst : sonst.ScopesOk := by scopes_treu
      simp only [execBlock]
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;>
        simp only [hc, ite_true, ite_false, Bool.true_eq_true, Bool.false_eq_true] at ⊢
      · exact block_unter bo hbV rest _ ρ hscope_rest (hl.heldB hh)
      · exact (end_unter bo hbV sonst _ ρ hscope_sonst (hl.heldB hh)).zuAusgang
  | .float op a b lo hi rest, σ, ρ, hscope, hh =>
      block_float_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        op a b lo hi rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .floatLit q lo hi rest, σ, ρ, hscope, hh =>
      block_floatLit_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        q lo hi rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .floatOf e lo hi rest, σ, ρ, hscope, hh =>
      block_floatOf_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e lo hi rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .floatNarrow e lo hi sonst rest, σ, ρ, hscope, hh =>
      block_floatNarrow_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e lo hi sonst rest
        (fun σ ρ hs hh => block_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV sonst σ ρ hs hh)
        σ ρ hscope hh
/-- **A terminal block under two gatedly-related handlers.** -/
theorem end_unter (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ), b.ScopesOk →
    HeldB bo Λ σ.haelt →
    EndUnter Er (execEnd O passes R₁ b σ ρ) (execEnd O passes R₂ b σ ρ)
  | .ret e _, _, _, _, _ => exact EndUnter.refl _
  | .retWhy .., _, _, _, _ => exact EndUnter.refl _
  | .retScoped e R, _, _, _, _ => exact EndUnter.refl _
  | .retWhyScoped _ R, _, _, _, _ => exact EndUnter.refl _
  | .leave .., _, _, _, _ => exact EndUnter.refl _
  | .next .., _, _, _, _ => exact EndUnter.refl _
  | .cons s rest, σ, ρ, hscope, hh =>
      end_cons_unter O passes R₁ R₂ hR hT₁ hO bo hbV s rest
        (fun σ ρ hs hh => stmt_unter bo hbV s σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bind e rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      have heq := end_unter bo hbV rest _ _ hscope_rest (hl.heldB hh)
      simp only [execEnd]
      exact heq.schrumpf
  | .bindCall g args he hp hr rest, σ, ρ, hscope, hh =>
      end_bindCall_unter O passes R₁ R₂ hR hT₁ hO bo hbV g args he hp hr rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindCallElse g args he hp hr err rest, σ, ρ, hscope, hh =>
      end_bindCallElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        g args he hp hr err rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hscope, hh =>
      end_bindAxiom_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        a args he hw hg hd hgd rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hscope, hh =>
      end_bindAxiomElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        a args he hr hw hg hd hgd err rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hscope, hh =>
      end_bindAxiomOpt_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e a args he hp hd hgd rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hscope, hh =>
      end_bindAxiomOptElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e a args he hp hd hgd hr err rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .regRead r hr rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execEnd]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => exact EndUnter.refl _
      | some v =>
          have heq := end_unter bo hbV rest _ (.cons v ρ) hscope_rest hh
          simp only [hx] at ⊢
          exact heq.schrumpf
  | .regReadElse r hr zusage sonst rest, σ, ρ, hscope, hh =>
      end_regReadElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        r hr zusage sonst rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV sonst σ ρ hs hh)
        σ ρ hscope hh
  | .awaits g hg hw hL hat rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execEnd]
      by_cases hs : O.sichtbar g (σ.fragt (.inr (.inr g))) = true
      · rw [if_pos hs, if_pos hs]
        have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ hat.orte
        have heq := end_unter bo hbV rest _ _ hscope_rest (hl.heldB hh)
        exact heq.schrumpf
      · rw [if_neg hs, if_neg hs]; exact EndUnter.refl _
  | .bindCallInd p args he hp hr rest, σ, ρ, hscope, hh =>
      end_bindCallInd_unter O passes R₁ R₂ hR hT₁ hO bo hbV p args he hp hr rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        σ ρ hscope hh
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hscope, hh =>
      end_bindCallIndElse_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        p args he hp hr err rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV err σ ρ hs hh)
        σ ρ hscope hh
  | .narrow e lo' hi' sonst rest, σ, ρ, hscope, hh =>
      end_narrow_unter O passes R₁ R₂ hR hT₁ hO bo hbV
        e lo' hi' sonst rest
        (fun σ ρ hs hh => end_unter bo hbV rest σ ρ hs hh)
        (fun σ ρ hs hh => end_unter bo hbV sonst σ ρ hs hh)
        σ ρ hscope hh
  | .narrowRequired e lo' hi' rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execEnd]
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;>
        simp only [hc, dif_pos, dif_neg] at ⊢
      · exact (end_unter bo hbV rest _ _ hscope_rest (hl.heldB hh)).schrumpf
  | .exchange g neu hw hL rest, σ, ρ, hscope, hh => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (.inr g :: neu.orte)
      have g1 := hl.trans (treu_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw)
      have heq := end_unter bo hbV rest _ _ hscope_rest (g1.heldB hh)
      simp only [execEnd]
      exact heq.schrumpf
  | .ite c t e, σ, ρ, hscope, hh => by
      have hscope_t : t.ScopesOk := by scopes_treu
      have hscope_e : e.ScopesOk := by scopes_treu
      simp only [execEnd]
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;>
        simp only [hc, ite_true, ite_false] at ⊢
      · exact end_unter bo hbV t _ _ hscope_t (hl.heldB hh)
      · exact end_unter bo hbV e _ _ hscope_e (hl.heldB hh)
end
end KongruenzDisz
end Gabbro.Grammatik