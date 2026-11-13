/-
  File:      stage0/Stage0/Senke/Bild/Gleich/FaelleStmt.lean
  Subject:   Package P1 of the closed calls of the image theorem, part 5: every statement form, given the statement
             for its direct sub-terms (`StmtKinder`), runs under `R₁` and `R₂` from `≈` worlds to related outcomes.
             Reads keep `≈` (`WeltGleich.lese`), expressions do not see the trace (`WeltGleich.wert'`), writes and
             lock moves are the same on both sides, calls are related by `HandlerLG`, register and visibility answers
             by `LeseblindRS`, foreign answers by `LeseblindW` (needed only at a foreign call: the alternative of
             `axFrei`).
-/
module
public import Stage0.Senke.Bild.Gleich.Ziele
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {O : Orakel D} {passes : Nat} {Er : Fehlermarke D → Prop}
  {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {V : Vertrag D}

theorem stmt_lg (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ'),
      (s.axFrei = true ∨ LeseblindW O) → StmtKinder O passes Er R₁ R₂ s → StmtLG O passes Er R₁ R₂ s
  | .assignSlot _ _ i e _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert' i ρ, h'.wert' e ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignThru p _ _ _ i e _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert' i ρ, h'.wert' e ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignThruOwn p _ _ _ i e _ _ _ _ _ _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert' i ρ, h'.wert' e ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignSlotRef r _ _ _ _ e _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (r.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert' r ρ, h'.wert' e ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignGlob _ e _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execStmt]
      rw [h'.wert' e ρ]
      exact .ok (h'.schreibGlob _ _ _)
  | .putBytes t f hf _ i _ _ e _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert' i ρ, h'.wert' e ρ]
      exact .ok (WeltGleich.schreibBytes t f hf Λ _ _ h')
  | .assignVar _ e, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execStmt]
      rw [h'.wert' e ρ]
      exact .ok h'
  | .shift t _ _ i _ _ _ _ _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (.inl t :: i.orte)
      simp only [execStmt]
      rw [h'.wert' i ρ, h'.slots]
      exact AusLG.ite (.ok (h'.schreibSlot _ _ _ _ _)) (.logik _)
  | .ite c _ _, _, hk => by
      obtain ⟨iht, ihe⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ c.orte
      simp only [execStmt]
      rw [h'.wert' c ρ]
      exact AusLG.ite (iht _ _ ρ h') (ihe _ _ ρ h')
  | .onOption o _ _, _, hk => by
      obtain ⟨ihp, iha⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ o.orte
      simp only [execStmt]
      rw [h'.wert' o ρ]
      cases hv : (eval (σ₂.lese Λ o.orte) o (σ₂.lese Λ o.orte) ρ : Option _) with
      | none => exact iha _ _ ρ h'
      | some k => exact (ihp _ _ (.cons k ρ) h').schrumpf
  | .onTag v _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ v.orte
      simp only [execStmt]
      rw [h'.wert' v ρ]
      exact hk _ _ _ ρ h'
  | .onWhy r _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ r.orte
      simp only [execStmt]
      rw [h'.wert' r ρ]
      exact hk _ _ _ ρ h'
  | .call f args _ hr, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execStmt]
      rw [h'.werte args ρ]
      have hc := hR f _ _ (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ) h'
      generalize R₁ f (σ₁.lese Λ args.orte) _ = a₁ at hc ⊢
      generalize R₂ f (σ₂.lese Λ args.orte) _ = a₂ at hc ⊢
      cases hc with
      | ok hw => exact .ok hw
      | @why _ _ r _ => exact keinGrund hr r
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE
  | .callInd p args _ hr, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (p.orte ++ args.orte)
      simp only [execStmt]
      rw [h'.wert' p ρ, h'.werte args ρ]
      generalize eval (σ₂.lese Λ (p.orte ++ args.orte)) p (σ₂.lese Λ (p.orte ++ args.orte)) ρ = w
      obtain ⟨g, hg⟩ := w
      dsimp only
      have hc := hR g _ _ (umsig hg (evalArgs (σ₂.lese Λ (p.orte ++ args.orte)) args
        (σ₂.lese Λ (p.orte ++ args.orte)) ρ)) h'
      generalize R₁ g (σ₁.lese Λ (p.orte ++ args.orte)) _ = a₁ at hc ⊢
      generalize R₂ g (σ₂.lese Λ (p.orte ++ args.orte)) _ = a₂ at hc ⊢
      cases hc with
      | ok hw => exact .ok hw
      | @why _ _ r _ => exact keinGrundSig hg hr r
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE
  | .callIndElse p args he _ hr _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (p.orte ++ args.orte)
      simp only [execStmt]
      refine indSonst_lg hR p args he hr h' ρ ?_ ?_
      · intro _ _ _ hw
        exact .ok hw
      · intro _ _ r hw
        exact (hk _ _ (.cons r ρ) hw).schrumpf.zuAusgang
  | .locks L _ _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      have hb := hk _ _ ρ (hσ.nimmt L)
      generalize execBlock O passes R₁ _ (σ₁.nimmt L) ρ = o₁ at hb ⊢
      generalize execBlock O passes R₂ _ (σ₂.nimmt L) ρ = o₂ at hb ⊢
      cases hb with
      | ok hw => exact .ok (hw.gibt L)
      | zurueck hw => exact .zurueck hw
      | why hw => exact .why hw
      | leave hw => exact .leave (hw.gibt L)
      | next hw => exact .next (hw.gibt L)
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE
  | .breaking _ _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact hk _ _ ρ hσ
  | .traverse _ inv _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      refine traverseLauf_lg ?_ (funLG_lese inv wahr?) _ _ _ ρ hσ
      intro a b c hw
      exact hk a b c hw
  | .consumeTraverse t member edge inv bound mass _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      refine verbrauchLauf_lg t ?_ (funLG_lese inv wahr?) (funLG_verbrauchSel t member edge)
        (funLG_lese mass (fun v => v.n)) bound _ _ _ ρ hσ
      intro a b c hw
      exact hk a b c hw
  | .retry n bis _ _, _, hk => by
      obtain ⟨ihb, ihu⟩ := hk
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      refine retryLauf_lg ?_ (funLG_lese bis wahr?) ?_ n _ _ ρ hσ
      · intro a b c hw
        exact ihb a b c hw
      · intro a b c hw
        exact ihu a b c hw
  | .forever a inv _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      refine foreverLauf_lg a ?_ (funLG_lese inv wahr?) passes _ _ ρ hσ
      intro x y c hw
      exact hk x y c hw
  | .axiomCall a args _ _ _ _ _, hX, _ => by
      have hW : LeseblindW O := hX.resolve_left Bool.false_ne_true
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execStmt]
      rw [h'.werte args ρ]
      have hp := paarLG_axiomAntwort hW a h' (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ)
      generalize axiomAntwort O a (σ₁.lese Λ args.orte) _ = A at hp ⊢
      generalize axiomAntwort O a (σ₂.lese Λ args.orte) _ = B at hp ⊢
      cases hp with
      | @mk σa σb x hw =>
        cases x with
        | none => exact .hardware _
        | some _ => exact .ok hw
  | .axiomCallElse _ a args _ _ _ _ _ _, hX, hk => by
      have hW : LeseblindW O := hX.resolve_left Bool.false_ne_true
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execStmt]
      rw [h'.werte args ρ]
      have hp := paarLG_axiomAntwortSonst hW a h'
        (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ)
      generalize axiomAntwortSonst O a (σ₁.lese Λ args.orte) _ = A at hp ⊢
      generalize axiomAntwortSonst O a (σ₂.lese Λ args.orte) _ = B at hp ⊢
      cases hp with
      | @mk σa σb x hw =>
        rcases x with _ | v | r
        · exact .hardware _
        · exact .ok hw
        · exact (hk _ _ (.cons r ρ) hw).schrumpf.zuAusgang
  | .regWrite _ _ e, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .ok (hσ.lese Λ e.orte)
  | .transition _ _ m _ _ _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .ok (hσ.fragt (.inr (.inl m)))
  | .publish _ e _ _ _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execStmt]
      rw [h'.wert' e ρ]
      exact .ok (h'.schreibGlob _ _ _)
  | .advances _ _ _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .ok hσ
  | .retires _ _ _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .ok hσ
  | .ret e _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execStmt]
      rw [h'.ergebnis e ρ]
      exact .zurueck h'
  | .retWhy _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .why hσ
  | .leave _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .leave hσ
  | .next _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .next hσ
  | .retScoped e _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execStmt]
      rw [h'.ergebnis e ρ]
      exact .zurueck (WeltGleich.gibt_foldl _ h')
  | .retWhyScoped _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execStmt]
      exact .why (WeltGleich.gibt_foldl _ hσ)

end Gabbro.Stage0.Senke.BildLauf
