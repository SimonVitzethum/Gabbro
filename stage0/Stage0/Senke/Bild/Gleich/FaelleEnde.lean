/-
  File:      stage0/Stage0/Senke/Bild/Gleich/FaelleEnde.lean
  Subject:   Package P1 of the closed calls of the image theorem, part 7: every terminal-block form, given the
             statement for its direct sub-terms (`EndeKinder`), runs under `R₁` and `R₂` from `≈` worlds to related
             outcomes.
-/
module
public import Stage0.Senke.Bild.Gleich.Ziele
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {O : Orakel D} {passes : Nat} {Er : Fehlermarke D → Prop}
  {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {V : Vertrag D}

theorem ende_lg (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ (b : Endblock D V l Γ Λ),
      (b.axFrei = true ∨ LeseblindW O) → EndeKinder O passes Er R₁ R₂ b → EndeLG O passes Er R₁ R₂ b
  | .ret e _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execEnd]
      rw [h'.ergebnis e ρ]
      exact .zurueck h'
  | .retWhy _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execEnd]
      exact .why hσ
  | .leave _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execEnd]
      exact .leave hσ
  | .next _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execEnd]
      exact .next hσ
  | .retScoped e _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execEnd]
      rw [h'.ergebnis e ρ]
      exact .zurueck (WeltGleich.gibt_foldl _ h')
  | .retWhyScoped _ _, _, _ => by
      intro σ₁ σ₂ ρ hσ
      simp only [execEnd]
      exact .why (WeltGleich.gibt_foldl _ hσ)
  | .cons s _, _, hk => by
      obtain ⟨ihs, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      simp only [execEnd]
      have hs := ihs _ _ ρ hσ
      generalize execStmt O passes R₁ s σ₁ ρ = o₁ at hs ⊢
      generalize execStmt O passes R₂ s σ₂ ρ = o₂ at hs ⊢
      cases hs with
      | @ok σa σb ρa hw => exact ihr _ _ ρa hw
      | zurueck hw => exact .zurueck hw
      | why hw => exact .why hw
      | leave hw => exact .leave hw
      | next hw => exact .next hw
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE
  | .bind e _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execEnd]
      rw [h'.wert' e ρ]
      exact (hk _ _ _ h').schrumpf
  | .bindCall f args _ _ hr _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execEnd]
      rw [h'.werte args ρ]
      have hc := hR f _ _ (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ) h'
      generalize R₁ f (σ₁.lese Λ args.orte) _ = a₁ at hc ⊢
      generalize R₂ f (σ₂.lese Λ args.orte) _ = a₂ at hc ⊢
      cases hc with
      | ok hw => exact (hk _ _ _ hw).schrumpf
      | @why _ _ r _ => exact keinGrund hr r
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE
  | .bindCallElse f args _ _ _ _ _, _, hk => by
      obtain ⟨ihe, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execEnd]
      rw [h'.werte args ρ]
      have hc := hR f _ _ (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ) h'
      generalize R₁ f (σ₁.lese Λ args.orte) _ = a₁ at hc ⊢
      generalize R₂ f (σ₂.lese Λ args.orte) _ = a₂ at hc ⊢
      cases hc with
      | ok hw => exact (ihr _ _ _ hw).schrumpf
      | why hw => exact (ihe _ _ _ hw).schrumpf
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE
  | .bindCallInd p args _ _ hr _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (p.orte ++ args.orte)
      simp only [execEnd]
      rw [h'.wert' p ρ, h'.werte args ρ]
      generalize eval (σ₂.lese Λ (p.orte ++ args.orte)) p (σ₂.lese Λ (p.orte ++ args.orte)) ρ = w
      obtain ⟨g, hg⟩ := w
      dsimp only
      have hc := hR g _ _ (umsig hg (evalArgs (σ₂.lese Λ (p.orte ++ args.orte)) args
        (σ₂.lese Λ (p.orte ++ args.orte)) ρ)) h'
      generalize R₁ g (σ₁.lese Λ (p.orte ++ args.orte)) _ = a₁ at hc ⊢
      generalize R₂ g (σ₂.lese Λ (p.orte ++ args.orte)) _ = a₂ at hc ⊢
      cases hc with
      | ok hw => exact (hk _ _ _ hw).schrumpf
      | @why _ _ r _ => exact keinGrundSig hg hr r
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE
  | .bindCallIndElse p args he _ hr _ _, _, hk => by
      obtain ⟨ihe, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (p.orte ++ args.orte)
      simp only [execEnd]
      refine indSonstE_lg hR p args he hr h' ρ ?_ ?_
      · intro _ _ _ hw
        exact (ihr _ _ _ hw).schrumpf
      · intro _ _ _ hw
        exact (ihe _ _ _ hw).schrumpf
  | .bindAxiom a args _ _ _ _ _ _, hX, hk => by
      have hW : LeseblindW O := hX.resolve_left Bool.false_ne_true
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execEnd]
      rw [h'.werte args ρ]
      have hp := paarLG_axiomAntwort hW a h' (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ)
      generalize axiomAntwort O a (σ₁.lese Λ args.orte) _ = A at hp ⊢
      generalize axiomAntwort O a (σ₂.lese Λ args.orte) _ = B at hp ⊢
      cases hp with
      | @mk σa σb x hw =>
        cases x with
        | none => exact .hardware _
        | some _ => exact (hk _ _ _ hw).schrumpf
  | .bindAxiomElse a args _ _ _ _ _ _ _ _, hX, hk => by
      have hW : LeseblindW O := hX.resolve_left Bool.false_ne_true
      obtain ⟨ihe, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execEnd]
      rw [h'.werte args ρ]
      have hp := paarLG_axiomAntwortSonst hW a h'
        (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ)
      generalize axiomAntwortSonst O a (σ₁.lese Λ args.orte) _ = A at hp ⊢
      generalize axiomAntwortSonst O a (σ₂.lese Λ args.orte) _ = B at hp ⊢
      cases hp with
      | @mk σa σb x hw =>
        rcases x with _ | v | r
        · exact .hardware _
        · exact (ihr _ _ _ hw).schrumpf
        · exact (ihe _ _ _ hw).schrumpf
  | .bindAxiomOpt e a args _ _ _ _ _, hX, hk => by
      have hW : LeseblindW O := hX.resolve_left Bool.false_ne_true
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execEnd]
      rw [h'.werte args ρ]
      have hp := paarLG_axiomAntwort hW a h' (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ)
      generalize axiomAntwort O a (σ₁.lese Λ args.orte) _ = A at hp ⊢
      generalize axiomAntwort O a (σ₂.lese Λ args.orte) _ = B at hp ⊢
      cases hp with
      | @mk σa σb x hw =>
        cases x with
        | none => exact .hardware _
        | some _ => exact (hk _ _ _ hw).weiterOpt e
  | .bindAxiomOptElse e a args _ _ _ _ _ _ _, hX, hk => by
      have hW : LeseblindW O := hX.resolve_left Bool.false_ne_true
      obtain ⟨ihe, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ args.orte
      simp only [execEnd]
      rw [h'.werte args ρ]
      have hp := paarLG_axiomAntwortSonst hW a h'
        (evalArgs (σ₂.lese Λ args.orte) args (σ₂.lese Λ args.orte) ρ)
      generalize axiomAntwortSonst O a (σ₁.lese Λ args.orte) _ = A at hp ⊢
      generalize axiomAntwortSonst O a (σ₂.lese Λ args.orte) _ = B at hp ⊢
      cases hp with
      | @mk σa σb x hw =>
        rcases x with _ | v | r
        · exact .hardware _
        · exact (ihr _ _ _ hw).weiterOpt e
        · exact (ihe _ _ _ hw).schrumpf
  | .regRead r _ _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have hf := hσ.fragt (.inr (.inl r))
      simp only [execEnd]
      rw [hO.regLies r _ _ hf]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ₂.fragt (.inr (.inl r)))) with
      | none => exact .hardware _
      | some v => exact EndLG.ite ((hk _ _ (.cons v ρ) hf).schrumpf) (.hardware _)
  | .regReadElse r _ zusage _ _, _, hk => by
      obtain ⟨ihs, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have hf := hσ.fragt (.inr (.inl r))
      simp only [execEnd]
      rw [hO.regLies r _ _ hf]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ₂.fragt (.inr (.inl r)))) with
      | none => exact .hardware _
      | some v =>
          have h'' := hf.lese Λ zusage.orte
          exact EndLG.ite_eq (congrArg wahr? (h''.wert' zusage (.cons v ρ)))
            ((ihr _ _ (.cons v ρ) h'').schrumpf) (ihs _ _ ρ h'')
  | .awaits g _ _ _ _ _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have hf := hσ.fragt (.inr (.inr g))
      have h'' := hf.lese Λ [.inr g]
      simp only [execEnd]
      rw [hO.sichtbar g _ _ hf, h''.globs]
      exact EndLG.ite ((hk _ _ _ h'').schrumpf) (.hardware _)
  | .exchange g neu _ _ _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (.inr g :: neu.orte)
      simp only [execEnd]
      rw [h'.globs, h'.wert' neu]
      exact (hk _ _ _ (h'.schreibGlob _ _ _)).schrumpf
  | .narrow e lo hi _ _, _, hk => by
      obtain ⟨ihs, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      have hn := congrArg Zahl.n (h'.wert' e ρ)
      by_cases h₁ : lo ≤ (eval (σ₁.lese Λ e.orte) e (σ₁.lese Λ e.orte) ρ).n ∧
          (eval (σ₁.lese Λ e.orte) e (σ₁.lese Λ e.orte) ρ).n ≤ hi
      · have h₂ : lo ≤ (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ∧
            (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ≤ hi := hn ▸ h₁
        simp only [execEnd, dif_pos h₁, dif_pos h₂]
        have hv : (⟨_, h₁.1, h₁.2⟩ : Zahl lo hi) = ⟨_, h₂.1, h₂.2⟩ := zahl_ext hn
        rw [hv]
        exact (ihr _ _ _ h').schrumpf
      · have h₂ : ¬ (lo ≤ (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ∧
            (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ≤ hi) := hn ▸ h₁
        simp only [execEnd, dif_neg h₁, dif_neg h₂]
        exact ihs _ _ ρ h'
  | .narrowRequired e lo hi _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      have hn := congrArg Zahl.n (h'.wert' e ρ)
      by_cases h₁ : lo ≤ (eval (σ₁.lese Λ e.orte) e (σ₁.lese Λ e.orte) ρ).n ∧
          (eval (σ₁.lese Λ e.orte) e (σ₁.lese Λ e.orte) ρ).n ≤ hi
      · have h₂ : lo ≤ (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ∧
            (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ≤ hi := hn ▸ h₁
        simp only [execEnd, dif_pos h₁, dif_pos h₂]
        have hv : (⟨_, h₁.1, h₁.2⟩ : Zahl lo hi) = ⟨_, h₂.1, h₂.2⟩ := zahl_ext hn
        rw [hv]
        exact (hk _ _ _ h').schrumpf
      · have h₂ : ¬ (lo ≤ (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ∧
            (eval (σ₂.lese Λ e.orte) e (σ₂.lese Λ e.orte) ρ).n ≤ hi) := hn ▸ h₁
        simp only [execEnd, dif_neg h₁, dif_neg h₂]
        exact .logik _
  | .ite c _ _, _, hk => by
      obtain ⟨iht, ihe⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ c.orte
      simp only [execEnd]
      rw [h'.wert' c ρ]
      exact EndLG.ite (iht _ _ ρ h') (ihe _ _ ρ h')
  | .float _ a b lo hi _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ (a.orte ++ b.orte)
      simp only [execEnd]
      rw [h'.wert' a ρ, h'.wert' b ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact .logik _
      | some _ => exact (hk _ _ _ h').schrumpf
  | .floatLit q lo hi _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      simp only [execEnd]
      generalize gleitPasst lo hi (bruch q) = x
      cases x with
      | none => exact .logik _
      | some _ => exact (hk _ _ _ hσ).schrumpf
  | .floatOf e lo hi _, _, hk => by
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execEnd]
      rw [h'.wert' e ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact .logik _
      | some _ => exact (hk _ _ _ h').schrumpf
  | .floatNarrow e lo hi _ _, _, hk => by
      obtain ⟨ihs, ihr⟩ := hk
      intro σ₁ σ₂ ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execEnd]
      rw [h'.wert' e ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact ihs _ _ ρ h'
      | some _ => exact (ihr _ _ _ h').schrumpf

end Gabbro.Stage0.Senke.BildLauf
