module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil4
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil4a

@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
variable {D D' : Deklaration}
namespace Einbettung
variable (E : Einbettung D D')
variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)
section Sim
variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

set_option linter.unusedSectionVars false in
theorem sim_end_bindCallElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (τ)
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    (ih_sim_end_err : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err) (execEndHA S' O' U' A' passes R' (exEnd hS err)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCallElse (τ := τ) f args he hp hr err rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.bindCallElse (τ := τ) f args he hp hr err rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
    (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
    ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
  generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
    (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
    · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
        execEnd_umΛ]
      exact E.endRel_schrumpf hR3
  · have hc : (Ty.why (D.gruende f) :: Γ).map E.tyE = Ty.why (D'.gruende (E.fn f)) :: Γ.map E.tyE := by
      rw [gruendeE hS]; rfl
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_err M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (Fin.cast (gruendeE hS f) r') ρ) (castE hc.symm (.cons r' ρ'))
      (hI2 W)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [gruendeE hS])
        (by rw [castW_why]; rfl)))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
    · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
        execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3)
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      trivial

set_option linter.unusedSectionVars false in
theorem sim_end_bindAxiom {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (τ)
    (a)
    (args)
    (he)
    (hw)
    (hg)
    (hd)
    (hgd)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindAxiom (τ := τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.bindAxiom (τ := τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' (hI.fragt E (.inl a) (.inl (E.ax a))) a (evalArgs σ₁ args σ₁ ρ)
  have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
  have hw' := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a)
  have he' : D'.aerg (E.ax a) = some (E.tyE τ) := by rw [E.aerg, he]; rfl
  cases hx : einpassenErg (fun _ => Option.none) (D.aerg a) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with
  | none =>
      refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
        rw [hx]
      · simp only [exEnd, execEndHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
          evalArgs_umτs, hargs, aparamsUm_falt, hw']
        rw [hx]
        trivial
  | some v =>
      obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_rest M₂ (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
        (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
        (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
      refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
      · simp only [execEndHA, axiomAntwort, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
          hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
        rw [hx]
        exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
      · simp only [exEnd, execEndHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
          evalArgs_umτs, hargs, aparamsUm_falt, hw']
        rw [hx]
        exact E.endRel_schrumpf hR3

set_option linter.unusedSectionVars false in
theorem sim_end_bindAxiomElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (τ)
    (a)
    (args)
    (he)
    (hr)
    (hw)
    (hg)
    (hd)
    (hgd)
    (err)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    (ih_sim_end_err : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err) (execEndHA S' O' U' A' passes R' (exEnd hS err)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' (hI.fragt E (.inl a) (.inl (E.ax a))) a (evalArgs σ₁ args σ₁ ρ)
  have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
  have hw' := E.axiomSonst_wert hZ (fun _ => Option.none) O'.zeiger a (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a) (E.agruende a)
  have he' : D'.aerg (E.ax a) = some (E.tyE τ) := by rw [E.aerg, he]; rfl
  rcases hx : sonstPasst (fun _ => Option.none) (D.aerg a) (D.agruende a) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with _ | (v | r)
  · refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, axiomAntwortSonst, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
      rw [hx]
    · simp only [exEnd, execEndHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, hw']
      rw [hx]
      trivial
  · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_rest M₂ (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
      (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
      (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
        hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
      rw [hx]
      exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
    · simp only [exEnd, execEndHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, hw']
      rw [hx]
      exact E.endRel_schrumpf hR3
  · have hc : (Ty.why (D.agruende a) :: Γ).map E.tyE = Ty.why (D'.agruende (E.ax a)) :: Γ.map E.tyE := by
      rw [E.agruende]; rfl
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_err M₂ (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
      (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) ρ'))
      (E.inv_antwort hZ hB.pad hI2 _)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [E.agruende])
        (by rw [castW_why]; exact Fin.ext rfl)))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
        hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
      rw [hx]
      exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
    · simp only [exEnd, execEndHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, hw']
      rw [hx]
      simp only [execEnd_umΓ]
      exact E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3)

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
