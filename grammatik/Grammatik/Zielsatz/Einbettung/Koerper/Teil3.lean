module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil2

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
theorem sim_block_bindCallInd {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (n)
    (τ)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCallInd (n := n) (τ := τ) p args he hp hr rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bindCallInd (n := n) (τ := τ) p args he hp hr rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
  have hp' := hev p ρ ρ' hρ
  rw [hvd] at hp'
  rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
  rw [hvd'] at hp'
  have hk : E.Konform hZ f f' := by
    rcases hp' with h | ⟨hz, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hz, hr, hf'⟩
  have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
    (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
    (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
  generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · have he₁ : D.erg f = some τ := ergSig hf he
    have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
      rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
    have he' : D'.erg f' = some (E.tyE τ) := ergSig hf' heS
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_block_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he₁ (E.ergZ hZ (D.erg f) (castV (konform_sig hS hk).2.1 v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (konform_sig hS hk).2.1.symm he₁ he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha,
        execBlock_vorΛ]
      exact E.ausRel_schrumpf hR3
  · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
    exact (Fin.cast h0 r').elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      trivial

set_option linter.unusedSectionVars false in
theorem sim_block_bindCallElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (τ)
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_err : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err) (execEndHA S' O' U' A' passes R' (exEnd hS err)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCallElse (τ := τ) f args he hp hr err rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bindCallElse (τ := τ) f args he hp hr err rest : Block D V l Γ Λ Λ'))) :=
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
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_block_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
    · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
        execBlock_vorΛ]
      exact E.ausRel_schrumpf hR3
  · have hc : (Ty.why (D.gruende f) :: Γ).map E.tyE = Ty.why (D'.gruende (E.fn f)) :: Γ.map E.tyE := by
      rw [gruendeE hS]; rfl
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_err M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (Fin.cast (gruendeE hS f) r') ρ) (castE hc.symm (.cons r' ρ'))
      (hI2 W)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [gruendeE hS])
        (by rw [castW_why]; rfl)))
    refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
    · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
        execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      trivial

set_option linter.unusedSectionVars false in
theorem sim_block_bindAxiom {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (τ)
    (a)
    (args)
    (he)
    (hw)
    (hg)
    (hd)
    (hgd)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindAxiom (τ := τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bindAxiom (τ := τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ'))) :=
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
      · simp only [execBlockHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
        rw [hx]
      · simp only [exB, execBlockHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
          evalArgs_umτs, hargs, aparamsUm_falt, hw']
        rw [hx]
        trivial
  | some v =>
      obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_block_rest M₂ (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
        (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
        (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
      refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, axiomAntwort, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
          hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
        rw [hx]
        exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
      · simp only [exB, execBlockHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
          evalArgs_umτs, hargs, aparamsUm_falt, hw']
        rw [hx]
        exact E.ausRel_schrumpf hR3

set_option linter.unusedSectionVars false in
theorem sim_block_bindAxiomElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
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
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_err : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err) (execEndHA S' O' U' A' passes R' (exEnd hS err)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bindAxiomElse (τ := τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ'))) :=
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
    · simp only [execBlockHA, axiomAntwortSonst, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
      rw [hx]
    · simp only [exB, execBlockHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, hw']
      rw [hx]
      trivial
  · obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_block_rest M₂ (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
      (.cons (ergWert he v) ρ) (.cons (ergWert he' (castV (E.aerg a).symm (E.ergE _ v))) ρ')
      (E.inv_antwort hZ hB.pad hI2 _) (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergE hZ (E.aerg a) he he' v))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
        hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
      rw [hx]
      exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
    · simp only [exB, execBlockHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, hw']
      rw [hx]
      exact E.ausRel_schrumpf hR3
  · have hc : (Ty.why (D.agruende a) :: Γ).map E.tyE = Ty.why (D'.agruende (E.ax a)) :: Γ.map E.tyE := by
      rw [E.agruende]; rfl
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_err M₂ (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1
      (.cons r ρ) (castE hc.symm (.cons (Fin.cast (E.agruende a).symm r) ρ'))
      (E.inv_antwort hZ hB.pad hI2 _)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ (by rw [E.agruende])
        (by rw [castW_why]; exact Fin.ext rfl)))
    refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, axiomAntwortSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)),
        hOΦ Φ (passt_teil hP hs3), orakelΦ_zeiger]
      rw [hx]
      exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
    · simp only [exB, execBlockHA, axiomAntwortSonst, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
        evalArgs_umτs, hargs, aparamsUm_falt, hw']
      rw [hx]
      simp only [execEnd_umΓ]
      exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))

set_option linter.unusedSectionVars false in
theorem sim_block_regRead {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.regRead r hk rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.regRead r hk rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel (hM.fragt E (.inr (.inl r)) (.inr (.inl (E.reg r))))
  have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) (E.rtyp r)
  have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
    rw [List.map_cons, E.rtyp]
  cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) with
  | none =>
      refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
        rw [hx]
      · simp only [exB, execBlockHA]
        rw [hw'.1 hx]
        trivial
  | some v =>
      have hz := hS.rzusage r v
      cases hzv : D.rzusage r v
      · refine ⟨_, .hardware (.geraet r), hs1, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
          rw [hx]
          simp only [hzv, Bool.false_eq_true, ↓reduceIte]
        · simp only [exB, execBlockHA]
          rw [hw'.2 v hx]
          simp only [hz, hzv, Bool.false_eq_true, ↓reduceIte]
          trivial
      · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_block_rest)
          _ (σ.fragt (.inr (.inl r))) (σ'.fragt (.inr (.inl (E.reg r)))) (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hk1
          (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
        refine ⟨M₂, o.schrumpf, teil_trans hs1 hs2, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ (passt_teil hP hs2)]
          rw [hx]
          simp only [hzv, ↓reduceIte]
          exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
        · simp only [exB, execBlockHA]
          rw [hw'.2 v hx]
          simp only [hz, hzv, ↓reduceIte]
          exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_regReadElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_sonst : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') sonst) (execEndHA S' O' U' A' passes R' (exEnd hS sonst)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨hk1, hs1, hΦ1⟩ := E.schluessel (hM.fragt E (.inr (.inl r)) (.inr (.inl (E.reg r))))
  have hw' := E.regLies_wert hZ (fun _ => Option.none) O'.zeiger r (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) (E.rtyp r)
  have hc : (D.rtyp r :: Γ).map E.tyE = D'.rtyp (E.reg r) :: Γ.map E.tyE := by
    rw [List.map_cons, E.rtyp]
  cases hx : einpassen (fun _ => Option.none) (D.rtyp r) (O'.regLies (E.reg r) (σ'.fragt (.inr (.inl (E.reg r))))) with
  | none =>
      refine ⟨_, .hardware (.register r), hs1, fun Φ hP => ?_, ?_⟩
      · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger, hΦ1 Φ hP]
        rw [hx]
      · simp only [exB, execBlockHA]
        rw [hw'.1 hx]
        trivial
  | some v =>
      obtain ⟨M₂, σ₁, hs2, hΦ2, hI, hev⟩ := E.lese_eval hZ hk1 T hB.havocA hB.atom Λ (Λ.map E.resE)
        zusage.orte
      have hev0 := E.frei_alle hZ (@hev) hρ
      have hrel := (E.envR_um hZ hc.symm (.cons v ρ)
          (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ' : Env D' (D'.rtyp (E.reg r) :: Γ.map E.tyE))).mpr
          (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
      have hz' := E.frei_eq hZ (hev zusage _ _ hrel) rfl
      cases hb : wahr? (eval σ₁ zusage σ₁ (.cons v ρ))
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := ih_sim_end_sonst M₂ σ₁ _ ρ ρ' hI hρ
        refine ⟨M₃, o.zuAusgang, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger,
            hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
          rw [hx]
          simp only [hΦ2 Φ (passt_teil hP hs3), hb, Bool.false_eq_true, ↓reduceIte]
          exact congrArg EndAusgang.zuAusgang (hΦ3 Φ hP)
        · simp only [exB, execBlockHA]
          rw [hw'.2 v hx]
          simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb,
            Bool.false_eq_true, ↓reduceIte]
          exact E.endRel_zuAusgang hR
      · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_block_rest)
          M₂ σ₁ _ (.cons v ρ) (.cons ((E.rtyp r).symm ▸ E.valE _ v) ρ') hI
          (E.envR_cons hZ hρ _ _ (E.rtyp r) (E.vrel_um hZ (E.rtyp r) (E.vrel_valE hZ _ v)))
        refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs1 hs2) hs3, fun Φ hP => ?_, ?_⟩
        · simp only [execBlockHA, orakelΦ_regLies, orakelΦ_zeiger,
            hΦ1 Φ (passt_teil hP (teil_trans hs2 hs3))]
          rw [hx]
          simp only [hΦ2 Φ (passt_teil hP hs3), hb, ↓reduceIte]
          exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
        · simp only [exB, execBlockHA]
          rw [hw'.2 v hx]
          simp only [Expr.orte_umΓ, Einbettung.orte_exE, eval_umΓ, hz', wahr_valE, hb, ↓reduceIte]
          exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_awaits {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T (hM.fragt E (.inr (.inr g)) (.inr (.inr (E.glob g)))) hB.havocA hB.atom Λ (Λ.map E.resE)
    [Sum.inr g] [Sum.inr (E.glob g)] rfl
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨hk2, hs2, hΦ2⟩ := E.schluessel hI
  have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
    rw [List.map_cons, E.gtyp]
  have hzf := hZ.frei.atomFrei g hat
  cases hvis : O'.sichtbar (E.glob g) (leseA A' (σ'.fragt (.inr (.inr (E.glob g)))) (Λ.map E.resE) [Sum.inr (E.glob g)])
  · refine ⟨_, .hardware (.sichtbarkeit D.a10), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), orakelΦ_sichtbar, hzf, hΦ2 Φ hP, hvis,
        Bool.false_eq_true, ↓reduceIte]
    · simp only [exB, execBlockHA, hvis, Bool.false_eq_true, ↓reduceIte]
      trivial
  · obtain ⟨M₃, o, hs3, hΦ3, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_block_rest)
      _ σ₁ _ (.cons (σ₁.globs g) ρ) (.cons ((leseA A' (σ'.fragt (.inr (.inr (E.glob g)))) (Λ.map E.resE) [Sum.inr (E.glob g)]).globs
        (E.glob g)) ρ') hk2 (E.envR_cons hZ hρ _ _ (E.gtyp g) (hk2.treu.2 g))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), orakelΦ_sichtbar, hzf,
        hΦ2 Φ (passt_teil hP hs3), hvis, ↓reduceIte]
      exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
    · simp only [exB, execBlockHA, hvis, ↓reduceIte]
      exact E.ausRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_block_exchange {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.exchange g neu hw hL rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.exchange g neu hw hL rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (Sum.inr g :: neu.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  have hc : (D.gtyp g :: Γ).map E.tyE = D'.gtyp (E.glob g) :: Γ.map E.tyE := by
    rw [List.map_cons, E.gtyp]
  have hrel := E.envR_cons hZ hρ (σ₁.globs g)
    ((leseA A' σ' (Λ.map E.resE) ((Sum.inr g :: neu.orte).map E.ortE)).globs (E.glob g))
    (E.gtyp g) (hI.treu.2 g)
  obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := E.koerperSim_block_um hZ S' O' U' A' passes R' hc _ _ (ih_sim_block_rest)
    M₁ (σ₁.schreibGlob g Λ (eval σ₁ neu σ₁ (.cons (σ₁.globs g) ρ))) _ (.cons (σ₁.globs g) ρ) _
    (hI.schreibGlob E g Λ (Λ.map E.resE) _ _
      (E.vrel_um hZ (E.gtyp g) (hev neu _ _ ((E.envR_um hZ hc.symm _ _).mpr hrel)))) hrel
  refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
  · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2)]
    exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
  · simp only [exB, execBlockHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umΓ, eval_umTy, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
    exact E.ausRel_schrumpf hR

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
