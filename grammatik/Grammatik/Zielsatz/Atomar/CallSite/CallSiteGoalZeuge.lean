/- C08 call-site regression: semantic software duties can hold jointly while
   the concrete checker refuses an unsupported foreign-call body. This is
   not an accepted witness of GabbroZiel. CallSiteAcceptedFixture supplies
   the separate accepted immediate-return witness. -/
module

public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteGoalSites
public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteGoalUser
public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteAcceptedFixture

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteGoal

open Gabbro.Grammatik Speichermodell

/-- The runtime's start memory and thread assignment. -/
abbrev sp0R : Speicher wD.mitRuhe := speicherR wE.sp0
abbrev initR : Faden → Σ f : wD.mitRuhe.Fn, Env wD.mitRuhe (wD.mitRuhe.params f) :=
  initRuhe wE.starts

/-- The thread machine of the runtime's start, every slot live. -/
abbrev K0 : FadenMaschine wD.mitRuhe := FadenStart wE.P.mitRuhe sp0R initR (fun _ => true)

/-- The semantic software call still fires, independently of checker acceptance. -/
theorem call_step : ∃ M1 : RufMaschineG wD.mitRuhe,
    RufSchrittG wE.P.mitRuhe echo.mitRuhe 0 K0.m 0 M1 ∧ (M1.faeden 0).stapel = [] ∧
    ∃ l Γ Λ ρ e hp, (M1.faeden 0).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hp)⟩ :=
  ⟨_, RufSchrittG.endeBindAxiom K0.m 0 _ _ _ _ _ _ _ _ _ _ _ _ _ rfl _ rfl _ _ rfl
      [.fremd (.inl ())] rfl (fun L => nomatch L),
    rfl, _, _, _, _, _, _, rfl⟩

/-- The refused fixture retains its non-degenerate semantic witnesses: a
    reachable software call, a pre that can fail, a binding outside the full
    summary, and a body that needs that summary. None implies acceptance. -/
theorem callSite_refused_zeuge [RootNativeFloat.Hardware] :
    akzeptiertX_pruefer.akzeptiert wE [()] [] [] = false ∧
    NutzerPflichtA wE ∧ CallSitePflicht wE ∧ PostDeckt wE ∧ ForeignVertrag wE echo ∧
    HardwareAnnahmenHw echo wE.Q ∧ Laufzeit wE sp0R initR ∧
    wD.axHerkunft () = some AxOrigin.software ∧
    AxVor wE.P.axVertrag () world (rhoW true) ∧ ¬ AxVor wE.P.axVertrag () world (rhoW false) ∧
    ¬ AxVertragO wE.Q echo ∧
    (∀ T, ¬ KoerperGutSA wE.P 0 (fun _ _ _ => true) wE.S T ()) ∧
    (∃ k, K0.m.foreignCallKey 0 = some k ∧ AxVor wE.P.mitRuhe.axVertrag k.1 k.2.1 k.2.2) ∧
    ∃ K1 : FadenMaschine wD.mitRuhe,
      FadenErreichbarX wE.P.mitRuhe echo.mitRuhe 0 (GeteiltV (D := wD) wE.P wE.ws) K0 K1 ∧
      RufSchrittG wE.P.mitRuhe echo.mitRuhe 0 K0.m 0 K1.m ∧
      (K1.m.faeden 0).stapel = [] ∧
      (∃ l Γ Λ ρ e hp, (K1.m.faeden 0).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hp)⟩) := by
  obtain ⟨M1, hs, hst, hret⟩ := call_step
  have hK1 : FadenErreichbarX wE.P.mitRuhe echo.mitRuhe 0 (GeteiltV (D := wD) wE.P wE.ws) K0
      ⟨M1, K0.lebt, K0.wartet, K0.rang, K0.uhr⟩ :=
    .schritt _ _ .start (.lauf K0 0 M1 rfl rfl (gx_aus_g hs))
  exact ⟨checker, user, call_sites, post_cover, binding, hardware, laufzeit_voll wE, rfl,
    pre_true world, pre_false world, echo_not_summary, summary_used, start_call,
    _, hK1, hs, hst, hret⟩

end Gabbro.Grammatik.Zielsatz.CallSiteGoal

#print axioms Gabbro.Grammatik.Zielsatz.CallSiteGoal.callSite_refused_zeuge
