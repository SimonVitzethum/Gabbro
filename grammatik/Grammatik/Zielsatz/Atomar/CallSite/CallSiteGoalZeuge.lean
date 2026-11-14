/- C08 R3b: THE JOINT WITNESS OF THE HEADLINE `GabbroZiel` (call-site duties) ON A UNIT WITH A
   SOFTWARE FOREIGN ITEM.

   `callSite_goal_zeuge`: on the unit `wE` of `CallSiteGoalFixture` (one function calling the
   software item `g(x : 0..1) -> 0..1`, `requires x != 0`, `ensures result == 1`, with
   `ensures result == 1` on the function) and the binding `echo` (answers its argument), ALL
   premises of `GabbroZiel` hold at once:
   (a) `akzeptiertX_pruefer` accepts the unit (`checker`);
   (b) `NutzerPflichtA` (`user`: the body's post follows only from `g`'s summary, granted where
       `g`'s pre held), `CallSitePflicht` (`call_sites`: every reached call meets the pre, over
       every run), `PostDeckt` (`post_cover`), `ForeignVertrag wE echo` (`binding`);
   (c) `HardwareAnnahmenHw echo wE.Q` (`hardware`: frame and register locality only, `g` being
       software);
   (d) `Laufzeit` of the runtime's start (`laufzeit_voll`).
   NON-DEGENERATE: `g` is software, its pre holds at `1` and fails at `0`, `echo` breaks the
   full summary (so `GabbroZielVoll` does not apply to it), and the body duty fails without
   `g`'s summary (`summary_used`). THE CONCLUSION, EXHIBITED: one GX step of thread 0 from the
   runtime's start runs the software call (the start's question has a true pre, `start_call`);
   the machine it reaches has thread 0 at its return (so the `StartEndeG` leg speaks about the
   answer of `echo`), and `gabbro_ziel` gives every leg of `ZielFX` there. -/
module

public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteGoalSites
public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteGoalUser
public import Grammatik.Zielsatz.Atomar.BeweisAtomar

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteGoal

open Gabbro.Grammatik Speichermodell

/-- The runtime's start memory and thread assignment. -/
abbrev sp0R : Speicher wD.mitRuhe := speicherR wE.sp0
abbrev initR : Faden → Σ f : wD.mitRuhe.Fn, Env wD.mitRuhe (wD.mitRuhe.params f) :=
  initRuhe wE.starts

/-- The thread machine of the runtime's start, every slot live. -/
abbrev K0 : FadenMaschine wD.mitRuhe := FadenStart wE.P.mitRuhe sp0R initR (fun _ => true)

/-- **The software call fires**: thread 0's first step from the start binds `echo`'s answer and
    leaves thread 0 at its return. -/
theorem call_step : ∃ M1 : RufMaschineG wD.mitRuhe,
    RufSchrittG wE.P.mitRuhe echo.mitRuhe 0 K0.m 0 M1 ∧ (M1.faeden 0).stapel = [] ∧
    ∃ l Γ Λ ρ e hp, (M1.faeden 0).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hp)⟩ :=
  ⟨_, RufSchrittG.endeBindAxiom K0.m 0 _ _ _ _ _ _ _ _ _ _ _ _ _ rfl _ rfl _ _ rfl
      [.fremd (.inl ())] rfl (fun L => nomatch L),
    rfl, _, _, _, _, _, _, rfl⟩

/-- **THE JOINT WITNESS** of the headline `GabbroZiel` with a software foreign item. -/
theorem callSite_goal_zeuge [RootNativeFloat.Hardware] :
    -- (a) the checker
    akzeptiertX_pruefer.akzeptiert wE [()] [] [] = true ∧
    -- (b) the user: bodies with the rely, call-site pres, post cover, the binding's proof
    NutzerPflichtA wE ∧ CallSitePflicht wE ∧ PostDeckt wE ∧ ForeignVertrag wE echo ∧
    -- (c) the named hardware
    HardwareAnnahmenHw echo wE.Q ∧
    -- (d) the runtime
    Laufzeit wE sp0R initR ∧
    -- non-degenerate: a software item with a pre that bites, a binding outside the full summary,
    -- a body duty that needs the summary
    wD.axHerkunft () = some AxOrigin.software ∧
    AxVor wE.P.axVertrag () world (rhoW true) ∧ ¬ AxVor wE.P.axVertrag () world (rhoW false) ∧
    ¬ AxVertragO wE.Q echo ∧
    (∀ T, ¬ KoerperGutSA wE.P 0 (fun _ _ _ => true) wE.S T ()) ∧
    -- the start asks the software item with a true pre
    (∃ k, K0.m.foreignCallKey 0 = some k ∧ AxVor wE.P.mitRuhe.axVertrag k.1 k.2.1 k.2.2) ∧
    -- the conclusion at the machine after the software call, thread 0 at its return
    ∃ K1 : FadenMaschine wD.mitRuhe,
      FadenErreichbarX wE.P.mitRuhe echo.mitRuhe 0 (GeteiltV (D := wD) wE.P wE.ws) K0 K1 ∧
      RufSchrittG wE.P.mitRuhe echo.mitRuhe 0 K0.m 0 K1.m ∧
      (K1.m.faeden 0).stapel = [] ∧
      (∃ l Γ Λ ρ e hp, (K1.m.faeden 0).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hp)⟩) ∧
      ZielFX wE.P.mitRuhe wE.S.mitRuhe echo.mitRuhe 0 (GeteiltV (D := wD) wE.P wE.ws)
        (RufStartG wE.P.mitRuhe sp0R initR) (wE.arenen.map (·.mitRuhe)) K1 := by
  obtain ⟨M1, hs, hst, hret⟩ := call_step
  have hK1 : FadenErreichbarX wE.P.mitRuhe echo.mitRuhe 0 (GeteiltV (D := wD) wE.P wE.ws) K0
      ⟨M1, K0.lebt, K0.wartet, K0.rang, K0.uhr⟩ :=
    .schritt _ _ .start (.lauf K0 0 M1 rfl rfl (gx_aus_g hs))
  have hZ := gabbro_ziel akzeptiertX_pruefer wD wE
    ⟨[()], fs_voll⟩ ⟨[], fun L => nomatch L⟩
    ⟨[], fun c => match c with | .inl t => nomatch t | .inr g => nomatch g⟩
    checker user call_sites post_cover echo binding hardware 0 sp0R initR (laufzeit_voll wE)
    (fun _ => true) _ hK1
  exact ⟨checker, user, call_sites, post_cover, binding, hardware, laufzeit_voll wE, rfl,
    pre_true world, pre_false world, echo_not_summary, summary_used, start_call,
    _, hK1, hs, hst, hret, hZ⟩

end Gabbro.Grammatik.Zielsatz.CallSiteGoal

#print axioms Gabbro.Grammatik.Zielsatz.CallSiteGoal.callSite_goal_zeuge
