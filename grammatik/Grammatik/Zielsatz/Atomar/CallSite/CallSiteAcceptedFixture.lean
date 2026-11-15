/- An accepted C08 goal witness with a declared software item. Its function
   contract is true and its sole start immediately returns. The call-site
   duty is empty; this does not claim acceptance of foreign-call bodies. -/
module

public import Grammatik.Zielsatz.Atomar.CallSite.CallSiteReplayBlocker
public import Grammatik.Zielsatz.Atomar.BeweisAtomar

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteAccepted

open Gabbro.Grammatik Speichermodell
open CallSiteZeuge (decl)
open CallSiteBlocker (traceOracle)
open CallSiteReplayBlocker (goodUnit good_checker good_user good_call_sites)

abbrev sp0R : Speicher decl.mitRuhe := speicherR goodUnit.sp0
abbrev initR : Faden → Σ f : decl.mitRuhe.Fn, Env decl.mitRuhe (decl.mitRuhe.params f) :=
  initRuhe goodUnit.starts
abbrev K0 : FadenMaschine decl.mitRuhe :=
  FadenStart goodUnit.P.mitRuhe sp0R initR (fun _ => true)

theorem fs_voll : ∀ f : decl.Fn, f ∈ [()] := fun f => by
  cases f
  exact List.mem_cons_self

/-- Joint witness of checker acceptance, all software and hardware duties,
    an actual declared start and the complete ZielFX conclusion on every
    reachable machine. The unused false software summary is not assumed. -/
theorem callSite_goal_zeuge [RootNativeFloat.Hardware] :
    akzeptiertX_pruefer.akzeptiert goodUnit [()] [] [] = true ∧
    NutzerPflichtA goodUnit ∧ CallSitePflicht goodUnit ∧ PostDeckt goodUnit ∧
    ForeignVertrag goodUnit traceOracle ∧ HardwareAnnahmenHw traceOracle goodUnit.Q ∧
    Laufzeit goodUnit sp0R initR ∧
    decl.axHerkunft () = some AxOrigin.software ∧
    ¬ AxVertragO goodUnit.Q traceOracle ∧
    ∀ passes K,
      FadenErreichbarX goodUnit.P.mitRuhe traceOracle.mitRuhe passes
        (GeteiltV (D := decl) goodUnit.P goodUnit.ws) K0 K →
      ZielFX goodUnit.P.mitRuhe goodUnit.S.mitRuhe traceOracle.mitRuhe passes
        (GeteiltV (D := decl) goodUnit.P goodUnit.ws)
        (RufStartG goodUnit.P.mitRuhe sp0R initR) (goodUnit.arenen.map (·.mitRuhe)) K := by
  have cover : PostDeckt goodUnit := CallSiteReplayBlocker.post_cover
  have binding : ForeignVertrag goodUnit traceOracle := CallSiteReplayBlocker.binding
  have hardware : HardwareAnnahmenHw traceOracle goodUnit.Q := CallSiteReplayBlocker.hardware
  refine ⟨good_checker, good_user, good_call_sites, cover, binding, hardware,
    laufzeit_voll goodUnit, rfl, CallSiteReplayBlocker.no_global_summary traceOracle, ?_⟩
  intro passes K reached
  exact gabbro_ziel akzeptiertX_pruefer decl goodUnit
    ⟨[()], fs_voll⟩ ⟨[], fun L => nomatch L⟩
    ⟨[], fun c => match c with | .inl t => nomatch t | .inr g => nomatch g⟩
    good_checker good_user good_call_sites cover traceOracle binding hardware
    passes sp0R initR (laufzeit_voll goodUnit) (fun _ => true) K reached

end Gabbro.Grammatik.Zielsatz.CallSiteAccepted

#print axioms Gabbro.Grammatik.Zielsatz.CallSiteAccepted.callSite_goal_zeuge
