/- C08 B1/B2: jointly satisfiable replay duties on a trace-faithful binding.
   Both calls have a nontrivial passing pre and distinct question keys.
   The original negative histories and integration blockers remain exhibits. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T10IntegrationBlocker
public import Grammatik.Logik.Ruf.FremdRuf.T9

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

namespace CallSiteBlocker

open CallSiteZeuge

theorem post_cover : PostDeckt unit := by
  intro a hsw σ0 ρ σ1 v hpost
  rfl

theorem binding_contract : ForeignVertrag unit traceOracle :=
  foreignVertrag_of_foreign foreign_trace

theorem trace_hardware [RootNativeFloat.Hardware] : HardwareAnnahmenHw traceOracle unit.Q :=
  ⟨traceOracle_gut, ⟨fun r => (nomatch r), fun g => (nomatch g)⟩,
    (fun a hsw => absurd rfl hsw), inferInstance⟩

/-- Two consecutive questions, each answered at its stored key. -/
def traceHistory : List (AxEintrag decl) :=
  actualHistory world ++ actualHistory answer

theorem traceHistory_passt : PasstA traceOracle traceHistory := by
  intro a σ ρ x hm
  rcases List.mem_append.mp hm with hm | hm
  · exact actualHistory_passt world a σ ρ x hm
  · exact actualHistory_passt answer a σ ρ x hm

theorem traceHistory_provenance : SchluesselHerkunft traceHistory := by
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · exact actualHistory_provenance world e hm
  · exact actualHistory_provenance answer e hm

theorem traceHistory_good : CallSitePflichtFremd unit.P.axVertrag traceHistory := by
  intro a σ ρ x hm hsw
  rcases List.mem_append.mp hm with hm | hm
  · exact actualHistory_good world a σ ρ x hm hsw
  · exact actualHistory_good answer a σ ρ x hm hsw

/-- Both recorded answers exercise the smaller binding interface and named
    post cover, without boundary-history assumptions in the transports. -/
theorem traceHistory_posts (a : decl.Ax) (σ : World decl)
    (ρ : Env decl (decl.aparams a)) (x : World decl × Int)
    (hm : (⟨a, σ, ρ, x⟩ : AxEintrag decl) ∈ traceHistory) :
    AxNach unit.P.axVertrag a σ ρ x.1 () ∧ unit.Q a x.1 () = true := by
  have hv : einpassenErg traceOracle.zeiger (decl.aerg a) x.2 = some () := rfl
  exact ⟨vertragANeu_sw_of_vertrag binding_contract traceHistory_good traceHistory_passt
      traceHistory_provenance hm rfl hv,
    qAmDatensatz_of_vertrag binding_contract traceHistory_good traceHistory_passt
      traceHistory_provenance post_cover hm rfl hv⟩

/-- An unconditional full-Q fixture inhabits the conditional class, and its
    two recorded answers retain membership through the new replay lemma. -/
theorem traceHistory_conditional :
    AxVertragOP (PreQ unit.P) unit.Q traceOracle ∧
      AxVertragOP (PreQ unit.P) unit.Q (orakelAus traceOracle traceHistory) := by
  have hQ : AxVertragO unit.Q traceOracle := fun _ _ _ _ _ => rfl
  have hrecord : VertragA traceOracle.zeiger unit.Q traceHistory :=
    fun _ _ _ _ _ _ _ _ _ _ => rfl
  exact ⟨axVertragOP_of_O _ hQ, orakelAus_vertragOP (axVertragOP_of_O _ hQ) hrecord⟩

/-- The first call of the existing program uses the good binding too. -/
theorem trace_first_step :
    RufSchrittG (program true) traceOracle 0 (start true) 0 (afterFirst true) := by
  refine RufSchrittG.blatt (start true) 0 false [] [] [] (call true) (tail true) .nil
    rfl rfl ?_ answer .nil [.fremd (.inl ())] rfl rfl ?_
  · intro L
    exact nomatch L
  · intro L
    exact nomatch L

/-- The second answer preserves its longer trace, rather than resetting it. -/
theorem trace_second_step :
    ∃ M : RufMaschineG decl,
      RufSchrittG (program true) traceOracle 0 (afterFirst true) 0 M := by
  refine ⟨_, RufSchrittG.blatt (afterFirst true) 0 false [] [] [] (call true)
    (.ret .empty (by rfl)) .nil rfl rfl ?_ key2 .nil [.fremd (.inl ())] rfl rfl ?_⟩
  · intro L
    exact nomatch L
  · intro L
    exact nomatch L

theorem traceHistory_sites : ∀ e ∈ traceHistory,
    CallSiteErreichbar (program true) traceOracle 0 (fun _ => False) (start true)
      ⟨e.1, e.2.1, e.2.2.1⟩ := by
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · have he : e = ⟨(), key1, rho true, (key1, 0)⟩ := by
      simp only [actualHistory, List.mem_singleton] at hm
      exact hm
    subst e
    exact ⟨start true, memory, 0, .start, fun c _ => traegerGleich_refl _ c, rfl⟩
  · have he : e = ⟨(), key2, rho true, (key2, 0)⟩ := by
      simp only [actualHistory, List.mem_singleton] at hm
      exact hm
    subst e
    refine ⟨afterFirst true, memory, 0,
      .schritt _ _ 0 .start (gx_aus_g trace_first_step),
      fun c _ => traegerGleich_refl _ c, ?_⟩
    simp only [RufMaschineG.foreignCallKey, afterFirst, rufUpdateG_self]
    rfl

/-- Independence of the named cover, on the existing false-Q exhibit. -/
theorem falseQ_not_postDeckt : ¬ PostDeckt falseQUnit := by
  intro h
  have hp := h () rfl world (rho true) world ()
    (software_post_does_not_imply_Q world).2.1
  change false = true at hp
  cases hp

/-- The hardware-only fixture discharges both new software duties vacuously. -/
def softwareFreeUnit : Einheit fdD where
  P := fdP
  S := SperrInv.leer fdD
  Q := fdQ
  starts := []
  sp0 := fdSp0

theorem software_free_duties_zeuge :
    PostDeckt softwareFreeUnit ∧ ForeignVertrag softwareFreeUnit fdO := by
  constructor
  · exact postDeckt_ohne _ fdD_ohne_software
  · exact foreignVertrag_ohne _ fdO fdD_ohne_software

/-- ZEUGE: every B1/B2 replay premise holds jointly for a GutO binding with
    two reachable calls, distinct keys, and a satisfiable and falsifiable pre.
    The native CPU contract remains an explicit hardware assumption. -/
theorem callSite_transport_zeuge [RootNativeFloat.Hardware] :
    GutO traceOracle ∧ HardwareAnnahmenHw traceOracle unit.Q ∧
    ForeignPflicht unit traceOracle [] ∧ ForeignVertrag unit traceOracle ∧ PostDeckt unit ∧
    PasstA traceOracle traceHistory ∧ SchluesselHerkunft traceHistory ∧
    CallSitePflichtFremd unit.P.axVertrag traceHistory ∧
    key1 ≠ key2 ∧ traceHistory.length = 2 ∧
    AxVor unit.P.axVertrag () world (rho true) ∧
    ¬ AxVor unit.P.axVertrag () world (rho false) ∧
    (∀ e ∈ traceHistory, CallSiteErreichbar (program true) traceOracle 0
      (fun _ => False) (start true) ⟨e.1, e.2.1, e.2.2.1⟩) ∧
    (∃ M : RufMaschineG decl,
      RufSchrittG (program true) traceOracle 0 (afterFirst true) 0 M) ∧
    ∀ (a : decl.Ax) (σ : World decl) (ρ : Env decl (decl.aparams a)) (x : World decl × Int),
      (⟨a, σ, ρ, x⟩ : AxEintrag decl) ∈ traceHistory →
      AxNach unit.P.axVertrag a σ ρ x.1 () ∧ unit.Q a x.1 () = true :=
  ⟨traceOracle_gut, trace_hardware, foreign_trace, binding_contract, post_cover,
    traceHistory_passt, traceHistory_provenance, traceHistory_good, keys_distinct, rfl,
    pre_true world, pre_false world, traceHistory_sites, trace_second_step, traceHistory_posts⟩

end CallSiteBlocker

end Gabbro.Grammatik
