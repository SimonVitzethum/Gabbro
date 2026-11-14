/- Concrete gate results for the structural candidates. Unsupported fragments
   remain refusals; source lock formulas restore the four lock fixtures. -/
module

public import Grammatik.Gen.Zeugen.Schluss.Teil2
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Decode
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.GateAudit

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Invarianten.Frag

/-- Read only the diagnostic; proof-valued successful results are not compared. -/
def contractCause (e : Einsatz) : Option Refusal :=
  match @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs
      e.lockSources {} (fun _ => none) with
  | .error cause => some cause
  | .ok _ => none

theorem refused_of_cause (e : Einsatz) (cause : Refusal)
    (reason : contractCause e = some cause) : e.gueltig = false := by
  have gate : @Vertraege.Pruefer.KontrakteGeprueftB e.D e.P e.S e.fs
      e.lockSources {} (fun _ => none) = false := by
    unfold Vertraege.Pruefer.KontrakteGeprueftB
    cases result : @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs
        e.lockSources {} (fun _ => none) with
    | error _ => rfl
    | ok _ => simp [contractCause, result] at reason
  cases verdict : e.gueltig with
  | false => rfl
  | true =>
    have accepted := ((einsatz_akzeptiert e).mp verdict).2.2
    rw [gate] at accepted
    exact Bool.noConfusion accepted

/-- The guard runs before VC generation, including the lock rule. -/
theorem m99_824_cause : contractCause M99_824.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

theorem m99_825_cause : contractCause M99_825.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

theorem m49_50_cause : contractCause M49_50.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

/-- The indirect call still has no contract-WP rule. -/
theorem m47_549_cause : contractCause M47_549.e = some
    (.unsupported "contract statement is outside the checked scalar/control fragment") := by decide

theorem m99_824_refused : M99_824.e.gueltig = false :=
  refused_of_cause _ _ m99_824_cause

theorem refused_of_cause_zeuge : contractCause M99_824.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") ∧
    M99_824.e.gueltig = false := ⟨m99_824_cause, m99_824_refused⟩

theorem m99_825_refused : M99_825.e.gueltig = false :=
  refused_of_cause _ _ m99_825_cause

theorem m49_50_refused : M49_50.e.gueltig = false :=
  refused_of_cause _ _ m49_50_cause

theorem m47_549_refused : M47_549.e.gueltig = false :=
  refused_of_cause _ _ m47_549_cause

/-- Omitting the actual source syntax is still refused. No default-true
    fallback has been introduced for an opaque semantic lock predicate. -/
theorem m16_missing_sources_refused :
    (@Vertraege.Pruefer.checkContracts M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs (fun _ => none) {} (fun _ => none)).toOption.isSome = false := by decide

/-- Full acceptance and the generic model duties hold together on the same
    unchanged bodies and contracts, using the ordinary source input. -/
theorem m16_source_checked_zeuge : M16_13.e.gueltig = true ∧
    ∀ f, Vertraege.Pruefer.ContractDuties M16_13.e.P M16_13.e.S f :=
  ⟨M16_13.e_gueltig, Vertraege.Pruefer.KontrakteGeprueftB_sound
    M16_13.e.hvoll (((einsatz_akzeptiert _).mp M16_13.e_gueltig).2.2)⟩

/-- A callee's logical requires is not an executed atomic read. The exact
    replay certificate adds this case while retaining the conservative gate. -/
theorem m169_atomic_replay_zeuge :
    Invarianten.Pruefer.atomicFreeB M169_350.e.P M169_350.fv = false ∧
    (Invarianten.Pruefer.atomicReplay? M169_350.e.P M169_350.fv).isSome = true := by decide

/-- The four former fragment refusals are accepted by the complete checker. -/
theorem lock_fixtures_checked_zeuge :
    M16_13.e.gueltig = true ∧ M169_350.e.gueltig = true ∧
    M103_803.e.gueltig = true ∧ M103_131.e.gueltig = true :=
  ⟨M16_13.e_gueltig, M169_350.e_gueltig, M103_803.e_gueltig, M103_131.e_gueltig⟩

end Gabbro.Grammatik.Gen.Zeugen.GateAudit
