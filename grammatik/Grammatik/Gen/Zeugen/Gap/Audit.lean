/- Concrete gate results for the structural candidates. Unsupported fragments
   remain refusals; source lock formulas restore the four lock fixtures. -/
module

public import Grammatik.Gen.Zeugen.Gap.M99_824
public import Grammatik.Gen.Zeugen.Gap.M99_825
public import Grammatik.Logik.Vertraege.Pruefer.Witness.AtomicReadAudit
public import Grammatik.Gen.Zeugen.Gap.M47_549
public import Grammatik.Gen.Zeugen.M.M169_350
public import Grammatik.Gen.Zeugen.M.M103_803
public import Grammatik.Gen.Zeugen.M.M103_131
public import Grammatik.Gen.Zeugen.M.M16_13
import all Grammatik.Logik.Invarianten.Frag.Observation
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
open Gabbro.Grammatik.Gen.Zeugen.Gap
open Invarianten.Frag

/-- Read only the diagnostic; proof-valued successful results are not compared. -/
def contractCause (e : Einsatz) : Option Refusal :=
  match @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs
      e.lockSources {} (fun _ => none) none with
  | .error cause => some cause
  | .ok _ => none

theorem refused_of_cause (e : Einsatz) (cause : Refusal)
    (reason : contractCause e = some cause) : e.gueltig = false := by
  have gate : @Vertraege.Pruefer.KontrakteGeprueftB e.D e.P e.S e.fs
      e.lockSources {} (fun _ => none) none = false := by
    unfold Vertraege.Pruefer.KontrakteGeprueftB
    cases result : @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs
        e.lockSources {} (fun _ => none) none with
    | error _ => rfl
    | ok _ => simp [contractCause, result] at reason
  cases verdict : e.gueltig with
  | false => rfl
  | true =>
    have accepted := ((einsatz_akzeptiert e).mp verdict).2.2
    rw [gate] at accepted
    exact Bool.noConfusion accepted

/-- Literal-true totality covers these typed register/atomic observations. -/
theorem m99_824_cause : contractCause M99_824.e = none := by decide +kernel

theorem m99_825_cause : contractCause M99_825.e = none := by decide +kernel

/-- The typed atomic read has literal true contracts and no owed invariant.
    Its totality certificate covers every value the atomic environment returns. -/
theorem m49_50_contract_checked : contractCause M49_50.e = none := by decide +kernel

/-- Without the decided interface refinement the indirect call is refused. -/
theorem m47_549_cause : contractCause M47_549.e = some
    (.unsupported "contract indirect call needs checked interface refinement") := by decide +kernel

theorem m99_824_checked : M99_824.e.gueltig = true := by decide +kernel

theorem m99_825_checked : M99_825.e.gueltig = true := by decide +kernel

/-- Literal-true lock predicates have no restoration duty. Both independent
    gates accept the unchanged typed atomic-read fixture. -/
theorem m49_50_checked : M49_50.e.gueltig = true :=
  Vertraege.Pruefer.AtomicReadAudit.accepted_zeuge

theorem m47_549_refused : M47_549.e.gueltig = false :=
  refused_of_cause _ _ m47_549_cause

/-- Omitting the actual source syntax is still refused. No default-true
    fallback has been introduced for an opaque semantic lock predicate. -/
theorem m16_missing_sources_refused :
    (@Vertraege.Pruefer.checkContracts M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs (fun _ => none) {} (fun _ => none) none).toOption.isSome = false := by decide +kernel

end Gabbro.Grammatik.Gen.Zeugen.GateAudit
