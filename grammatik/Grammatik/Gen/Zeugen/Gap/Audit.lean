/- Concrete diagnostics under the source predicates actually supplied by each fixture. -/
module

public import Grammatik.Gen.Zeugen.Gap.M99_824
public import Grammatik.Gen.Zeugen.Gap.M99_825
public import Grammatik.Gen.Zeugen.Gap.M49_50
public import Grammatik.Gen.Zeugen.Gap.M47_549
public import Grammatik.Gen.Zeugen.Gap.M169_350
public import Grammatik.Gen.Zeugen.Gap.M103_803
public import Grammatik.Gen.Zeugen.Gap.M103_131
public import Grammatik.Gen.Zeugen.M.M16_13
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

/-- Read only the diagnostic; successful proof-valued results are not compared. -/
def contractCause (e : Einsatz)
    (sources : Invarianten.Pruefer.LockSources e.S := e.lockSources) : Option Refusal :=
  match @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs sources {} (fun _ => none) with
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

theorem m99_824_cause : contractCause M99_824.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

theorem m99_824_refused : M99_824.e.gueltig = false :=
  refused_of_cause _ _ m99_824_cause

theorem m99_825_cause : contractCause M99_825.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

theorem m99_825_refused : M99_825.e.gueltig = false :=
  refused_of_cause _ _ m99_825_cause

theorem m49_50_cause : contractCause M49_50.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

theorem m49_50_refused : M49_50.e.gueltig = false :=
  refused_of_cause _ _ m49_50_cause

theorem m47_549_cause : contractCause M47_549.e = some
    (.unsupported "contract statement is outside the checked scalar/control fragment") := by decide

theorem m47_549_refused : M47_549.e.gueltig = false :=
  refused_of_cause _ _ m47_549_cause

theorem m169_350_cause : contractCause M169_350.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

theorem m169_350_refused : M169_350.e.gueltig = false :=
  refused_of_cause _ _ m169_350_cause

theorem m103_803_cause : contractCause M103_803.e = some
    (.unsupported "contract statement is outside the checked scalar/control fragment") := by decide

theorem m103_803_refused : M103_803.e.gueltig = false :=
  refused_of_cause _ _ m103_803_cause

theorem m103_131_cause : contractCause M103_131.e = some
    (.unsupported "contract statement is outside the checked scalar/control fragment") := by decide

theorem m103_131_refused : M103_131.e.gueltig = false :=
  refused_of_cause _ _ m103_131_cause

/-- The now-preserved source is the actual definitionally true lock predicate. -/
def trueLockSources (z : Spez) : Invarianten.Pruefer.LockSources z.sperreMax := z.lockSources

/-- Even a true semantic predicate is refused when its source input is removed. -/
theorem m16_without_sources_cause : contractCause M16_13.e (fun _ => none) = some
    (.unsupported "semantic lock invariant has no reified source formula; user duty") := by decide

theorem m16_with_sources_checked :
    @Vertraege.Pruefer.KontrakteGeprueftB M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs M16_13.e.lockSources {} (fun _ => none) = true := by decide

/-- Full acceptance and its generic contract duties hold jointly. -/
theorem m16_source_accepted_zeuge : M16_13.e.gueltig = true ∧
    ∀ f, Vertraege.Pruefer.ContractDuties M16_13.e.P M16_13.e.S f :=
  ⟨M16_13.e_gueltig, Vertraege.Pruefer.KontrakteGeprueftB_sound
    M16_13.e.hvoll m16_with_sources_checked⟩

theorem refused_of_cause_zeuge : contractCause M99_824.e = some
    (.unsupported "contract body reads atomic memory outside the checked VC fragment") ∧
    M99_824.e.gueltig = false := ⟨m99_824_cause, m99_824_refused⟩

end Gabbro.Grammatik.Gen.Zeugen.GateAudit
