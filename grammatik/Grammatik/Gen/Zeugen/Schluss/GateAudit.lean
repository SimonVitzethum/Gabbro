/- Concrete refusals of the old structural M candidates. These are fragment
   findings, not counterexamples to their declared postconditions. -/
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
      (fun _ => none) {} (fun _ => none) with
  | .error cause => some cause
  | .ok _ => none

theorem refused_of_cause (e : Einsatz) (cause : Refusal)
    (reason : contractCause e = some cause) : e.gueltig = false := by
  have gate : @Vertraege.Pruefer.KontrakteGeprueftB e.D e.P e.S e.fs
      (fun _ => none) {} (fun _ => none) = false := by
    unfold Vertraege.Pruefer.KontrakteGeprueftB
    cases result : @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs
        (fun _ => none) {} (fun _ => none) with
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

/-- The caller's quantified requires is translated. Its indirect call has no
    contract-WP rule, although the typed model has an execution rule. -/
theorem m47_549_cause : contractCause M47_549.e = some
    (.unsupported "contract statement is outside the checked scalar/control fragment") := by decide

theorem m16_13_cause : contractCause M16_13.e = some
    (.unsupported "semantic lock invariant has no reified source formula; user duty") := by decide

theorem m169_350_cause : contractCause M169_350.e = some
    (.unsupported "semantic lock invariant has no reified source formula; user duty") := by decide

theorem m103_803_cause : contractCause M103_803.e = some
    (.unsupported "semantic lock invariant has no reified source formula; user duty") := by decide

theorem m103_131_cause : contractCause M103_131.e = some
    (.unsupported "semantic lock invariant has no reified source formula; user duty") := by decide

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

theorem m16_13_refused : M16_13.e.gueltig = false :=
  refused_of_cause _ _ m16_13_cause

theorem m169_350_refused : M169_350.e.gueltig = false :=
  refused_of_cause _ _ m169_350_cause

theorem m103_803_refused : M103_803.e.gueltig = false :=
  refused_of_cause _ _ m103_803_cause

theorem m103_131_refused : M103_131.e.gueltig = false :=
  refused_of_cause _ _ m103_131_cause

/-- A source formula for the actual maximal lock family's true predicate.
    This changes checker input only in the following diagnostic witness. -/
def trueLockSources (z : Spez) : Invarianten.Pruefer.LockSources z.sperreMax :=
  fun _ => some
    { resources := []
      expression := .tru
      correct := fun _ => rfl }

/-- The same M16 bodies and contracts pass once their existing true lock
    predicates are reified. No gate or semantic obligation is weakened. -/
theorem m16_with_sources_checked :
    @Vertraege.Pruefer.KontrakteGeprueftB M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs (trueLockSources M16_13.z) {} (fun _ => none) = true := by decide

/-- Joint evidence that the default-source refusal is not a false contract. -/
theorem m16_gate_finding_zeuge : M16_13.e.gueltig = false ∧
    ∀ f, Vertraege.Pruefer.ContractDuties M16_13.e.P M16_13.e.S f :=
  ⟨m16_13_refused, Vertraege.Pruefer.KontrakteGeprueftB_sound
    M16_13.e.hvoll m16_with_sources_checked⟩

private theorem verdict_iff_reset (e : Einsatz) (refused : e.gueltig = false) :
    e.gueltig = true ↔ e = Reset.Good.e := by
  constructor
  · intro accepted
    rw [refused] at accepted
    exact Bool.noConfusion accepted
  · intro same
    rw [same, Reset.Good.e_gueltig] at refused
    exact Bool.noConfusion refused

/-- Exact classification of every old M candidate, including the accepted
    reset fixture. No unsupported fixture is called a false ensures. -/
theorem old_m_verdicts : ∀ e ∈ structuralWitnesses, e.gueltig = true ↔ e = Reset.Good.e := by
  intro e member
  simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact verdict_iff_reset _ m99_824_refused
  · exact verdict_iff_reset _ m47_549_refused
  · exact verdict_iff_reset _ m169_350_refused
  · exact verdict_iff_reset _ m16_13_refused
  · exact verdict_iff_reset _ m49_50_refused
  · exact verdict_iff_reset _ m103_803_refused
  · exact verdict_iff_reset _ m103_131_refused
  · exact verdict_iff_reset _ m99_825_refused
  · exact ⟨fun _ => rfl, fun _ => Reset.Good.e_gueltig⟩

end Gabbro.Grammatik.Gen.Zeugen.GateAudit
