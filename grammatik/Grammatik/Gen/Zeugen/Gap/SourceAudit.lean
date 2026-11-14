/- Reified lock sources close only the obligations they actually check. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Decode
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Gap.SourceAudit

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Invarianten.Frag

/-- The invariant gate is a separate obligation from the contract gate. -/
theorem m16_invariants_with_sources :
    @Invarianten.Pruefer.programInvariantsB M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs (GateAudit.trueLockSources M16_13.z) {} M16_13.e.ls = true := by decide

/-- Removing the first missing-source refusal may expose a second fragment gap. -/
theorem m169_with_sources_cause :
    GateAudit.contractCause M169_350.e (GateAudit.trueLockSources M169_350.z) = some
      (.unsupported "contract body reads atomic memory outside the checked VC fragment") := by decide

theorem m103_803_with_sources_cause :
    GateAudit.contractCause M103_803.e (GateAudit.trueLockSources M103_803.z) = some
      (.unsupported "contract statement is outside the checked scalar/control fragment") := by decide

theorem m103_131_with_sources_cause :
    GateAudit.contractCause M103_131.e (GateAudit.trueLockSources M103_131.z) = some
      (.unsupported "contract statement is outside the checked scalar/control fragment") := by decide

theorem m16_both_gates_zeuge : M16_13.e.gueltig = true ∧
    @Invarianten.Pruefer.programInvariantsB M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs (GateAudit.trueLockSources M16_13.z) {} M16_13.e.ls = true ∧
    @Vertraege.Pruefer.KontrakteGeprueftB M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs (GateAudit.trueLockSources M16_13.z) {} (fun _ => none) = true :=
  ⟨M16_13.e_gueltig, m16_invariants_with_sources, GateAudit.m16_with_sources_checked⟩

end Gabbro.Grammatik.Gen.Zeugen.Gap.SourceAudit
