/- The restored fixtures satisfy both gates under their actual source predicates. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Gap.SourceAudit

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- A contract-gate result alone never substitutes for the invariant gate. -/
theorem m16_both_gates_zeuge : M16_13.e.gueltig = true ∧
    @Invarianten.Pruefer.programInvariantsB M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs M16_13.e.lockSources {} M16_13.e.ls = true ∧
    @Vertraege.Pruefer.KontrakteGeprueftB M16_13.e.D M16_13.e.P M16_13.e.S
      M16_13.e.fs M16_13.e.lockSources {} (fun _ => none) = true :=
  ⟨M16_13.e_gueltig, ((einsatz_akzeptiert _).mp M16_13.e_gueltig).2⟩

/-- All four unchanged lock programs now have full checker certificates. -/
theorem restored_zeuge : M16_13.e.gueltig = true ∧ M169_350.e.gueltig = true ∧
    M103_803.e.gueltig = true ∧ M103_131.e.gueltig = true :=
  GateAudit.lock_fixtures_checked_zeuge

end Gabbro.Grammatik.Gen.Zeugen.Gap.SourceAudit
