module

public import Core.Ast.LowLevel.Proofs.EnvironmentUnit
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def EnvironmentUnitAussage : Prop :=
  environmentUnitForm.ParseAussage ∧ environmentUnitForm.ElaboriertAussage ∧
    environmentUnitForm.RealisiertAussage ∧ EnvironmentUnitAdmissionAussage ∧
    EnvironmentUnitTransferAussage ∧ environmentUnitForm.AnnahmeAussage ∧
    environmentUnitForm.IdealAussage ∧ environmentUnitForm.EinheitAussage ∧
    environmentUnitForm.ImplAussage ∧ environmentUnitForm.ErhaltungsAussage ∧
    EnvironmentUnitErfuellbarAussage

theorem environmentUnit : EnvironmentUnitAussage :=
  ⟨environmentUnit_parse, environmentUnit_elaboriert, environmentUnit_realisiert,
    environmentUnit_admission, environmentUnit_transfer, environmentUnit_annahme,
    environmentUnit_ideal, environmentUnit_einheit, environmentUnit_impl,
    environmentUnit_erhaltung, environmentUnit_erfuellbar⟩

end Gabbro.Core.Ast.Semantik
