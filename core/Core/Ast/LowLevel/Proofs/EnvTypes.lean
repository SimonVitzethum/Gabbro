module

public import Core.Ast.LowLevel.Obligations
public import Core.Ast.LowLevel.Proofs.Syntax
public import Core.Ast.LowLevel.Proofs.Elaboration
public import Core.Ast.LowLevel.Proofs.Execution
public import Core.Ast.LowLevel.Proofs.Preservation
public import Core.Ast.LowLevel.Proofs.Meaning
public import Core.Ast.LowLevel.Proofs.Satisfiability

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

/-- The full low-level promise for an occurrence: every obligation of the form
    and its form-specific meaning hold jointly. The component proofs are shared
    across all forms; only the printer and the satisfiability witnesses are
    form-specific. -/

theorem addressType_aussage : AddressTypeAussage := by
  unfold AddressTypeAussage MeaningAussage
  constructor
  · exact ⟨parseAussage .addressType, inversionAussage .addressType,
      eindeutigAussage .addressType, druckAussage_addressType,
      elaboriert_form .addressType, realisiert_form .addressType,
      annahme_form .addressType, execution_ideal .addressType,
      execution_einheit .addressType, execution_impl .addressType,
      execution_fortschritt .addressType, erhaltung .addressType,
      regelSicher .addressType, regelAntwortSicher .addressType,
      aussenLokal .addressType, kosten .addressType,
      addressType_erfuellbar⟩
  · exact addressTypeMeaning

theorem regionAddress_aussage : RegionAddressAussage := by
  unfold RegionAddressAussage MeaningAussage
  constructor
  · exact ⟨parseAussage .regionAddress, inversionAussage .regionAddress,
      eindeutigAussage .regionAddress, druckAussage_regionAddress,
      elaboriert_form .regionAddress, realisiert_form .regionAddress,
      annahme_form .regionAddress, execution_ideal .regionAddress,
      execution_einheit .regionAddress, execution_impl .regionAddress,
      execution_fortschritt .regionAddress, erhaltung .regionAddress,
      regelSicher .regionAddress, regelAntwortSicher .regionAddress,
      aussenLokal .regionAddress, kosten .regionAddress,
      regionAddress_erfuellbar⟩
  · exact regionAddressMeaning

theorem environment_aussage : EnvironmentAussage := by
  unfold EnvironmentAussage MeaningAussage
  constructor
  · exact ⟨parseAussage .environment, inversionAussage .environment,
      eindeutigAussage .environment, druckAussage_environment,
      elaboriert_form .environment, realisiert_form .environment,
      annahme_form .environment, execution_ideal .environment,
      execution_einheit .environment, execution_impl .environment,
      execution_fortschritt .environment, erhaltung .environment,
      regelSicher .environment, regelAntwortSicher .environment,
      aussenLokal .environment, kosten .environment,
      environment_erfuellbar⟩
  · exact environmentMeaning

end Gabbro.Core.Ast.LowLevel
