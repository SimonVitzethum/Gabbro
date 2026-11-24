module

public import Core.Ast.LowLevel.Proofs.ViewParts
public import Core.Ast.LowLevel.Proofs.ViewRules

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter

theorem view_aussage : ViewAussage := by
  refine ⟨?_, viewMeaningAussage⟩
  exact ⟨viewParseAussage, viewInversionAussage, viewEindeutigAussage, viewDruckAussage,
    viewElaboriertAussage, viewRealisiertAussage, viewAnnahmeAussage,
    viewIdealAussage, viewEinheitAussage, viewImplAussage, viewFortschrittAussage,
    viewErhaltungAussage, viewRegelSicherAussage, viewRegelAntwortSicherAussage,
    viewAussenLokalAussage, viewKostenAussage, viewErfuellbarAussage⟩

end Gabbro.Core.Ast.LowLevel
