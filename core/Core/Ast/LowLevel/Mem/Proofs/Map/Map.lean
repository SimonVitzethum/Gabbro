module

public import Core.Ast.LowLevel.Mem.Proofs.Map.MapAux
public import Core.Ast.LowLevel.Mem.Proofs.Map.MapMeaning
public import Core.Ast.LowLevel.Mem.Proofs.Map.MapSat
public import Core.Ast.LowLevel.Mem.Proofs.SplitAt

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

theorem mapObligations : memObligationsKern .mapSpace := by
  repeat' constructor
  · exact mapMemParse .mapSpace
  · exact mapMemInversion .mapSpace
  · exact mapEindeutig
  · exact mapMemDruck .mapSpace
  · exact memElaboriert .mapSpace
  · exact memRealisiert .mapSpace
  · exact memAnnahme .mapSpace
  · exact memIdeal .mapSpace
  · exact memEinheit .mapSpace
  · exact memImpl .mapSpace
  · exact memFortschritt .mapSpace
  · exact memErhaltung .mapSpace
  · exact memRegelSicher .mapSpace
  · exact memRegelAntwortSicher .mapSpace
  · exact memAussenLokal .mapSpace
  · exact memKosten .mapSpace
  · exact memSchranken
  · exact memEtiketten
  · exact memFluss

theorem map_aussage : MapAussage := by
  exact ⟨mapObligations, mapMeaning, map_joint⟩

end Gabbro.Core.Ast.LowLevel
