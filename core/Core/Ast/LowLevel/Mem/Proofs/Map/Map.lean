module

public import Core.Ast.LowLevel.Mem.Proofs.Map.MapAux
public import Core.Ast.LowLevel.Mem.Proofs.Map.MapMeaning
public import Core.Ast.LowLevel.Mem.Proofs.Map.MapSat
public import Core.Ast.LowLevel.Mem.Proofs.Kern

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

theorem map_aussage : MapAussage :=
  ⟨memObligationsKern_alle .mapSpace, mapMeaning, map_joint⟩

theorem mapKind_aussage : MapKindAussage :=
  ⟨mapKindMeaning, mapUncached_erfuellbar⟩

end Gabbro.Core.Ast.LowLevel
