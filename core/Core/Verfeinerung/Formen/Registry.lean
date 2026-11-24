module

public import Core.Verfeinerung.Formen.Abdeckung
public import Core.Waechter.Registry

namespace Gabbro.Core.Ast.Semantik

open Waechter

public theorem skalarEntry : RegistryPacketProof ``SimFamilie.skalar SkalarSimAussage := ⟨skalarSim⟩

public theorem kontrollflussEntry :
    RegistryPacketProof ``SimFamilie.kontrollfluss KontrollflussSimAussage := ⟨kontrollflussSim⟩

public theorem aufrufSchleifeEntry :
    RegistryPacketProof ``SimFamilie.aufrufSchleife AufrufSchleifeSimAussage := ⟨aufrufSchleifeSim⟩

public theorem aggregatEntry : RegistryPacketProof ``SimFamilie.aggregat AggregatSimAussage := ⟨aggregatSim⟩

public theorem varianteEntry : RegistryPacketProof ``SimFamilie.variante VarianteSimAussage := ⟨varianteSim⟩

public theorem textEntry : RegistryPacketProof ``SimFamilie.text TextSimAussage := ⟨textSim⟩

end Gabbro.Core.Ast.Semantik
