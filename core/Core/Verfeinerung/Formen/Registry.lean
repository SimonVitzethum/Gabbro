module

public import Core.Verfeinerung.Formen.Abdeckung
public import Core.Waechter.Registry

namespace Gabbro.Core.Ast.Semantik

open Waechter

public theorem lokalEntry : RegistryPacketProof ``Wirkungsklasse.lokal LokalSimAussage := ⟨klassenSim .lokal⟩

public theorem rufEntry : RegistryPacketProof ``Wirkungsklasse.ruf RufSimAussage := ⟨klassenSim .ruf⟩

end Gabbro.Core.Ast.Semantik
