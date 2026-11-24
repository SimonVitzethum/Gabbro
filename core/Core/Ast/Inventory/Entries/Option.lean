module

public import Core.Ast.Aggregate.Carrier.Option.MatchProofs

namespace Gabbro.Core.Ast.Semantik

open Waechter

public theorem optionMatchEntry : RegistryPacketProof ``optionMatchForm OptionMatchProofPacket :=
  ⟨⟨optionMatchPayload, optionMatchDerivation, optionMatchParse, optionMatchElaboriert,
    optionMatchRealisiert, optionMatchAnnahme, optionMatchIdeal, optionMatchEinheit,
    optionMatchImpl, optionMatchErhaltung, optionMatchRegelSicher, optionMatchErfuellbarAm⟩⟩

end Gabbro.Core.Ast.Semantik
