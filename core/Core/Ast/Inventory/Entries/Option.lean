module

public import Core.Ast.Aggregate.Carrier.Option.ConstructProofs
public import Core.Ast.Aggregate.Carrier.Option.MatchProofs
public import Core.Ast.Aggregate.Carrier.Option.TestProofs
public import Core.Ast.Semantik.Kernregister

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem optionTestPacket : OptionTestProofPacket :=
  ⟨optionTestInversion, optionTestCases, optionTestDerivation, optionTestParse,
    optionTestElaboriert, optionTestRealisiert, optionTestAnnahme, optionTestIdeal,
    optionTestEinheit, optionTestImpl, optionTestErhaltung, optionTestRegelSicher,
    optionTestErfuellbarAm, optionTestInitialized⟩

public def optionTestEntry :
    RegistryPacketEntry ``Expr.optionIsSome (exprSchema ``Expr.optionIsSome) OptionTestProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface optionTestParse optionTestElaboriert optionTestRealisiert, optionTestAnnahme,
      optionTestIdeal, optionTestEinheit, optionTestImpl, optionTestErhaltung, optionTestErfuellbarAm⟩
  packetProof := optionTestPacket

public def optionIstBesetztEntry :
    RegistryPacketEntry ``Befehl.optionIstBesetzt (befehlSchema ``Befehl.optionIstBesetzt) OptionTestProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (optionTestIdeal scope).1⟩, optionTestAnnahme,
      optionTestIdeal, optionTestEinheit, optionTestImpl, optionTestErhaltung, optionTestErfuellbarAm⟩
  packetProof := optionTestPacket

private theorem optionConstructorPacket : OptionConstructorProofPacket :=
  ⟨optionInitializerInversion, optionInitializerPrint, optionAbsent, optionPresent,
    optionLetDerivation, optionReturnDerivation, optionConstructorParse, optionConstructorElaboriert,
    optionConstructorRealisiert, optionConstructorAnnahme, optionConstructorIdeal, optionConstructorEinheit,
    optionConstructorImpl, optionConstructorErhaltung, optionConstructorRegelSicher,
    optionLetErfuellbarAm, optionReturnErfuellbarAm⟩

public def letOptionEntry :
    RegistryPacketEntry ``Stmt.letOption (stmtSchema ``Stmt.letOption) OptionConstructorProofPacket where
  entry := by
    simp only [stmtSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface optionConstructorParse.1 optionConstructorElaboriert.1 optionConstructorRealisiert.1,
      optionConstructorAnnahme.1, optionConstructorIdeal.1, optionConstructorEinheit.1,
      optionConstructorImpl.1, optionConstructorErhaltung.1, optionLetErfuellbarAm⟩
  packetProof := optionConstructorPacket

public def retOptionEntry :
    RegistryPacketEntry ``Stmt.retOption (stmtSchema ``Stmt.retOption) OptionConstructorProofPacket where
  entry := by
    simp only [stmtSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface optionConstructorParse.2 optionConstructorElaboriert.2 optionConstructorRealisiert.2,
      optionConstructorAnnahme.2, optionConstructorIdeal.2, optionConstructorEinheit.2,
      optionConstructorImpl.2, optionConstructorErhaltung.2, optionReturnErfuellbarAm⟩
  packetProof := optionConstructorPacket

public theorem optionMatchEntry : RegistryPacketProof ``optionMatchForm OptionMatchProofPacket :=
  ⟨⟨optionMatchPayload, optionMatchDerivation, optionMatchParse, optionMatchElaboriert,
    optionMatchRealisiert, optionMatchAnnahme, optionMatchIdeal, optionMatchEinheit,
    optionMatchImpl, optionMatchErhaltung, optionMatchRegelSicher, optionMatchErfuellbarAm⟩⟩

end Gabbro.Core.Ast.Semantik
