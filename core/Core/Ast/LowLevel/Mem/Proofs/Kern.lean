module

public import Core.Ast.LowLevel.Mem.Obligations
public import Core.Ast.LowLevel.Mem.Proofs.Activate.ActivateObligations
public import Core.Ast.LowLevel.Mem.Proofs.Activate.ActivatePreservation

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

theorem memParseKern (form : MemForm) : MemParseAussage form := memParseActivate form

theorem memInversionKern (form : MemForm) : MemInversionAussage form := memInversionActivate form

theorem memEindeutigKern (form : MemForm) : MemEindeutigAussage form := memEindeutigActivate form

theorem memDruckKern (form : MemForm) : MemDruckAussage form := memDruckActivate form

theorem memElaboriertKern (form : MemForm) : MemElaboriertAussage form := memElaboriert form

theorem memRealisiertKern (form : MemForm) : MemRealisiertAussage form := memRealisiertActivate form

theorem memAnnahmeKern (form : MemForm) : MemAnnahmeAussage form := memAnnahmeActivate form

theorem memIdealKern (form : MemForm) : MemIdealAussage form := memIdealActivate form

theorem memEinheitKern (form : MemForm) : MemEinheitAussage form := memEinheit form

theorem memImplKern (form : MemForm) : MemImplAussage form := memImpl form

theorem memFortschrittKern (form : MemForm) : MemFortschrittAussage form := memFortschrittActivate form

theorem memErhaltungKern (form : MemForm) : MemErhaltungAussage form := memErhaltungActivate form

theorem memRegelSicherKern (form : MemForm) : MemRegelSicherAussage form := memRegelSicherActivate form

theorem memRegelAntwortSicherKern (form : MemForm) : MemRegelAntwortSicherAussage form :=
  activateRegelAntwortSicher form

theorem memAussenLokalKern (form : MemForm) : MemAussenLokalAussage form := memAussenLokalActivate form

theorem memKostenKern (form : MemForm) : MemKostenAussage form := memKostenActivate form

theorem memObligationsKern_alle (form : MemForm) : memObligationsKern form :=
  ⟨memParseKern form, memInversionKern form, memEindeutigKern form, memDruckKern form,
    memElaboriertKern form, memRealisiertKern form, memAnnahmeKern form, memIdealKern form,
    memEinheitKern form, memImplKern form, memFortschrittKern form, memErhaltungKern form,
    memRegelSicherKern form, memRegelAntwortSicherKern form, memAussenLokalKern form,
    memKostenKern form, memSchranken, memEtiketten, memFluss⟩

end Gabbro.Core.Ast.LowLevel
