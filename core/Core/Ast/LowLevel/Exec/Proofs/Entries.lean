module

public import Core.Ast.LowLevel.Exec.Registry
public import Core.Ast.LowLevel.Exec.Proofs.ExecKern
public import Core.Ast.LowLevel.Exec.Proofs.ExecStateDecl
public import Core.Ast.LowLevel.Exec.Proofs.ExecJump
public import Core.Ast.LowLevel.Exec.Proofs.Handoff
public import Core.Ast.LowLevel.Exec.Proofs.ExecWait
public import Core.Ast.LowLevel.Exec.Proofs.ExecStop
public import Core.Ast.LowLevel.Exec.Proofs.ExecEntry

namespace Gabbro.Core.Ast.LowLevel

open Waechter

private theorem kernConj {form : ExecForm} (kern : execObligationsKern form) :
    ExecParseAussage form ∧ ExecInversionAussage form ∧ ExecEindeutigAussage form ∧
    ExecDruckAussage form ∧ ExecElaboriertAussage form ∧ ExecRealisiertAussage form ∧
    ExecAnnahmeAussage form ∧ ExecIdealAussage form ∧ ExecEinheitAussage form ∧
    ExecImplAussage form ∧ ExecFortschrittAussage form ∧ ExecErhaltungAussage form ∧
    ExecRegelSicherAussage form ∧ ExecRegelAntwortSicherAussage form ∧
    ExecAussenLokalAussage form ∧ ExecKostenAussage form ∧
    ExecSchrankenAussage ∧ ExecEtikettenAussage ∧ ExecFlussAussage := kern

public def stateDeclEntry : RegistryEntry ``ExecTree.stateDecl (schemaExec ``ExecTree.stateDecl) := by
  simp only [schemaExec, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsExec, MeaningAussageExec, JointAussageExec]
  rcases (show execObligationsKern .stateDecl ∧ StateDeclMeaningAussage ∧
    ExecErfuellbarAussage .stateDecl from stateDecl_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def jumpEntry : RegistryEntry ``ExecTree.jump (schemaExec ``ExecTree.jump) := by
  simp only [schemaExec, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsExec, MeaningAussageExec, JointAussageExec]
  rcases (show execObligationsKern .jump ∧ JumpMeaningAussage ∧
    JumpJointAussage from jump_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def jumpLongEntry : RegistryEntry ``ExecTree.jumpLong (schemaExec ``ExecTree.jumpLong) := by
  simp only [schemaExec, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsExec, MeaningAussageExec, JointAussageExec]
  rcases (show execObligationsKern .jumpLong ∧ JumpLongMeaningAussage ∧
    JumpLongJointAussage from jumpLong_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def waitInterruptEntry : RegistryEntry ``ExecTree.waitInterrupt (schemaExec ``ExecTree.waitInterrupt) := by
  simp only [schemaExec, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsExec, MeaningAussageExec, JointAussageExec]
  rcases (show execObligationsKern .waitInterrupt ∧ WaitMeaningAussage ∧
    WaitJointAussage from wait_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def stopCoreEntry : RegistryEntry ``ExecTree.stopCore (schemaExec ``ExecTree.stopCore) := by
  simp only [schemaExec, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsExec, MeaningAussageExec, JointAussageExec]
  rcases (show execObligationsKern .stopCore ∧ StopMeaningAussage ∧
    StopJointAussage from stop_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def entryDeclEntry : RegistryEntry ``ExecTree.entryDecl (schemaExec ``ExecTree.entryDecl) := by
  simp only [schemaExec, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsExec, MeaningAussageExec, JointAussageExec]
  rcases (show execObligationsKern .entryDecl ∧ EntryMeaningAussage ∧
    ExecErfuellbarAussage .entryDecl from entry_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

end Gabbro.Core.Ast.LowLevel
