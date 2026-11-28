module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.Kern
public import Core.Ast.LowLevel.Mem.Proofs.SplitAt
public import Core.Ast.LowLevel.Mem.Proofs.SplitPages.SplitPagesSatisfiability
public import Core.Ast.LowLevel.Mem.Proofs.Merge.Merge
public import Core.Ast.LowLevel.Mem.Proofs.NewSpace
public import Core.Ast.LowLevel.Mem.Proofs.Map.Map
public import Core.Ast.LowLevel.Mem.Proofs.Protect.Protect
public import Core.Ast.LowLevel.Mem.Proofs.Unmap.UnmapSat
public import Core.Ast.LowLevel.Mem.Proofs.Flush.Flush
public import Core.Ast.LowLevel.Mem.Proofs.Flush.FlushNarrowJoint
public import Core.Ast.LowLevel.Mem.Proofs.Flush.FlushNarrowWide
public import Core.Ast.LowLevel.Mem.Proofs.Activate.Activate

namespace Gabbro.Core.Ast.LowLevel

open Waechter

private theorem kernConj {form : MemForm} (kern : memObligationsKern form) :
    MemParseAussage form ∧ MemInversionAussage form ∧ MemEindeutigAussage form ∧
    MemDruckAussage form ∧ MemElaboriertAussage form ∧ MemRealisiertAussage form ∧
    MemAnnahmeAussage form ∧ MemIdealAussage form ∧ MemEinheitAussage form ∧
    MemImplAussage form ∧ MemFortschrittAussage form ∧ MemErhaltungAussage form ∧
    MemRegelSicherAussage form ∧ MemRegelAntwortSicherAussage form ∧
    MemAussenLokalAussage form ∧ MemKostenAussage form ∧
    MemSchrankenAussage ∧ MemEtikettenAussage ∧ MemFlussAussage := kern

public def splitAtEntry : RegistryEntry ``MemTree.splitAt (schemaMem ``MemTree.splitAt) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .splitAt ∧ SplitAtMeaningAussage ∧
    MemErfuellbarAussage .splitAt from splitAt_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def splitPagesEntry : RegistryEntry ``MemTree.splitPages (schemaMem ``MemTree.splitPages) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .splitPages ∧ SplitPagesMeaningAussage ∧
    MemErfuellbarAussage .splitPages from splitPages_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def mergeEntry : RegistryEntry ``MemTree.merge (schemaMem ``MemTree.merge) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .merge ∧ MergeMeaningAussage ∧
    MemErfuellbarAussage .merge from merge_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def newSpaceEntry : RegistryEntry ``MemTree.newSpace (schemaMem ``MemTree.newSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .newSpace ∧ NewSpaceMeaningAussage ∧
    MemErfuellbarAussage .newSpace from newSpace_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

private def newGuestSpaceSurfaceProof : RegistryEntry ``MemTree.newGuestSpace
    ⟨.surface, statementsMem ``MemTree.newGuestSpace .newGuestSpace⟩ := by
  obtain ⟨kern, meaning, isolation, joint, reachable⟩ := newGuestSpace_aussage
  obtain ⟨parse, inversion, unique, print, elaborated, realized, admitted, ideal, units,
    implementation, progress, preservation, safe, answers, outside, cost, bounds, labels, flow⟩ := kernConj kern
  exact ⟨.surface ⟨parse, inversion, unique, print⟩ elaborated realized,
    ⟨admitted, outside, meaning, isolation⟩, ideal, units, implementation,
    ⟨preservation, progress, safe, answers, cost, bounds, labels, flow⟩, ⟨joint, reachable⟩⟩

public def newGuestSpaceEntry : RegistryEntry ``MemTree.newGuestSpace (schemaMem ``MemTree.newGuestSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
  exact newGuestSpaceSurfaceProof

public def newGuestSpaceCoreEntry :
    RegistryEntry ``MemInstruction.newGuestSpace newGuestSpaceCoreSchema where
  realization := .core newGuestSpaceOrigin
  acceptanceRule := newGuestSpaceSurfaceProof.acceptanceRule
  idealRule := newGuestSpaceSurfaceProof.idealRule
  unitsAndCommutation := newGuestSpaceSurfaceProof.unitsAndCommutation
  implementationRule := newGuestSpaceSurfaceProof.implementationRule
  preservation := newGuestSpaceSurfaceProof.preservation
  jointlySatisfiable := newGuestSpaceSurfaceProof.jointlySatisfiable

public theorem newGuestSpaceCorePacket :
    RegistryPacketProof ``MemInstruction.newGuestSpace NewGuestSpaceCoreAussage :=
  ⟨⟨newGuestSpace_aussage, ⟨newGuestSpaceCoreEntry⟩⟩⟩

public def mapEntry : RegistryEntry ``MemTree.mapSpace (schemaMem ``MemTree.mapSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .mapSpace ∧ MapMeaningAussage ∧
    MapJointAussage from map_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning, mapKind_aussage.1⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, ⟨hJoint, mapKind_aussage.2⟩⟩

public def protectEntry : RegistryEntry ``MemTree.protectSpace (schemaMem ``MemTree.protectSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .protectSpace ∧ ProtectMeaningAussage ∧
    ProtectJointAussage from protect_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def unmapEntry : RegistryEntry ``MemTree.unmapSpace (schemaMem ``MemTree.unmapSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .unmapSpace ∧ UnmapMeaningAussage ∧
    UnmapJointAussage from unmap_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def flushEntry : RegistryEntry ``MemTree.flushSpace (schemaMem ``MemTree.flushSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .flushSpace ∧ FlushMeaningAussage ∧
    FlushJointAussage from flush_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, ⟨hJoint, flushNarrowJoint, flushNarrowWideJoint⟩⟩

public def activateEntry : RegistryEntry ``MemTree.activateSpace (schemaMem ``MemTree.activateSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  rcases (show memObligationsKern .activateSpace ∧ ActivateMeaningAussage ∧
    ActivateJointAussage from activate_aussage) with ⟨hkern, hMeaning, hJoint⟩
  rcases kernConj hkern with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme,
    hIdeal, hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher,
    hAussen, hKosten, hSchranken, hEtiketten, hFluss⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

end Gabbro.Core.Ast.LowLevel
