module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.SplitAt
public import Core.Ast.LowLevel.Mem.Proofs.SplitPages.SplitPagesSatisfiability
public import Core.Ast.LowLevel.Mem.Proofs.Merge.Merge
public import Core.Ast.LowLevel.Mem.Proofs.NewSpace
public import Core.Ast.LowLevel.Mem.Proofs.Map.Map
public import Core.Ast.LowLevel.Mem.Proofs.Protect.Protect
public import Core.Ast.LowLevel.Mem.Proofs.Unmap.UnmapSat
public import Core.Ast.LowLevel.Mem.Proofs.Flush.Flush
public import Core.Ast.LowLevel.Mem.Proofs.Activate.Activate

namespace Gabbro.Core.Ast.LowLevel

open Waechter

public def splitAtEntry : RegistryEntry ``MemTree.splitAt (schemaMem ``MemTree.splitAt) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := splitAt_aussage
  simp only [SplitAtAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def splitPagesEntry : RegistryEntry ``MemTree.splitPages (schemaMem ``MemTree.splitPages) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := splitPages_aussage
  simp only [SplitPagesAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def mergeEntry : RegistryEntry ``MemTree.merge (schemaMem ``MemTree.merge) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := merge_aussage
  simp only [MergeAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def newSpaceEntry : RegistryEntry ``MemTree.newSpace (schemaMem ``MemTree.newSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := newSpace_aussage
  simp only [NewSpaceAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def mapEntry : RegistryEntry ``MemTree.mapSpace (schemaMem ``MemTree.mapSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := map_aussage
  simp only [MapAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def protectEntry : RegistryEntry ``MemTree.protectSpace (schemaMem ``MemTree.protectSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := protect_aussage
  simp only [ProtectAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def unmapEntry : RegistryEntry ``MemTree.unmapSpace (schemaMem ``MemTree.unmapSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := unmap_aussage
  simp only [UnmapAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def flushEntry : RegistryEntry ``MemTree.flushSpace (schemaMem ``MemTree.flushSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := flush_aussage
  simp only [FlushAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

public def activateEntry : RegistryEntry ``MemTree.activateSpace (schemaMem ``MemTree.activateSpace) := by
  simp only [schemaMem, beq_iff_eq, Lean.Name.str.injEq, String.reduceEq, and_false,
    ite_true, ite_false, statementsMem, MeaningAussageMem, JointAussageMem]
  have h := activate_aussage
  simp only [ActivateAussage, memObligationsKern] at h
  rcases h with ⟨hParse, hInv, hEindeutig, hDruck, hElab, hReal, hAnnahme, hIdeal,
    hEinheit, hImpl, hFortschritt, hErhaltung, hSicher, hAntwortSicher, hAussen,
    hKosten, hSchranken, hEtiketten, hFluss, hMeaning, hJoint⟩
  exact ⟨.surface ⟨hParse, hInv, hEindeutig, hDruck⟩ hElab hReal,
    ⟨hAnnahme, hAussen, hMeaning⟩, hIdeal, hEinheit, hImpl,
    ⟨hErhaltung, hFortschritt, hSicher, hAntwortSicher, hKosten, hSchranken,
      hEtiketten, hFluss⟩, hJoint⟩

end Gabbro.Core.Ast.LowLevel
