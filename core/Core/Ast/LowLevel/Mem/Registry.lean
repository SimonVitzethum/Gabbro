module

public import Core.Ast.LowLevel.Mem.RegionObligations
public import Core.Ast.LowLevel.Mem.SpaceObligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Waechter

def MapJointAussage : Prop :=
  MemErfuellbarNach .mapSpace fun «prefix» op =>
    ∃ tables virt frames rights, «prefix» = [.newSpace tables] ∧ op = .mapSpace 0 virt frames rights

def ProtectJointAussage : Prop :=
  MemErfuellbarNach .protectSpace fun «prefix» op =>
    ∃ tables virt frames original narrowed pages,
      «prefix» = [.newSpace tables, .mapSpace 0 virt frames original] ∧
      op = .protectSpace 0 virt pages narrowed

def UnmapJointAussage : Prop :=
  MemErfuellbarNach .unmapSpace fun «prefix» op =>
    ∃ tables virt frames rights pages,
      «prefix» = [.newSpace tables, .mapSpace 0 virt frames rights] ∧ op = .unmapSpace 0 virt pages

def FlushJointAussage : Prop :=
  MemErfuellbarNach .flushSpace fun «prefix» op =>
    ∃ tables virt frames rights pages name,
      «prefix» = [.newSpace tables, .mapSpace 0 virt frames rights, .unmapSpace 0 virt pages, .bindToken name] ∧
      op = .flushSpace name

def ActivateJointAussage : Prop :=
  MemErfuellbarNach .activateSpace fun «prefix» op =>
    ∃ tables, «prefix» = [.newSpace tables] ∧ op = .activateSpace 0

def MeaningAussageMem : MemForm → Prop
  | .splitAt => SplitAtMeaningAussage
  | .splitPages => SplitPagesMeaningAussage
  | .merge => MergeMeaningAussage
  | .newSpace => NewSpaceMeaningAussage
  | .mapSpace => MapMeaningAussage
  | .protectSpace => ProtectMeaningAussage
  | .unmapSpace => UnmapMeaningAussage
  | .flushSpace => FlushMeaningAussage
  | .activateSpace => ActivateMeaningAussage

def JointAussageMem : MemForm → Prop
  | .mapSpace => MapJointAussage
  | .protectSpace => ProtectJointAussage
  | .unmapSpace => UnmapJointAussage
  | .flushSpace => FlushJointAussage
  | .activateSpace => ActivateJointAussage
  | form => MemErfuellbarAussage form

def SplitAtAussage : Prop :=
  memObligationsKern .splitAt ∧ SplitAtMeaningAussage ∧ MemErfuellbarAussage .splitAt

def SplitPagesAussage : Prop :=
  memObligationsKern .splitPages ∧ SplitPagesMeaningAussage ∧ MemErfuellbarAussage .splitPages

def MergeAussage : Prop :=
  memObligationsKern .merge ∧ MergeMeaningAussage ∧ MemErfuellbarAussage .merge

def NewSpaceAussage : Prop :=
  memObligationsKern .newSpace ∧ NewSpaceMeaningAussage ∧ MemErfuellbarAussage .newSpace

def MapAussage : Prop := memObligationsKern .mapSpace ∧ MapMeaningAussage ∧ MapJointAussage
def ProtectAussage : Prop := memObligationsKern .protectSpace ∧ ProtectMeaningAussage ∧ ProtectJointAussage
def UnmapAussage : Prop := memObligationsKern .unmapSpace ∧ UnmapMeaningAussage ∧ UnmapJointAussage
def FlushAussage : Prop := memObligationsKern .flushSpace ∧ FlushMeaningAussage ∧ FlushJointAussage
def ActivateAussage : Prop := memObligationsKern .activateSpace ∧ ActivateMeaningAussage ∧ ActivateJointAussage

def statementsMem (constructor : Lean.Name) (form : MemForm) : RegistryStatements constructor .surface where
  realization := .surface (MemParseAussage form ∧ MemInversionAussage form ∧
    MemEindeutigAussage form ∧ MemDruckAussage form)
    (MemElaboriertAussage form) (MemRealisiertAussage form)
  acceptanceRule := MemAnnahmeAussage form ∧ MemAussenLokalAussage form ∧ MeaningAussageMem form
  idealRule := MemIdealAussage form
  unitsAndCommutation := MemEinheitAussage form
  implementationRule := MemImplAussage form
  preservation := MemErhaltungAussage form ∧ MemFortschrittAussage form ∧
    MemRegelSicherAussage form ∧ MemRegelAntwortSicherAussage form ∧ MemKostenAussage form ∧
    MemSchrankenAussage ∧ MemEtikettenAussage ∧ MemFlussAussage
  jointlySatisfiable := JointAussageMem form

def schemaMem (constructor : Lean.Name) : RegistrySchema constructor :=
  let form := if constructor == ``MemTree.splitAt then MemForm.splitAt
    else if constructor == ``MemTree.splitPages then MemForm.splitPages
    else if constructor == ``MemTree.merge then MemForm.merge
    else if constructor == ``MemTree.newSpace then MemForm.newSpace
    else if constructor == ``MemTree.mapSpace then MemForm.mapSpace
    else if constructor == ``MemTree.protectSpace then MemForm.protectSpace
    else if constructor == ``MemTree.unmapSpace then MemForm.unmapSpace
    else if constructor == ``MemTree.flushSpace then MemForm.flushSpace
    else MemForm.activateSpace
  ⟨.surface, statementsMem constructor form⟩

end Gabbro.Core.Ast.LowLevel
