module

public import Core.Ast.LowLevel.Mem.RegionObligations
public import Core.Ast.LowLevel.Mem.SpaceObligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter Annahme Sicherheit Aussen

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

/-- **Joint satisfiability of the completion of a narrowing.** Unlike the release of an unmapped range,
    the prefix here creates a space, maps a frame with rights, performs the staged `protect` that narrows
    the table and records a pending token (`nurRechte = true`), then binds that token. In the reached state
    `flushSpace` of the bound token completes the narrowing with `.protected`, and no pending token covers
    any page of the range any more. The run is a real, reachable run of `memProgram`: no state is built by
    hand. The translation cache of this run is empty throughout (`map` invalidates its range, `protect`
    touches no cache and no `tlbFuellen` occurs), so the completion is enabled without an eviction step;
    a run with a wider cached cell would need a `tlbVerdraengen` step before `flushSpace` (THEOREM-MAP §219). -/
def FlushNarrowJointAussage : Prop :=
  ∃ (k : Katalog) (scope : MemScope) (tree : MemTree .flushSpace) (op : MemInstruction)
    (env : Katalog.Umgebung) (start : AussenStart) (text : RawText) («prefix» : List MemInstruction)
    (s : MemState) (next : MemFrame) (token : Zuruecknahme),
    let E := memProgram k («prefix» ++ [op])
    (∃ tables virt frames rights pages narrowed name,
      «prefix» = [.newSpace tables, .mapSpace 0 virt frames rights,
        .protectSpace 0 virt pages narrowed, .bindToken name] ∧ op = .flushSpace name) ∧
    Hardware k env ∧ E.ZulStart env start ∧ Annahme.Akzeptiert E ∧
    (scope.regionen.map Subtype.val).Nodup ∧ (scope.raeume.map Subtype.val).Nodup ∧
    (scope.marken.map Subtype.val).Nodup ∧
    BezeichnetMem k scope text (memUnit k op) .flushSpace ∧ MemParse text tree ∧
    elaborateMem scope tree = some op ∧
    E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s entryContext = some op ∧
    op.evaluate k.plattform.ziel s entryContext = some next ∧
    token.nurRechte = true ∧ token ∈ (s.lokal entryContext).verengt ∧
    next.result = some .«protected» ∧ token ∉ next.verengt ∧
    (∀ t ∈ next.verengt, ∀ pg, token.contains pg → ¬ t.contains pg) ∧
    E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) ∧
    E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s)

/-- **Joint satisfiability of the completion of a narrowing with a wider cached cell.** The prefix
    creates a space, maps a frame with `[read, write]`, fills a translation of the page into the cache,
    performs the staged `protect` down to `[read]` and binds the pending token. In the reached state a
    wider cell is cached, so `flushSpace` is refused. After a `tlbVerdraengen` step drops that cell the
    same `flushSpace` completes the narrowing with `.protected` and no pending token covers the range.
    The whole run is reachable through real steps of `memProgram` (`System.IErreichbar.schritt`); no state
    is built by hand. This is the wider-cache counterpart of `FlushNarrowJointAussage`, whose cache is
    empty throughout (THEOREM-MAP §219). -/
def FlushNarrowWideJointAussage : Prop :=
  ∃ (k : Katalog) (scope : MemScope) (tree : MemTree .flushSpace) (op evict : MemInstruction)
    (env : Katalog.Umgebung) (start : AussenStart) (text : RawText)
    (tables virt frames pages core sp page : Nat) (rights narrowed : List Speicherdienst)
    (name : Identifier) («prefix» : List MemInstruction)
    (s s' : MemState) (next : MemFrame) (token : Zuruecknahme),
    let E := memProgram k («prefix» ++ [evict, op])
    «prefix» = [.newSpace tables, .mapSpace 0 virt frames rights,
      .tlbFuellen core sp page, .protectSpace 0 virt pages narrowed, .bindToken name] ∧
    rights = [.read, .write] ∧ narrowed = [.read] ∧
    evict = .tlbVerdraengen core sp page ∧ op = .flushSpace name ∧
    Hardware k env ∧ E.ZulStart env start ∧ Annahme.Akzeptiert E ∧
    (scope.regionen.map Subtype.val).Nodup ∧ (scope.raeume.map Subtype.val).Nodup ∧
    (scope.marken.map Subtype.val).Nodup ∧
    BezeichnetMem k scope text (memUnit k op) .flushSpace ∧ MemParse text tree ∧
    elaborateMem scope tree = some op ∧
    E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s entryContext = some evict ∧
    (∃ zelle, zelle ∈ (s.lokal entryContext).tlb.zellen ∧ zelle.raum = sp ∧
      pageRange (virt / k.plattform.ziel.seitengranule) pages zelle.seite ∧
      ∃ right ∈ zelle.eintrag.rights, right ∉ narrowed) ∧
    (∃ space, (s.lokal entryContext).spaces[token.raum]? = some space ∧
      ((s.lokal entryContext).marken.find? (fun p => p.1.val == name.val)).map Prod.snd = some token ∧
      ¬ (s.lokal entryContext).tlb.NichtBreiter space token.raum token.seite token.seiten) ∧
    token.nurRechte = true ∧ token ∈ (s.lokal entryContext).verengt ∧
    op.evaluate k.plattform.ziel s entryContext = none ∧
    E.system.IErreichbar (I.start E start).2 s' ∧ E.system.kopf s' entryContext = some op ∧
    op.evaluate k.plattform.ziel s' entryContext = some next ∧
    next.result = some .«protected» ∧ token ∉ next.verengt ∧
    (∀ t ∈ next.verengt, ∀ pg, token.contains pg → ¬ t.contains pg) ∧
    E.system.ISchritt entryContext s' () [plan] (next.advance entryContext s') ∧
    E.system.ImplSchritt entryContext s' () [plan] (next.advance entryContext s')

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
  | .flushSpace => FlushJointAussage ∧ FlushNarrowJointAussage ∧ FlushNarrowWideJointAussage
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
