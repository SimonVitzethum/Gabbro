module

public import Core.Ast.LowLevel.Execution

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine Text

def MemParseAussage (form : MemForm) : Prop :=
  ∀ text (tree : MemTree form), MemParse text tree ↔ blocks text [tree.print]

def MemInversionAussage (form : MemForm) : Prop :=
  ∀ (tree : MemTree form) tokens, tree.production tokens →
    ∃ pieces, Lexed tree.print pieces ∧ canonicalTokens pieces = tokens

def MemEindeutigAussage (form : MemForm) : Prop :=
  ∀ (first second : MemTree form) tokens, first.production tokens → second.production tokens →
    first = second

def MemDruckAussage (form : MemForm) : Prop :=
  ∀ (tree : MemTree form) pieces, Lexed tree.print pieces →
    tree.production (pieces.map PrintedToken.value)

def ElaboriertMem (k : Katalog) (scope : MemScope) (tree : MemTree form) (E : Unit k) : Prop :=
  ∃ op, elaborateMem k scope tree = some op ∧ E = unit op

def BezeichnetMem {form : MemForm} (k : Katalog) (scope : MemScope) (text : Text.RawText)
    (E : Unit k) : Prop :=
  ∃ tree : MemTree form, MemParse text tree ∧ ElaboriertMem k scope tree E

def MemElaboriertAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    ElaboriertMem k scope tree (unit op)

def MemRealisiertAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    ∀ s c, (unit op).system.kopf s c = some op ↔
      s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
        (op.evaluate s c).isSome = true

def MemAnnahmeAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    Annahme.RegelLokal (unit op) op

def MemIdealAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    Ideal.RegelAbgleich (unit op) op

def MemEinheitAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    (unit op).stotterLaenge op = 0

def MemImplAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    I.RegelBestimmt (unit op).einrichtung (unit op).system op

def MemFortschrittAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    Ideal.RegelFortschritt (unit op).system op

def MemErhaltungAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    I.RegelAbgleich (unit op) op ∧ I.RegelKomponierbar (unit op).einrichtung (unit op).system op

def MemRegelSicherAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    Sicherheit.RegelSicher (safetyUnit op) op

/-- The memory forms issue no question and commit no outside effect, so no
    reply event appears in their trace and no outstanding answer is consumed. -/
def MemRegelAntwortSicherAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      (∀ ev : AntwortEreignis, Ereignis.antwort ev ∉ trace.aussen) ∧
      next.verbraucht = s.verbraucht

def MemAussenLokalAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    Annahme.AussenLokal (unit op)

/-- M9 accounts for these occurrences as one model step, with no memory
    graph event, external event, or additional private step. -/
def MemKostenAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem k scope tree = some op →
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (unit op).stotterLaenge op = 0

/-- M9 bounds: the memory occurrences declare no resource bounds. Every bound
    stays open, so the language promises no time, memory or stack budget here. -/
def MemSchrankenAussage : Prop :=
  ∀ (k : Katalog) (op : Instruction k), (unit op).schranken = .leer

/-- M9 labels: the memory occurrences carry the empty label assignment, so
    every location, handle and channel they touch observes as public. -/
def MemEtikettenAussage : Prop :=
  ∀ (k : Katalog) (op : Instruction k), (unit op).etiketten = .leer

/-- M9 flows: the memory occurrences claim no constant-time discipline and
    emit no outputs, releases or speculative footprints. -/
def MemFlussAussage : Prop :=
  ∀ (k : Katalog) (op : Instruction k), (unit op).fluss = .leer

/-- Syntax, admission at the catalogue boundary, realization, and both transfer
    rules must hold jointly at the initial live occurrence. -/
def MemErfuellbarAussage (form : MemForm) : Prop :=
  ∃ (k : Katalog) (scope : MemScope) (tree : MemTree form) (op : Instruction k)
    (env : Umgebung) (start : AussenStart) (text : RawText) (transfer : Transfer k),
    KatalogWohlgeformt k ∧ (scope.regionen.map Subtype.val).Nodup ∧
    (scope.raeume.map Subtype.val).Nodup ∧ (scope.marken.map Subtype.val).Nodup ∧
    scope.regionen.length = start.regions.length ∧
    (unit op).ZulStart env start ∧ MemParse text tree ∧ elaborateMem k scope tree = some op ∧
    ElaboriertMem k scope tree (unit op) ∧
    let s := (I.start (unit op) start).2
    (unit op).system.kopf s entryContext = some op ∧ op.evaluate s entryContext = some transfer ∧
    op.ideal entryContext s () [plan] (transfer.apply entryContext s) ∧
    op.impl entryContext s () [plan] (transfer.apply entryContext s)

def memObligationsKern (form : MemForm) : Prop :=
  MemParseAussage form ∧ MemInversionAussage form ∧ MemEindeutigAussage form ∧ MemDruckAussage form ∧
  MemElaboriertAussage form ∧ MemRealisiertAussage form ∧ MemAnnahmeAussage form ∧
  MemIdealAussage form ∧ MemEinheitAussage form ∧ MemImplAussage form ∧ MemFortschrittAussage form ∧
  MemErhaltungAussage form ∧ MemRegelSicherAussage form ∧ MemRegelAntwortSicherAussage form ∧
  MemAussenLokalAussage form ∧ MemKostenAussage form ∧
  MemSchrankenAussage ∧ MemEtikettenAussage ∧ MemFlussAussage

def memObligations (form : MemForm) : Prop :=
  memObligationsKern form ∧ MemErfuellbarAussage form

/-- `r.split_at(a)` succeeds exactly when the caller owns `r` unborrowed and
    the point lies strictly inside. The two halves are disjoint, share the
    boundary `a`, and cover the original extent; the new tail object is
    brought to life in the authority ledger. -/
def SplitAtMeaningAussage : Prop :=
  ∀ (k : Katalog) (scope : MemScope) (region : Identifier) (point : Nat)
    (slot : Nat) (s : State k) (c : Kontext) (transfer : Transfer k),
    MemScope.slotRegion scope region = some slot →
    ((s.lokal c).regions[slot]? = none → (.splitRegion slot point).evaluate s c = none) ∧
    (∀ handle extent, heldRegion s c slot = some (handle, extent) →
      (extent.von < point ∧ point < extent.bis →
        (.splitRegion slot point).evaluate s c = some transfer →
        ∃ left right regions,
          transfer.value = .partition left right ∧
          left = ⟨extent.von, point⟩ ∧ right = ⟨point, extent.bis⟩ ∧
          transfer.regionen = some regions ∧
          regions = (s.lokal c).regions.set slot left ++ [right] ∧
          transfer.rechte = some (s.rechte.beleben regions.length.pred) ∧
          transfer.loan = none ∧ transfer.raeume = none ∧ transfer.tlb = none ∧
          transfer.aktiv = none ∧ transfer.marken = none ∧
          left.getrennt right ∧ left.von = extent.von ∧ left.bis = right.von ∧
          right.bis = extent.bis) ∧
      (¬ (extent.von < point ∧ point < extent.bis) →
        (.splitRegion slot point).evaluate s c = none))

/-- `r.split_pages(n)` succeeds exactly when the caller owns `r` unborrowed,
    the region starts page-aligned, and `n` pages fit strictly inside. The
    first chunk holds exactly `n` pages and stays page-aligned; disjointness,
    coverage and the ledger update are those of the address split. -/
def SplitPagesMeaningAussage : Prop :=
  ∀ (k : Katalog) (scope : MemScope) (region : Identifier) (pages : Nat)
    (slot : Nat) (s : State k) (c : Kontext) (transfer : Transfer k),
    MemScope.slotRegion scope region = some slot →
    ((s.lokal c).regions[slot]? = none → (.splitPages slot pages).evaluate s c = none) ∧
    (∀ handle extent, heldRegion s c slot = some (handle, extent) →
      let g := k.plattform.ziel.seitengranule
      let cut := extent.von + pages * g
      (extent.von % g = 0 ∧ 0 < pages ∧ cut < extent.bis →
        (.splitPages slot pages).evaluate s c = some transfer →
        ∃ left right regions,
          transfer.value = .partition left right ∧
          left = ⟨extent.von, cut⟩ ∧ right = ⟨cut, extent.bis⟩ ∧
          transfer.regionen = some regions ∧
          regions = (s.lokal c).regions.set slot left ++ [right] ∧
          transfer.rechte = some (s.rechte.beleben regions.length.pred) ∧
          transfer.loan = none ∧ transfer.raeume = none ∧ transfer.tlb = none ∧
          transfer.aktiv = none ∧ transfer.marken = none ∧
          left.getrennt right ∧ cut % g = 0 ∧ left.bis - left.von = pages * g ∧
          left.von = extent.von ∧ right.bis = extent.bis) ∧
      (¬ (extent.von % g = 0 ∧ 0 < pages ∧ cut < extent.bis) →
        (.splitPages slot pages).evaluate s c = none))

/-- `merge(r1, r2)` succeeds exactly when the caller owns both regions
    unborrowed, the slots differ, and the extents are adjacent. The merged
    extent covers both inputs; the consumed slot is revoked, so its old handle
    is dead while every other slot is untouched. -/
def MergeMeaningAussage : Prop :=
  ∀ (k : Katalog) (scope : MemScope) (r₁ r₂ : Identifier)
    (s₁ s₂ : Nat) (s : State k) (c : Kontext) (transfer : Transfer k),
    MemScope.slotRegion scope r₁ = some s₁ → MemScope.slotRegion scope r₂ = some s₂ →
    (((s.lokal c).regions[s₁]? = none ∨ (s.lokal c).regions[s₂]? = none) →
      (.mergeRegions s₁ s₂).evaluate s c = none) ∧
    (∀ h₁ e₁ h₂ e₂, heldRegion s c s₁ = some (h₁, e₁) → heldRegion s c s₂ = some (h₂, e₂) →
      (s₁ ≠ s₂ ∧ (e₁.bis = e₂.von ∨ e₂.bis = e₁.von) →
        (.mergeRegions s₁ s₂).evaluate s c = some transfer →
        ∃ merged regions,
          transfer.value = .merged merged ∧
          merged = ⟨Nat.min e₁.von e₂.von, Nat.max e₁.bis e₂.bis⟩ ∧
          transfer.regionen = some regions ∧
          regions = (s.lokal c).regions.set s₁ merged ∧
          transfer.rechte = some (s.rechte.widerrufen s₂) ∧
          transfer.loan = none ∧ transfer.raeume = none ∧ transfer.tlb = none ∧
          transfer.aktiv = none ∧ transfer.marken = none ∧
          (e₁.bis = e₂.von → merged.von = e₁.von ∧ merged.bis = e₂.bis) ∧
          (e₂.bis = e₁.von → merged.von = e₂.von ∧ merged.bis = e₁.bis) ∧
          ¬ (s.rechte.widerrufen s₂).Gueltig h₂) ∧
      (¬ (s₁ ≠ s₂ ∧ (e₁.bis = e₂.von ∨ e₂.bis = e₁.von)) →
        (.mergeRegions s₁ s₂).evaluate s c = none))

/-- `protect(s, virt, n, rights)` succeeds exactly when every page of the
    range is mapped, the base is page-aligned and canonical, and the right
    set is non-empty. Rights are replaced in place, keeping frame and
    generation; the cached translations of the range are dropped on every
    core at once, so no stale entry survives with the old rights. -/
def ProtectMeaningAussage : Prop :=
  ∀ (k : Katalog) (scope : MemScope) (sname : Identifier) (virt pages : Nat)
    (rights : List Speicherdienst) (sps : Nat) (s : State k) (c : Kontext)
    (transfer : Transfer k),
    MemScope.slotRaum scope sname = some sps →
    ((s.lokal c).spaces[sps]? = none → (.protectSpace sps virt pages rights).evaluate s c = none) ∧
    (∀ space, (s.lokal c).spaces[sps]? = some space →
      let z := k.plattform.ziel
      let g := z.seitengranule
      let base := virt / g
      (rights ≠ [] ∧ 0 < pages ∧ virt % g = 0 ∧
          (∀ i, i < pages → (space.abbildung (base + i)).isSome) ∧
          (∀ i, i < pages → z.virtuell (virt + i * g)) →
        (.protectSpace sps virt pages rights).evaluate s c = some transfer →
        ∃ abbildung tlb spaces',
          transfer.value = .protected ∧
          transfer.raeume = some spaces' ∧
          spaces' = (s.lokal c).spaces.set sps { space with abbildung := abbildung } ∧
          transfer.tlb = some tlb ∧
          transfer.loan = none ∧ transfer.regionen = none ∧ transfer.rechte = none ∧
          transfer.aktiv = none ∧ transfer.marken = none ∧
          (∀ i, i < pages → abbildung (base + i) =
            (space.abbildung (base + i)).map (fun e => { e with rights := rights })) ∧
          (∀ pg, pg < base ∨ base + pages ≤ pg → abbildung pg = space.abbildung pg) ∧
          (∀ co sp' pg, sp' = sps ∧ base ≤ pg ∧ pg < base + pages → tlb co sp' pg = none) ∧
          (∀ co sp' pg, sp' ≠ sps ∨ pg < base ∨ base + pages ≤ pg →
            tlb co sp' pg = (s.lokal c).tlb co sp' pg)) ∧
      (¬ (rights ≠ [] ∧ 0 < pages ∧ virt % g = 0 ∧
          (∀ i, i < pages → (space.abbildung (base + i)).isSome) ∧
          (∀ i, i < pages → z.virtuell (virt + i * g))) →
        (.protectSpace sps virt pages rights).evaluate s c = none))

/-- The map occurrence is reachable: a fresh space is created from an owned
    table region, then the mapping installs over an owned frame extent. Both
    rules execute, so the joint authority the map needs is really produced. -/
def MapJointAussage : Prop :=
  ∃ (k : Katalog) (scope : MemScope) (tNew : MemTree .spaceNew) (tMap : MemTree .mapSpace)
    (opNew opMap : Instruction k) (env : Umgebung) (start : AussenStart)
    (textNew textMap : RawText) (trNew trMap : Transfer k)
    (tables frames sname : Identifier) (tSlot fSlot : Nat) (virt : Nat)
    (rights : List Speicherdienst),
    KatalogWohlgeformt k ∧ (scope.regionen.map Subtype.val).Nodup ∧
    (scope.raeume.map Subtype.val).Nodup ∧ (scope.marken.map Subtype.val).Nodup ∧
    scope.regionen.length = start.regions.length ∧
    (unit opNew).ZulStart env start ∧
    MemParse textNew tNew ∧ MemParse textMap tMap ∧
    elaborateMem k scope tNew = some opNew ∧ elaborateMem k scope tMap = some opMap ∧
    ElaboriertMem k scope tNew (unit opNew) ∧ ElaboriertMem k scope tMap (unit opMap) ∧
    tNew = .newSpace tables ∧ tMap = .mapSpace sname virt frames rights ∧
    MemScope.slotRegion scope tables = some tSlot ∧
    MemScope.slotRegion scope frames = some fSlot ∧
    (∃ sps, MemScope.slotRaum scope sname = some sps) ∧
    let s₀ := (I.start (unit opNew) start).2
    (unit opNew).system.kopf s₀ entryContext = some opNew ∧
    opNew.evaluate s₀ entryContext = some trNew ∧
    opNew.ideal entryContext s₀ () [plan] (trNew.apply entryContext s₀) ∧
    opNew.impl entryContext s₀ () [plan] (trNew.apply entryContext s₀) ∧
    let s₁ := trNew.apply entryContext s₀
    opMap.evaluate s₁ entryContext = some trMap ∧
    opMap.ideal entryContext s₁ () [plan] (trMap.apply entryContext s₁) ∧
    opMap.impl entryContext s₁ () [plan] (trMap.apply entryContext s₁)

/-- The protect occurrence is reachable: creation, mapping, then the rights
    narrowing executes over the installed entries with both rules. -/
def ProtectJointAussage : Prop :=
  ∃ (k : Katalog) (scope : MemScope) (tNew : MemTree .spaceNew) (tMap : MemTree .mapSpace)
    (tProt : MemTree .protectSpace) (opNew opMap opProt : Instruction k) (env : Umgebung)
    (start : AussenStart) (textNew textMap textProt : RawText)
    (trNew trMap trProt : Transfer k)
    (tables frames sname : Identifier) (tSlot fSlot : Nat) (virt pages : Nat)
    (rights rights' : List Speicherdienst),
    KatalogWohlgeformt k ∧ (scope.regionen.map Subtype.val).Nodup ∧
    (scope.raeume.map Subtype.val).Nodup ∧ (scope.marken.map Subtype.val).Nodup ∧
    scope.regionen.length = start.regions.length ∧
    (unit opNew).ZulStart env start ∧
    MemParse textNew tNew ∧ MemParse textMap tMap ∧ MemParse textProt tProt ∧
    elaborateMem k scope tNew = some opNew ∧ elaborateMem k scope tMap = some opMap ∧
    elaborateMem k scope tProt = some opProt ∧
    ElaboriertMem k scope tNew (unit opNew) ∧ ElaboriertMem k scope tMap (unit opMap) ∧
    ElaboriertMem k scope tProt (unit opProt) ∧
    tNew = .newSpace tables ∧ tMap = .mapSpace sname virt frames rights ∧
    tProt = .protectSpace sname virt pages rights' ∧
    MemScope.slotRegion scope tables = some tSlot ∧
    MemScope.slotRegion scope frames = some fSlot ∧
    (∃ sps, MemScope.slotRaum scope sname = some sps) ∧
    let s₀ := (I.start (unit opNew) start).2
    (unit opNew).system.kopf s₀ entryContext = some opNew ∧
    opNew.evaluate s₀ entryContext = some trNew ∧
    opNew.ideal entryContext s₀ () [plan] (trNew.apply entryContext s₀) ∧
    opNew.impl entryContext s₀ () [plan] (trNew.apply entryContext s₀) ∧
    let s₁ := trNew.apply entryContext s₀
    opMap.evaluate s₁ entryContext = some trMap ∧
    opMap.ideal entryContext s₁ () [plan] (trMap.apply entryContext s₁) ∧
    opMap.impl entryContext s₁ () [plan] (trMap.apply entryContext s₁) ∧
    let s₂ := trMap.apply entryContext s₁
    opProt.evaluate s₂ entryContext = some trProt ∧
    opProt.ideal entryContext s₂ () [plan] (trProt.apply entryContext s₂) ∧
    opProt.impl entryContext s₂ () [plan] (trProt.apply entryContext s₂)

def SplitAtAussage : Prop :=
  memObligationsKern .splitAt ∧ MemErfuellbarAussage .splitAt ∧ SplitAtMeaningAussage

def SplitPagesAussage : Prop :=
  memObligationsKern .splitPages ∧ MemErfuellbarAussage .splitPages ∧ SplitPagesMeaningAussage

def MergeAussage : Prop :=
  memObligationsKern .merge ∧ MemErfuellbarAussage .merge ∧ MergeMeaningAussage

def NewSpaceAussage : Prop :=
  memObligationsKern .newSpace ∧ MemErfuellbarAussage .newSpace ∧ NewSpaceMeaningAussage

def MapAussage : Prop :=
  memObligationsKern .mapSpace ∧ MapJointAussage ∧ MapMeaningAussage

def ProtectAussage : Prop :=
  memObligationsKern .protectSpace ∧ ProtectJointAussage ∧ ProtectMeaningAussage

/-- `space.new(tables)` succeeds exactly when the caller owns the table region
    unborrowed and the extent is a non-empty, page-aligned range inside the
    physical address width. The fresh space starts with an empty page map,
    generation zero and no pending revocations; the identifier is the previous
    space count. Created spaces are well-formed, hence ready to activate. -/
def NewSpaceMeaningAussage : Prop :=
  ∀ (k : Katalog) (scope : MemScope) (tables : Identifier)
    (slot : Nat) (s : State k) (c : Kontext) (transfer : Transfer k),
    MemScope.slotRegion scope tables = some slot →
    ((s.lokal c).regions[slot]? = none → (.newSpace slot).evaluate s c = none) ∧
    (∀ handle extent, heldRegion s c slot = some (handle, extent) →
      let z := k.plattform.ziel
      (extent.von < extent.bis ∧ extent.bis ≤ 2 ^ z.physicalBits ∧
          extent.von % z.seitengranule = 0 →
        (.newSpace slot).evaluate s c = some transfer →
        ∃ sp spaces,
          transfer.value = .space (s.lokal c).spaces.length ∧
          sp = { tabellen := extent, abbildung := fun _ => none, generation := 0,
            ausstehend := [] } ∧
          transfer.raeume = some spaces ∧
          spaces = (s.lokal c).spaces ++ [sp] ∧
          transfer.loan = none ∧ transfer.regionen = none ∧ transfer.rechte = none ∧
          transfer.tlb = none ∧ transfer.aktiv = none ∧ transfer.marken = none ∧
          sp.Wohlgeformt z) ∧
      (¬ (extent.von < extent.bis ∧ extent.bis ≤ 2 ^ z.physicalBits ∧
          extent.von % z.seitengranule = 0) →
        (.newSpace slot).evaluate s c = none))

/-- `map(s, virt, frames, rights) else full` installs one page entry per page
    covered by the owned frame extent: the virtual base is page-aligned and
    canonical, every target page is absent from the table and from every
    pending revocation, and the right set is non-empty. Entries carry the
    frame base plus page index with the space's generation. The `full`
    channel is the lowering's resource signal; at the leaf, evaluation
    succeeds exactly under the stated authority and mapping conditions. -/
def MapMeaningAussage : Prop :=
  ∀ (k : Katalog) (scope : MemScope) (sname fname : Identifier) (virt : Nat)
    (rights : List Speicherdienst) (sps frs : Nat) (s : State k) (c : Kontext)
    (transfer : Transfer k),
    MemScope.slotRaum scope sname = some sps → MemScope.slotRegion scope fname = some frs →
    (((s.lokal c).spaces[sps]? = none ∨ (s.lokal c).regions[frs]? = none) →
      (.mapSpace sps virt frs rights).evaluate s c = none) ∧
    (∀ space fext, (s.lokal c).spaces[sps]? = some space →
      heldRegion s c frs = some (⟨frs, 0⟩, fext) →
      let z := k.plattform.ziel
      let g := z.seitengranule
      let bytes := fext.bis - fext.von
      let seiten := bytes / g
      let base := virt / g
      let fbasis := fext.von / g
      (rights ≠ [] ∧ fext.von < fext.bis ∧ bytes % g = 0 ∧ fext.von % g = 0 ∧
          0 < seiten ∧ virt % g = 0 ∧
          (∀ i, i < seiten → space.abbildung (base + i) = none) ∧
          (∀ i, i < seiten → z.virtuell (virt + i * g)) ∧
          (∀ t ∈ space.ausstehend, ∀ i, i < seiten →
            ¬ (t.seite ≤ base + i ∧ base + i < t.seite + t.seiten)) →
        (.mapSpace sps virt frs rights).evaluate s c = some transfer →
        ∃ abbildung spaces',
          transfer.value = .mapped ∧
          transfer.raeume = some spaces' ∧
          spaces' = (s.lokal c).spaces.set sps { space with abbildung := abbildung } ∧
          transfer.loan = none ∧ transfer.regionen = none ∧ transfer.rechte = none ∧
          transfer.tlb = none ∧ transfer.aktiv = none ∧ transfer.marken = none ∧
          (∀ i, i < seiten → abbildung (base + i) =
            some { frame := fbasis + i, rights := rights, generation := space.generation }) ∧
          (∀ pg, pg < base ∨ base + seiten ≤ pg → abbildung pg = space.abbildung pg)) ∧
      (¬ (rights ≠ [] ∧ fext.von < fext.bis ∧ bytes % g = 0 ∧ fext.von % g = 0 ∧
          0 < seiten ∧ virt % g = 0 ∧
          (∀ i, i < seiten → space.abbildung (base + i) = none) ∧
          (∀ i, i < seiten → z.virtuell (virt + i * g)) ∧
          (∀ t ∈ space.ausstehend, ∀ i, i < seiten →
            ¬ (t.seite ≤ base + i ∧ base + i < t.seite + t.seiten))) →
        (.mapSpace sps virt frs rights).evaluate s c = none))

end Gabbro.Core.Ast.LowLevel
