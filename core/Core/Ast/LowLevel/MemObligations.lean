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

def SplitAtAussage : Prop :=
  memObligationsKern .splitAt ∧ MemErfuellbarAussage .splitAt ∧ SplitAtMeaningAussage

def SplitPagesAussage : Prop :=
  memObligationsKern .splitPages ∧ MemErfuellbarAussage .splitPages ∧ SplitPagesMeaningAussage

def MergeAussage : Prop :=
  memObligationsKern .merge ∧ MemErfuellbarAussage .merge ∧ MergeMeaningAussage

end Gabbro.Core.Ast.LowLevel
