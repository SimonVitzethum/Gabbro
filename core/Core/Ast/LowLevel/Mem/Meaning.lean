module

public import Core.Ast.LowLevel.Mem.State

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

inductive MemInstruction where
  | splitRegion (slot point : Nat)
  | splitPages (slot pages : Nat)
  | mergeRegions (first second : Nat)
  | newSpace (tables : Nat)
  | mapSpace (space virt frames : Nat) (rights : List Speicherdienst)
  | protectSpace (space virt pages : Nat) (rights : List Speicherdienst)
  | unmapSpace (space virt pages : Nat)
  | flushSpace (name : Identifier)
  | activateSpace (space : Nat)
  | bindToken (name : Identifier)
  /-- A core takes the present table entry of a page into its translation cache. No source form
      elaborates to it: it stands for the translations hardware caches on its own, so that every
      statement over the unit also covers runs with stale translations. -/
  | tlbFuellen (core space page : Nat)

def elaborateMem (scope : MemScope) : MemTree form → Option MemInstruction
  | .splitAt region point => (scope.slotRegion region).map (fun slot => .splitRegion slot point)
  | .splitPages region pages => (scope.slotRegion region).map (fun slot => .splitPages slot pages)
  | .merge first second => do
    let left ← scope.slotRegion first
    let right ← scope.slotRegion second
    pure (.mergeRegions left right)
  | .newSpace tables => (scope.slotRegion tables).map .newSpace
  | .mapSpace space virt frames rights => do
    let sp ← scope.slotRaum space
    let fr ← scope.slotRegion frames
    pure (.mapSpace sp virt fr rights)
  | .protectSpace space virt pages rights => do
    let sp ← scope.slotRaum space
    pure (.protectSpace sp virt pages rights)
  | .unmapSpace space virt pages => do
    let sp ← scope.slotRaum space
    pure (.unmapSpace sp virt pages)
  | .flushSpace name => (scope.slotMarke name).map (fun _ => .flushSpace name)
  | .activateSpace space => (scope.slotRaum space).map .activateSpace

/-- A single region cut supplies both the left and the right authority. -/
def MemFrame.partition (frame : MemFrame) (slot : Nat) (region : MemRegion) (point : Nat) : MemFrame :=
  let left := { region with extent := ⟨region.extent.von, point⟩ }
  let right := { region with extent := ⟨point, region.extent.bis⟩ }
  { frame with
    result := some (.partition left right)
    regions := frame.regions.set slot (some left) ++ [some right] }

def pageRange (base pages index : Nat) : Prop := base ≤ index ∧ index < base + pages

instance (base pages index : Nat) : Decidable (pageRange base pages index) :=
  inferInstanceAs (Decidable (_ ∧ _))

def validVirtualRange (target : ZielDaten) (virt pages : Nat) : Bool :=
  decide (0 < pages ∧ virt % target.seitengranule = 0) &&
    (List.range pages).all fun i => decide (target.virtuell (virt + i * target.seitengranule))

/-- The cells of a page range of one space, on every core. -/
def TlbZelle.imBereich (zelle : TlbZelle) (space base pages : Nat) : Bool :=
  decide (zelle.raum = space ∧ pageRange base pages zelle.seite)

/-- Dropping the cells of a page range on every core. -/
def TranslationCache.invalidate (cache : TranslationCache) (space base pages : Nat) : TranslationCache :=
  ⟨cache.zellen.filter fun zelle => !zelle.imBereich space base pages⟩

/-- No core caches a translation of a page of the range. -/
def TranslationCache.Frei (cache : TranslationCache) (space base pages : Nat) : Prop :=
  ∀ zelle ∈ cache.zellen, zelle.imBereich space base pages = false

def TranslationCache.frei (cache : TranslationCache) (space base pages : Nat) : Bool :=
  cache.zellen.all fun zelle => !zelle.imBereich space base pages

theorem TranslationCache.frei_eq_true {cache : TranslationCache} {space base pages : Nat} :
    cache.frei space base pages = true ↔ cache.Frei space base pages := by
  simp only [TranslationCache.frei, TranslationCache.Frei, List.all_eq_true, Bool.not_eq_true']

theorem TranslationCache.frei_invalidate (cache : TranslationCache) (space base pages : Nat) :
    (cache.invalidate space base pages).Frei space base pages := by
  intro zelle mem
  have kept := (List.mem_filter.mp mem).2
  simpa only [Bool.not_eq_true'] using kept

theorem TranslationCache.haelt_invalidate (cache : TranslationCache)
    (space base pages core sp page : Nat) (entry : Seiteneintrag) :
    (cache.invalidate space base pages).Haelt core sp page entry ↔
      cache.Haelt core sp page entry ∧ ¬ (sp = space ∧ pageRange base pages page) := by
  simp only [TranslationCache.Haelt, TranslationCache.invalidate, List.mem_filter,
    TlbZelle.imBereich, Bool.not_eq_true', decide_eq_false_iff_not]

/-- The operations use the acting frame as their authority source. Table
    updates and invalidation are reflected in a single successor frame. -/
def MemInstruction.evaluate (target : ZielDaten) (op : MemInstruction)
    (s : MemState) (c : Kontext) : Option MemFrame :=
  let frame := s.lokal c
  let granule := target.seitengranule
  match op with
  | .splitRegion slot point => do
    let region ← heldMemRegion target s c slot
    if region.extent.von < point ∧ point < region.extent.bis then
      pure (frame.partition slot region point)
    else none
  | .splitPages slot pages => do
    let region ← heldMemRegion target s c slot
    let cut := region.extent.von + pages * granule
    if region.extent.von % granule = 0 ∧ 0 < pages ∧ cut < region.extent.bis then
      pure (frame.partition slot region cut)
    else none
  | .mergeRegions first second => do
    let left ← heldMemRegion target s c first
    let right ← heldMemRegion target s c second
    if first ≠ second ∧ left.extent.von < left.extent.bis ∧ right.extent.von < right.extent.bis ∧
        (left.extent.bis = right.extent.von ∨ right.extent.bis = left.extent.von) then
      let joined : MemRegion := ⟨
        ⟨min left.extent.von right.extent.von, max left.extent.bis right.extent.bis⟩,
        left.backing ++ right.backing⟩
      pure { frame with
        result := some (.merged joined)
        regions := (frame.regions.set first (some joined)).set second none }
    else none
  | .newSpace tables => do
    let region ← heldMemRegion target s c tables
    if region.extent.seiten target then
      let space : Adressraum := ⟨region.extent, [], 0, []⟩
      pure { frame with result := some (.space frame.spaces.length), spaces := frame.spaces ++ [space] }
    else none
  | .mapSpace sp virt slot rights => do
    let space ← frame.spaces[sp]?
    let region ← heldMemRegion target s c slot
    let extent := region.extent
    let pages := (extent.bis - extent.von) / granule
    let base := virt / granule
    let range := List.range pages
    if rights ≠ [] ∧ extent.seiten target ∧ validVirtualRange target virt pages ∧
        (range.all fun i => (space.abbildung (base + i)).isNone) ∧
        (space.ausstehend.all fun token =>
          range.all fun i => decide (¬ token.contains (base + i))) then
      let entries := range.map fun i => (base + i, ⟨extent.von / granule + i, rights, space.generation⟩)
      pure { frame with
        result := some .mapped
        spaces := frame.spaces.set sp { space with entries := space.entries ++ entries } }
    else none
  | .protectSpace sp virt pages rights => do
    let space ← frame.spaces[sp]?
    let base := virt / granule
    if rights ≠ [] ∧ validVirtualRange target virt pages ∧
        ((List.range pages).all fun i =>
          (space.abbildung (base + i)).any fun entry => rights.all (· ∈ entry.rights)) then
      let entries := space.entries.map fun (page, entry) =>
        if pageRange base pages page then (page, { entry with rights }) else (page, entry)
      pure { frame with
        result := some .«protected»
        spaces := frame.spaces.set sp { space with entries },
        tlb := frame.tlb.invalidate sp base pages }
    else none
  | .unmapSpace sp virt pages => do
    let space ← frame.spaces[sp]?
    let base := virt / granule
    let first ← space.abbildung base
    if validVirtualRange target virt pages ∧ ((List.range pages).all fun i =>
        ((space.abbildung (base + i)).map Seiteneintrag.frame) == some (first.frame + i)) then
      let entries := space.entries.filter fun (page, _) => !decide (pageRange base pages page)
      let token : Zuruecknahme := ⟨sp, base, pages, space.generation + 1, first.frame⟩
      pure { frame with
        result := some (.pending token)
        spaces := frame.spaces.set sp
          { space with entries, generation := token.generation, ausstehend := token :: space.ausstehend } }
    else none
  | .flushSpace name => do
    let (_, token) ← frame.marken.find? (fun p => p.1.val == name.val)
    let space ← frame.spaces[token.raum]?
    -- The release step of a shootdown: the frames return only when the table entries are gone AND no
    -- core still caches a translation of them. The remote invalidations are steps of the handlers, never
    -- implied by this step.
    if token ∈ space.ausstehend &&
        ((List.range token.seiten).all fun i => (space.abbildung (token.seite + i)).isNone) &&
        frame.tlb.frei token.raum token.seite token.seiten then
      pure { frame with
        result := some (.frames (token.frames granule))
        spaces := frame.spaces.set token.raum
          { space with ausstehend := space.ausstehend.filter (· != token) },
        marken := frame.marken.filter (fun p => p.1.val != name.val && p.2 != token) }
    else none
  | .activateSpace sp => do
    let space ← frame.spaces[sp]?
    if space.Aktivierbar target s c then pure { frame with result := some .activated, active := some sp }
    else none
  | .bindToken name => do
    let some (.pending token) := frame.result | none
    frame.bindMarke name token
  | .tlbFuellen core sp page => do
    let space ← frame.spaces[sp]?
    let entry ← space.abbildung page
    pure { frame with tlb := frame.tlb.fill ⟨core, sp, page, entry⟩ }

/-- Evaluation reads only the acting frame, region rights and loans. -/
theorem MemInstruction.evaluate_congr (op : MemInstruction) (target : ZielDaten) (c : Kontext)
    {s₁ s₂ : MemState} (locals : s₁.lokal = s₂.lokal)
    (rights : s₁.rechte = s₂.rechte) (loans : s₁.leihen = s₂.leihen) :
    op.evaluate target s₁ c = op.evaluate target s₂ c := by
  cases s₁
  cases s₂
  cases locals
  cases rights
  cases loans
  cases op <;> rfl

end Gabbro.Core.Ast.LowLevel
