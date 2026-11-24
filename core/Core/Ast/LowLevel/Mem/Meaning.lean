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

def TranslationCache.invalidate (cache : TranslationCache) (space base pages : Nat) : TranslationCache :=
  fun core sp index =>
    if sp = space ∧ pageRange base pages index then none else cache core sp index

theorem TranslationCache.invalidate_hit (cache : TranslationCache)
    (space base pages core index : Nat) (covered : pageRange base pages index) :
    cache.invalidate space base pages core space index = none :=
  if_pos ⟨rfl, covered⟩

theorem TranslationCache.invalidate_miss (cache : TranslationCache)
    (space base pages core actual index : Nat)
    (outside : actual ≠ space ∨ ¬ pageRange base pages index) :
    cache.invalidate space base pages core actual index = cache core actual index :=
  if_neg fun inside => outside.elim (fun other => other inside.1) (fun uncovered => uncovered inside.2)

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
        spaces := frame.spaces.set sp { space with entries := space.entries ++ entries },
        tlb := frame.tlb.invalidate sp base pages }
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
    if token ∈ space.ausstehend &&
        ((List.range token.seiten).all fun i => (space.abbildung (token.seite + i)).isNone) then
      pure { frame with
        result := some (.frames (token.frames granule))
        tlb := frame.tlb.invalidate token.raum token.seite token.seiten,
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
