module

public import Core.Ast.LowLevel.Mem.Obligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

def NewSpaceMeaningAussage : Prop :=
  ∀ target s c slot region, heldMemRegion target s c slot = some region →
    (region.extent.seiten target → ∃ next space,
      (MemInstruction.newSpace slot).evaluate target s c = some next ∧
      next.result = some (.space (s.lokal c).spaces.length) ∧
      next.spaces = (s.lokal c).spaces ++ [space] ∧ space.tabellen = region.extent ∧
      space.entries = [] ∧ space.generation = 0 ∧ space.ausstehend = [] ∧
      space.Wohlgeformt target) ∧
    (¬ region.extent.seiten target → (MemInstruction.newSpace slot).evaluate target s c = none)

def MapMeaningAussage : Prop :=
  ∀ target s c sp virt slot rights space region,
    (s.lokal c).spaces[sp]? = some space → heldMemRegion target s c slot = some region →
    let granule := target.seitengranule
    let base := virt / granule
    let pages := (region.extent.bis - region.extent.von) / granule
    (rights ≠ [] ∧ region.extent.seiten target ∧ validVirtualRange target virt pages ∧
        (∀ i < pages, space.abbildung (base + i) = none) ∧
        (∀ token ∈ space.ausstehend, ∀ i < pages, ¬ token.contains (base + i)) →
      ∃ next mapped, (MemInstruction.mapSpace sp virt slot rights).evaluate target s c = some next ∧
        next.spaces[sp]? = some mapped ∧ next.result = some .mapped ∧
        next.tlb = (s.lokal c).tlb ∧
        (∀ i < pages, mapped.abbildung (base + i) =
          some ⟨region.extent.von / granule + i, rights, space.generation⟩) ∧
        (∀ pg, ¬ pageRange base pages pg → mapped.abbildung pg = space.abbildung pg)) ∧
    ((∃ token ∈ space.ausstehend, ∃ i < pages, token.contains (base + i)) →
      (MemInstruction.mapSpace sp virt slot rights).evaluate target s c = none)

def ProtectMeaningAussage : Prop :=
  ∀ target s c sp virt pages rights space,
    (s.lokal c).spaces[sp]? = some space →
    let base := virt / target.seitengranule
    (rights ≠ [] ∧ validVirtualRange target virt pages ∧
      (∀ i < pages, ∃ entry, space.abbildung (base + i) = some entry ∧
        ∀ right ∈ rights, right ∈ entry.rights) →
      ∃ next narrowed, (MemInstruction.protectSpace sp virt pages rights).evaluate target s c = some next ∧
        next.spaces[sp]? = some narrowed ∧ next.result = some .«protected» ∧
        (∀ pg entry, pageRange base pages pg → space.abbildung pg = some entry →
          narrowed.abbildung pg = some { entry with rights }) ∧
        next.tlb.Frei sp base pages) ∧
    ((∃ i < pages, ∃ entry, space.abbildung (base + i) = some entry ∧
      ∃ right ∈ rights, right ∉ entry.rights) →
      (MemInstruction.protectSpace sp virt pages rights).evaluate target s c = none)

/-- Clearing a mapping retains the old translations and reserves the physical
    extent with a pending token. Reuse is refused in every address space. -/
def UnmapMeaningAussage : Prop :=
  ∀ target s c sp virt pages space first,
    (s.lokal c).spaces[sp]? = some space →
    let granule := target.seitengranule
    let base := virt / granule
    space.abbildung base = some first →
    validVirtualRange target virt pages →
    (∀ i < pages, (space.abbildung (base + i)).map Seiteneintrag.frame = some (first.frame + i)) →
    ∃ next cleared token,
      (MemInstruction.unmapSpace sp virt pages).evaluate target s c = some next ∧
      next.result = some (.pending token) ∧ next.spaces[sp]? = some cleared ∧
      token = ⟨sp, base, pages, space.generation + 1, first.frame⟩ ∧
      cleared.generation = token.generation ∧ cleared.ausstehend = token :: space.ausstehend ∧
      (∀ pg, pageRange base pages pg → cleared.abbildung pg = none) ∧
      (∀ pg, ¬ pageRange base pages pg → cleared.abbildung pg = space.abbildung pg) ∧
      next.tlb = (s.lokal c).tlb ∧
      ∀ extent, ¬ extent.getrennt (token.frames granule) → next.unreserved granule extent = false

/-- The release step of a shootdown. A matching token is consumed only after its table entries have
    been cleared AND no core caches a translation of its pages: the invalidation on the other cores is
    the work of their handlers, never a side effect of this step. A step that finds a cached
    translation of the range is refused, so the frames of a stale translation stay reserved. -/
def FlushMeaningAussage : Prop :=
  ∀ target s c name token space,
    ((s.lokal c).marken.find? (fun p => p.1.val == name.val)).map Prod.snd = some token →
    (s.lokal c).spaces[token.raum]? = some space →
    (token ∈ space.ausstehend ∧ (∀ i < token.seiten, space.abbildung (token.seite + i) = none) ∧
        (s.lokal c).tlb.Frei token.raum token.seite token.seiten →
      ∃ next flushed, (MemInstruction.flushSpace name).evaluate target s c = some next ∧
        next.result = some (.frames (token.frames target.seitengranule)) ∧
        next.spaces[token.raum]? = some flushed ∧ flushed.entries = space.entries ∧
        token ∉ flushed.ausstehend ∧
        (∀ bound ∈ next.marken, bound.2 ≠ token) ∧
        next.tlb = (s.lokal c).tlb) ∧
    ((token ∉ space.ausstehend ∨ (∃ pg, token.contains pg ∧ (space.abbildung pg).isSome) ∨
        ¬ (s.lokal c).tlb.Frei token.raum token.seite token.seiten) →
      (MemInstruction.flushSpace name).evaluate target s c = none)

def ActivateMeaningAussage : Prop :=
  ∀ target s c sp,
    ((s.lokal c).spaces[sp]? = none → (MemInstruction.activateSpace sp).evaluate target s c = none) ∧
    ∀ space, (s.lokal c).spaces[sp]? = some space →
      (space.Aktivierbar target s c →
        (MemInstruction.activateSpace sp).evaluate target s c =
          some { s.lokal c with active := some sp, result := some .activated }) ∧
      (¬ space.Aktivierbar target s c → (MemInstruction.activateSpace sp).evaluate target s c = none)

theorem activate_meaning : ActivateMeaningAussage := by
  intro target s c sp
  constructor
  · intro missing
    simp only [MemInstruction.evaluate, missing, Option.bind_eq_bind, Option.bind_none]
  · intro space found
    constructor
    · intro valid
      simp only [MemInstruction.evaluate, found, Option.bind_eq_bind, Option.bind_some, if_pos valid, Option.pure_def]
    · intro invalid
      simp only [MemInstruction.evaluate, found, Option.bind_eq_bind, Option.bind_some, if_neg invalid]

end Gabbro.Core.Ast.LowLevel
