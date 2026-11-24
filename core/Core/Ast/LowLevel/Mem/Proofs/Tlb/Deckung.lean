module

public import Core.Ast.LowLevel.Mem.Execution

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # Cached translations stay covered by reserved frames

A translation a core caches may outlive the table entry it was copied from: `unmap` clears the entry
and keeps the frames reserved under a pending token, and only the release step of `flush` returns
them, after no core caches a translation of the range. The invariant below states exactly this: every
cached cell is explained by an active table entry of its space or by a pending token of its space.
Hardware may fill a cell from a present entry and drop any cell at any time; both keep the invariant. -/

/-- The pending token owns the frame of `page`: its range contains the page and the frame is the
    frame the unmapped extent had at that page. -/
def Zuruecknahme.deckt (token : Zuruecknahme) (page frame : Nat) : Prop :=
  token.contains page ∧ frame = token.frameBasis + (page - token.seite)

/-- A frame that a cache cell of `page` may point to: the frame of the active table entry, or the
    frame a pending token still owns. -/
def Adressraum.deckt (space : Adressraum) (page frame : Nat) : Prop :=
  (∃ entry, space.abbildung page = some entry ∧ entry.frame = frame) ∨
    ∃ token ∈ space.ausstehend, token.deckt page frame

/-- Every cell of the translation cache of every core is covered in its space. -/
def MemFrame.TlbGedeckt (frame : MemFrame) : Prop :=
  ∀ zelle ∈ frame.tlb.zellen, ∃ space, frame.spaces[zelle.raum]? = some space ∧
    space.deckt zelle.seite zelle.eintrag.frame

theorem MemFrame.TlbGedeckt.aus_gleich {frame next : MemFrame} (inv : frame.TlbGedeckt)
    (tlb : next.tlb = frame.tlb) (spaces : next.spaces = frame.spaces) : next.TlbGedeckt := by
  intro zelle mem
  rw [tlb] at mem
  obtain ⟨space, found, covered⟩ := inv zelle mem
  exact ⟨space, by rw [spaces]; exact found, covered⟩

/-- The frames of a fresh frame (no cell) are covered. -/
theorem MemFrame.TlbGedeckt.leer {frame : MemFrame} (empty : frame.tlb.zellen = []) :
    frame.TlbGedeckt := by
  intro zelle mem
  rw [empty] at mem
  cases mem

/-- Hardware drops cells on its own: a sub-cache of a covered cache is covered. -/
theorem MemFrame.TlbGedeckt.verdraengt {frame next : MemFrame} (inv : frame.TlbGedeckt)
    (subset : ∀ zelle ∈ next.tlb.zellen, zelle ∈ frame.tlb.zellen)
    (spaces : next.spaces = frame.spaces) : next.TlbGedeckt := by
  intro zelle mem
  obtain ⟨space, found, covered⟩ := inv zelle (subset zelle mem)
  exact ⟨space, by rw [spaces]; exact found, covered⟩

theorem Adressraum.deckt_mit {space space' : Adressraum} {page frame : Nat}
    (tabelle : ∀ entry, space.abbildung page = some entry →
      ∃ entry', space'.abbildung page = some entry' ∧ entry'.frame = entry.frame)
    (marken : ∀ token ∈ space.ausstehend, token.deckt page frame →
      ∃ token' ∈ space'.ausstehend, token'.deckt page frame)
    (covered : space.deckt page frame) : space'.deckt page frame := by
  rcases covered with ⟨entry, found, same⟩ | ⟨token, mem, own⟩
  · obtain ⟨entry', found', same'⟩ := tabelle entry found
    exact Or.inl ⟨entry', found', same'.trans same⟩
  · obtain ⟨token', mem', own'⟩ := marken token mem own
    exact Or.inr ⟨token', mem', own'⟩

/-- Cells of a space other than the one an instruction changes keep their cover. -/
theorem MemFrame.TlbGedeckt.set_fern {frame : MemFrame} {zelle : TlbZelle} {sp : Nat}
    {new space : Adressraum} (other : zelle.raum ≠ sp)
    (found : frame.spaces[zelle.raum]? = some space) :
    (frame.spaces.set sp new)[zelle.raum]? = some space := by
  rw [List.getElem?_set_ne (Ne.symm other)]
  exact found

/-- A cell of a page range can only be covered by a present table entry of its space or by a pending
    token of that space. If the range has neither, `TlbGedeckt` leaves no cell to clear there. -/
theorem MemFrame.TlbGedeckt.keine_Zelle {frame : MemFrame} (inv : frame.TlbGedeckt)
    {sp base pages : Nat} {space : Adressraum} (found : frame.spaces[sp]? = some space)
    (habb : ∀ i < pages, space.abbildung (base + i) = none)
    (htok : ∀ token ∈ space.ausstehend, ∀ i < pages, ¬ token.contains (base + i)) :
    ∀ zelle ∈ frame.tlb.zellen, zelle.imBereich sp base pages = false := by
  intro zelle mem
  cases him : zelle.imBereich sp base pages with
  | false => rfl
  | true =>
      have drin : zelle.raum = sp ∧ pageRange base pages zelle.seite := by
        simpa only [TlbZelle.imBereich, decide_eq_true_eq] using him
      have idxlt : zelle.seite - base < pages := by
        unfold pageRange at drin
        omega
      have zurueck : base + (zelle.seite - base) = zelle.seite := by
        unfold pageRange at drin
        omega
      obtain ⟨space0, found0, covered0⟩ := inv zelle mem
      have unique : space0 = space := by
        rw [drin.1] at found0
        exact Option.some.inj (found0.symm.trans found)
      rw [unique] at covered0
      rcases covered0 with ⟨entry, he, _⟩ | ⟨token, tmem, own⟩
      · have hnone := habb (zelle.seite - base) idxlt
        rw [zurueck, he] at hnone
        cases hnone
      · have hcont := htok token tmem (zelle.seite - base) idxlt
        rw [zurueck] at hcont
        exact (hcont own.1).elim

/-- Clearing a page range that has no cell is the identity. `map` adds entries only to a range with
    neither a table entry nor a pending token, so on every state `tlbGedeckt_erreichbar` covers, its
    former clearing of that range changed nothing. -/
theorem TranslationCache.invalidate_eq_self (cache : TranslationCache) (space base pages : Nat)
    (h : ∀ zelle ∈ cache.zellen, zelle.imBereich space base pages = false) :
    cache.invalidate space base pages = cache := by
  cases cache with
  | mk zellen =>
      unfold TranslationCache.invalidate
      apply congrArg TranslationCache.mk
      apply List.filter_eq_self.mpr
      intro zelle hz
      rw [h zelle hz]
      rfl

/-! ## Instructions that touch neither the spaces nor the cache -/

private theorem bindMarke_erhaelt {frame next : MemFrame} {name : Identifier} {token : Zuruecknahme}
    (h : frame.bindMarke name token = some next) :
    next.tlb = frame.tlb ∧ next.spaces = frame.spaces ∧ next.verengt = frame.verengt := by
  unfold MemFrame.bindMarke at h
  cases hs : frame.spaces[token.raum]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · exact ⟨by rw [← Option.some.inj h], by rw [← Option.some.inj h], by rw [← Option.some.inj h]⟩
    · cases h

theorem tlbGedeckt_tlbFuellen (target : ZielDaten) (core sp page : Nat) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.tlbFuellen core sp page).evaluate target s c = some next)
    (inv : (s.lokal c).TlbGedeckt) : next.TlbGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    cases hm : space.abbildung page with
    | none => simp only [hm, Option.bind_none] at h <;> cases h
    | some entry =>
      simp only [hm, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h
      intro zelle mem
      change zelle ∈ (⟨core, sp, page, entry⟩ : TlbZelle) :: (s.lokal c).tlb.zellen at mem
      rcases List.mem_cons.mp mem with rfl | old
      · exact ⟨space, hs, Or.inl ⟨entry, hm, rfl⟩⟩
      · exact inv zelle old

theorem tlbGedeckt_newSpace (target : ZielDaten) (tables : Nat) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.newSpace tables).evaluate target s c = some next)
    (inv : (s.lokal c).TlbGedeckt) : next.TlbGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hr : heldMemRegion target s c tables with
  | none => simp only [hr, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some region =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      intro zelle mem
      obtain ⟨space, found, covered⟩ := inv zelle mem
      have lt : zelle.raum < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp found).1
      refine ⟨space, ?_, covered⟩
      change ((s.lokal c).spaces ++ _)[zelle.raum]? = some space
      rw [List.getElem?_append_left lt]
      exact found
    · cases h

theorem tlbGedeckt_ohne_raeume (target : ZielDaten) (op : MemInstruction) (s : MemState)
    (c : Kontext) {next : MemFrame}
    (keine : ∀ frame : MemFrame, op.evaluate target s c = some frame →
      frame.tlb = (s.lokal c).tlb ∧ frame.spaces = (s.lokal c).spaces ∧
        frame.verengt = (s.lokal c).verengt)
    (h : op.evaluate target s c = some next) (inv : (s.lokal c).TlbGedeckt) :
    next.TlbGedeckt :=
  inv.aus_gleich (keine next h).1 (keine next h).2.1

theorem erhaelt_splitRegion (target : ZielDaten) (slot point : Nat) (s : MemState) (c : Kontext) :
    ∀ frame : MemFrame, (MemInstruction.splitRegion slot point).evaluate target s c = some frame →
      frame.tlb = (s.lokal c).tlb ∧ frame.spaces = (s.lokal c).spaces ∧
        frame.verengt = (s.lokal c).verengt := by
  intro frame h
  simp only [MemInstruction.evaluate] at h
  cases hr : heldMemRegion target s c slot with
  | none => simp only [hr, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some region =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
    · cases h

theorem erhaelt_splitPages (target : ZielDaten) (slot pages : Nat) (s : MemState) (c : Kontext) :
    ∀ frame : MemFrame, (MemInstruction.splitPages slot pages).evaluate target s c = some frame →
      frame.tlb = (s.lokal c).tlb ∧ frame.spaces = (s.lokal c).spaces ∧
        frame.verengt = (s.lokal c).verengt := by
  intro frame h
  simp only [MemInstruction.evaluate] at h
  cases hr : heldMemRegion target s c slot with
  | none => simp only [hr, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some region =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
    · cases h

theorem erhaelt_mergeRegions (target : ZielDaten) (first second : Nat) (s : MemState)
    (c : Kontext) :
    ∀ frame : MemFrame, (MemInstruction.mergeRegions first second).evaluate target s c = some frame →
      frame.tlb = (s.lokal c).tlb ∧ frame.spaces = (s.lokal c).spaces ∧
        frame.verengt = (s.lokal c).verengt := by
  intro frame h
  simp only [MemInstruction.evaluate] at h
  cases hl : heldMemRegion target s c first with
  | none => simp only [hl, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some left =>
    cases hr : heldMemRegion target s c second with
    | none => simp only [hl, hr, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> cases h
    | some right =>
      simp only [hl, hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩
      · cases h

theorem erhaelt_activateSpace (target : ZielDaten) (sp : Nat) (s : MemState) (c : Kontext) :
    ∀ frame : MemFrame, (MemInstruction.activateSpace sp).evaluate target s c = some frame →
      frame.tlb = (s.lokal c).tlb ∧ frame.spaces = (s.lokal c).spaces ∧
        frame.verengt = (s.lokal c).verengt := by
  intro frame h
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
    · cases h

theorem erhaelt_bindToken (target : ZielDaten) (name : Identifier) (s : MemState) (c : Kontext) :
    ∀ frame : MemFrame, (MemInstruction.bindToken name).evaluate target s c = some frame →
      frame.tlb = (s.lokal c).tlb ∧ frame.spaces = (s.lokal c).spaces ∧
        frame.verengt = (s.lokal c).verengt := by
  intro frame h
  simp only [MemInstruction.evaluate] at h
  cases hres : (s.lokal c).result with
  | none => simp only [hres] at h <;> cases h
  | some result =>
    cases result with
    | pending token => simp only [hres] at h; exact bindMarke_erhaelt h
    | partition _ _ => simp only [hres] at h <;> cases h
    | merged _ => simp only [hres] at h <;> cases h
    | space _ => simp only [hres] at h <;> cases h
    | mapped => simp only [hres] at h <;> cases h
    | «protected» => simp only [hres] at h <;> cases h
    | frames _ => simp only [hres] at h <;> cases h
    | activated => simp only [hres] at h <;> cases h

end Gabbro.Core.Ast.LowLevel
