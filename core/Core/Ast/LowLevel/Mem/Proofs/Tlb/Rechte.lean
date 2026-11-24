module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Lauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # A cached translation never grants more than the table, except inside a pending narrowing

`protect` narrows the table in one step but cannot clear the caches of the other cores: a core may keep
a translation with the old, wider rights. The invariant below says exactly how far that goes: every
cell grants at most what the table entry of its page grants, UNLESS a pending narrowing token (a
`protect` whose shootdown has not finished) covers its page. The completion step (`flush` of the
token) is enabled only when the first alternative holds again for the whole range. -/

/-- Some pending narrowing of the space covers the page. -/
def MemFrame.VerengtBei (frame : MemFrame) (raum seite : Nat) : Prop :=
  ∃ token ∈ frame.verengt, token.raum = raum ∧ token.contains seite

/-- **Rights of cached translations.** Every cell of every core grants at most what the table of its
    space grants (when the entry maps its frame), or its page is covered by a pending narrowing. -/
def MemFrame.TlbRechteGedeckt (frame : MemFrame) : Prop :=
  ∀ zelle ∈ frame.tlb.zellen, ∀ space, frame.spaces[zelle.raum]? = some space →
    zelle.RechteGedeckt space ∨ frame.VerengtBei zelle.raum zelle.seite

theorem MemFrame.VerengtBei.von_gleich {frame next : MemFrame} {raum seite : Nat}
    (same : next.verengt = frame.verengt) (h : frame.VerengtBei raum seite) :
    next.VerengtBei raum seite := by
  unfold MemFrame.VerengtBei at h ⊢
  rw [same]
  exact h

theorem TlbZelle.RechteGedeckt.abbildung_gleich {zelle : TlbZelle} {space space' : Adressraum}
    (same : space'.abbildung zelle.seite = space.abbildung zelle.seite)
    (h : zelle.RechteGedeckt space) : zelle.RechteGedeckt space' := by
  intro entry found frame right hr
  rw [same] at found
  exact h entry found frame right hr

theorem MemFrame.TlbRechteGedeckt.aus_gleich {frame next : MemFrame} (inv : frame.TlbRechteGedeckt)
    (tlb : next.tlb = frame.tlb) (spaces : next.spaces = frame.spaces)
    (verengt : next.verengt = frame.verengt) : next.TlbRechteGedeckt := by
  intro zelle mem space found
  rw [tlb] at mem
  rw [spaces] at found
  rcases inv zelle mem space found with ok | pending
  · exact Or.inl ok
  · exact Or.inr (pending.von_gleich verengt)

/-- A fresh frame (no cell) satisfies the invariant. -/
theorem MemFrame.TlbRechteGedeckt.leer {frame : MemFrame} (empty : frame.tlb.zellen = []) :
    frame.TlbRechteGedeckt := by
  intro zelle mem
  rw [empty] at mem
  cases mem

/-- Hardware or a handler drops cells at any time: a sub-cache keeps the invariant. -/
theorem MemFrame.TlbRechteGedeckt.verdraengt {frame next : MemFrame} (inv : frame.TlbRechteGedeckt)
    (subset : ∀ zelle ∈ next.tlb.zellen, zelle ∈ frame.tlb.zellen)
    (spaces : next.spaces = frame.spaces) (verengt : next.verengt = frame.verengt) :
    next.TlbRechteGedeckt := by
  intro zelle mem space found
  rw [spaces] at found
  rcases inv zelle (subset zelle mem) space found with ok | pending
  · exact Or.inl ok
  · exact Or.inr (pending.von_gleich verengt)

theorem MemFrame.TlbRechteGedeckt.bei_gleich {frame next : MemFrame} (inv : frame.TlbRechteGedeckt)
    (same : next.verengt = frame.verengt) {zelle : TlbZelle} (mem : zelle ∈ frame.tlb.zellen)
    {space : Adressraum} (found : frame.spaces[zelle.raum]? = some space) :
    zelle.RechteGedeckt space ∨ next.VerengtBei zelle.raum zelle.seite := by
  rcases inv zelle mem space found with ok | pending
  · exact Or.inl ok
  · exact Or.inr (pending.von_gleich same)

private theorem spaces_set_gleich {spaces : List Adressraum} {sp : Nat} {new space1 : Adressraum}
    {raum : Nat} (same : raum = sp) (lt : sp < spaces.length)
    (found : (spaces.set sp new)[raum]? = some space1) : space1 = new := by
  rw [same, List.getElem?_set_self lt] at found
  exact (Option.some.inj found).symm

private theorem spaces_set_fern {spaces : List Adressraum} {sp : Nat} {new space1 : Adressraum}
    {raum : Nat} (other : raum ≠ sp)
    (found : (spaces.set sp new)[raum]? = some space1) : spaces[raum]? = some space1 := by
  rw [List.getElem?_set_ne (Ne.symm other)] at found
  exact found

/-! ## A fill copies a present entry, so it grants exactly what the table grants -/

theorem tlbRechte_tlbFuellen (target : ZielDaten) (core sp page : Nat) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.tlbFuellen core sp page).evaluate target s c = some next)
    (inv : (s.lokal c).TlbRechteGedeckt) : next.TlbRechteGedeckt := by
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
      intro zelle mem space1 found
      change zelle ∈ (⟨core, sp, page, entry⟩ : TlbZelle) :: (s.lokal c).tlb.zellen at mem
      rcases List.mem_cons.mp mem with rfl | old
      · left
        have found' : (s.lokal c).spaces[sp]? = some space1 := found
        have unique : space1 = space := Option.some.inj (found'.symm.trans hs)
        subst unique
        intro entry' hf same right hr
        have hf' : space1.abbildung page = some entry' := hf
        have eq : entry = entry' := Option.some.inj (hm.symm.trans hf')
        subst eq
        exact hr
      · exact inv.bei_gleich rfl old found

/-! ## Narrowing: the cells keep their rights, the token records that the shootdown is pending -/

theorem tlbRechte_protectSpace (target : ZielDaten) (sp virt pages : Nat)
    (rights : List Speicherdienst) (s : MemState) (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.protectSpace sp virt pages rights).evaluate target s c = some next)
    (inv : (s.lokal c).TlbRechteGedeckt) : next.TlbRechteGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      intro zelle mem space1 found
      have lt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
      by_cases same : zelle.raum = sp
      · have narrowed : space1 = narrowRights space (virt / target.seitengranule) pages rights :=
          spaces_set_gleich same lt found
        by_cases inside : pageRange (virt / target.seitengranule) pages zelle.seite
        · exact Or.inr ⟨Zuruecknahme.verengung sp (virt / target.seitengranule) pages space.generation,
            List.mem_cons_self .., same.symm, inside⟩
        · have found0 : (s.lokal c).spaces[zelle.raum]? = some space := by
            rw [same]
            exact hs
          rcases inv zelle mem space found0 with ok | pending
          · refine Or.inl ?_
            subst narrowed
            exact ok.abbildung_gleich (abbildung_narrow_aussen space _ pages rights zelle.seite inside)
          · obtain ⟨t, tmem, traum, tcontains⟩ := pending
            exact Or.inr ⟨t, List.mem_cons_of_mem _ tmem, traum, tcontains⟩
      · have found0 : (s.lokal c).spaces[zelle.raum]? = some space1 := spaces_set_fern same found
        rcases inv zelle mem space1 found0 with ok | pending
        · exact Or.inl ok
        · obtain ⟨t, tmem, traum, tcontains⟩ := pending
          exact Or.inr ⟨t, List.mem_cons_of_mem _ tmem, traum, tcontains⟩
    · cases h

/-! ## Mapping adds entries on pages no cell can cache -/

theorem tlbRechte_mapSpace (target : ZielDaten) (sp virt slot : Nat)
    (rights : List Speicherdienst) (s : MemState) (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.mapSpace sp virt slot rights).evaluate target s c = some next)
    (cover : (s.lokal c).TlbGedeckt) (inv : (s.lokal c).TlbRechteGedeckt) :
    next.TlbRechteGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    cases hr : heldMemRegion target s c slot with
    | none => simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> cases h
    | some region =>
      simp only [hs, hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i cond
        obtain ⟨_, _, _, hnone, htokens⟩ := cond
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        intro zelle mem space1 found
        have mem' : zelle ∈ (s.lokal c).tlb.zellen := by
          first
            | exact mem
            | exact (List.mem_filter.mp mem).1
        have lt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
        by_cases same : zelle.raum = sp
        · have mapped := spaces_set_gleich same lt found
          have found0 : (s.lokal c).spaces[zelle.raum]? = some space := by
            rw [same]
            exact hs
          by_cases inside : pageRange (virt / target.seitengranule)
              ((region.extent.bis - region.extent.von) / target.seitengranule) zelle.seite
          · -- a cell on a page that is about to be mapped cannot exist: nothing covers it
            exfalso
            obtain ⟨space0, found1, covered⟩ := cover zelle mem'
            have unique : space0 = space := Option.some.inj (found1.symm.trans found0)
            subst unique
            have idx : zelle.seite - virt / target.seitengranule <
                (region.extent.bis - region.extent.von) / target.seitengranule := by
              unfold pageRange at inside
              omega
            have back : virt / target.seitengranule +
                (zelle.seite - virt / target.seitengranule) = zelle.seite := by
              unfold pageRange at inside
              omega
            rcases covered with ⟨entry, hentry, _⟩ | ⟨token, tmem, own⟩
            · have isNone := List.all_eq_true.mp hnone (zelle.seite - virt / target.seitengranule)
                (List.mem_range.mpr idx)
              rw [back, hentry] at isNone
              cases isNone
            · have outside := List.all_eq_true.mp (List.all_eq_true.mp htokens token tmem)
                (zelle.seite - virt / target.seitengranule) (List.mem_range.mpr idx)
              rw [back] at outside
              exact (of_decide_eq_true outside) own.1
          · rcases inv zelle mem' space found0 with ok | pending
            · refine Or.inl ?_
              subst mapped
              refine ok.abbildung_gleich ?_
              refine abbildung_append_fern _ _ zelle.seite ?_
              intro e he
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
              intro heq
              apply inside
              have hlt := List.mem_range.mp hi
              rw [← heq]
              exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hlt _⟩
            · exact Or.inr (pending.von_gleich rfl)
        · have found0 : (s.lokal c).spaces[zelle.raum]? = some space1 := spaces_set_fern same found
          exact inv.bei_gleich rfl mem' found0
      · cases h

/-! ## Unmapping removes entries: the cells of the range keep only the cover of the pending token -/

private theorem entries_filter_none (base pages pg : Nat) (hpg : pageRange base pages pg)
    (entries : List (Nat × Seiteneintrag)) :
    (entries.filter (fun (page, _) => !decide (pageRange base pages page))).find?
        (fun entry => entry.1 == pg) = none := by
  apply List.find?_eq_none.mpr
  rintro ⟨page, entry⟩ hmem
  have hnot := (List.mem_filter.mp hmem).2
  by_cases heq : page = pg
  · subst page
    change (!decide (pageRange base pages pg)) = true at hnot
    have hd : decide (pageRange base pages pg) = true := decide_eq_true hpg
    rw [hd] at hnot
    cases hnot
  · intro h
    exact heq (beq_iff_eq.mp h)

theorem tlbRechte_unmapSpace (target : ZielDaten) (sp virt pages : Nat) (s : MemState)
    (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.unmapSpace sp virt pages).evaluate target s c = some next)
    (inv : (s.lokal c).TlbRechteGedeckt) : next.TlbRechteGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some space =>
    cases hf : space.abbildung (virt / target.seitengranule) with
    | none => simp only [hs, hf, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> cases h
    | some first =>
      simp only [hs, hf, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        intro zelle mem space1 found
        have lt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
        by_cases same : zelle.raum = sp
        · have cleared := spaces_set_gleich same lt found
          have found0 : (s.lokal c).spaces[zelle.raum]? = some space := by
            rw [same]
            exact hs
          by_cases inside : pageRange (virt / target.seitengranule) pages zelle.seite
          · -- the entry of the page is gone: nothing is claimed about the cell's rights
            refine Or.inl ?_
            subst cleared
            intro entry hentry
            change ((space.entries.filter (fun (page, _) =>
              !decide (pageRange (virt / target.seitengranule) pages page))).find?
                (fun e => e.1 == zelle.seite)).map Prod.snd = some entry at hentry
            rw [entries_filter_none _ _ _ inside] at hentry
            cases hentry
          · rcases inv zelle mem space found0 with ok | pending
            · refine Or.inl ?_
              subst cleared
              refine ok.abbildung_gleich ?_
              refine abbildung_filter_fern space _ _ zelle.seite rfl ?_
              intro e he'
              obtain ⟨page, entry'⟩ := e
              simp only at he'
              subst he'
              simp only [decide_eq_false inside, Bool.not_false]
            · exact Or.inr (pending.von_gleich rfl)
        · have found0 : (s.lokal c).spaces[zelle.raum]? = some space1 := spaces_set_fern same found
          exact inv.bei_gleich rfl mem found0
      · cases h

/-! ## The step that ends a shootdown -/

theorem tlbRechte_flush (target : ZielDaten) (name : Identifier) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.flushSpace name).evaluate target s c = some next)
    (inv : (s.lokal c).TlbRechteGedeckt) : next.TlbRechteGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hm : (s.lokal c).marken.find? (fun p => p.1.val == name.val) with
  | none => simp only [hm, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some pair =>
    obtain ⟨nm, token⟩ := pair
    simp only [hm, Option.bind_eq_bind, Option.bind_some] at h
    cases hs : (s.lokal c).spaces[token.raum]? with
    | none => simp only [hs, Option.bind_none] at h <;> cases h
    | some space =>
      simp only [hs, Option.bind_some] at h
      by_cases hnr : token.nurRechte = true
      · -- completion of a narrowing: the token ends because no cell of its range is wider than the table
        simp only [hnr, ↓reduceIte] at h
        split at h
        · rename_i cond
          simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
          have nichtBreiter := TranslationCache.nichtBreiter_eq_true.mp cond.2
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          intro zelle mem space1 found
          change zelle ∈ (s.lokal c).tlb.zellen at mem
          have found0 : (s.lokal c).spaces[zelle.raum]? = some space1 := found
          rcases inv zelle mem space1 found0 with ok | ⟨t, tmem, traum, tcontains⟩
          · exact Or.inl ok
          · by_cases eq : t = token
            · subst eq
              have unique : space1 = space := by
                rw [← traum] at found0
                exact Option.some.inj (found0.symm.trans hs)
              subst unique
              refine Or.inl (nichtBreiter zelle mem ?_)
              simp only [TlbZelle.imBereich, decide_eq_true_eq]
              exact ⟨traum.symm, tcontains⟩
            · exact Or.inr ⟨t, List.mem_filter.mpr ⟨tmem, bne_iff_ne.mpr eq⟩, traum, tcontains⟩
        · cases h
      · have hnr' : token.nurRechte = false := by
          cases hb : token.nurRechte with
          | false => rfl
          | true => exact (hnr hb).elim
        simp only [hnr', Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          intro zelle mem space1 found
          change zelle ∈ (s.lokal c).tlb.zellen at mem
          have lt : token.raum < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
          by_cases same : zelle.raum = token.raum
          · have flushed := spaces_set_gleich same lt found
            have found0 : (s.lokal c).spaces[zelle.raum]? = some space := by
              rw [same]
              exact hs
            rcases inv zelle mem space found0 with ok | pending
            · refine Or.inl ?_
              subst flushed
              exact ok.abbildung_gleich rfl
            · exact Or.inr (pending.von_gleich rfl)
          · have found0 : (s.lokal c).spaces[zelle.raum]? = some space1 := spaces_set_fern same found
            exact inv.bei_gleich rfl mem found0
        · cases h

end Gabbro.Core.Ast.LowLevel
