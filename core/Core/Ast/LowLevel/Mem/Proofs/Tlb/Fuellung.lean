module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Lauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # No refill inside a pending token's range

This is the memory machine's instance of the `keineFuellung` cache law that
`FlushProtokoll.frei_bei_freigabe` (core/Core/Verfeinerung/Abnahme/Flush.lean) takes as a premise:
once `unmap` has opened a pending token, no step creates a cached translation of a page of that range.
The only cell-creating instruction is `tlbFuellen`, and it needs an active table entry of the page;
`unmap` cleared exactly those entries and `map` refuses any range that still overlaps a pending token. -/

/-- No active entry of a space lies in the range of one of its pending tokens. This is the
    refill-relevant part of `Adressraum.Wohlgeformt`, isolated for the cache law. -/
def Adressraum.FreiAusstehend (space : Adressraum) : Prop :=
  ∀ entry ∈ space.entries, ∀ token ∈ space.ausstehend, ¬ token.contains entry.1

/-- A page covered by a pending token has no active table entry. -/
theorem Adressraum.abbildung_none_im_ausstehend {space : Adressraum}
    (wf : space.FreiAusstehend) {token : Zuruecknahme}
    (tmem : token ∈ space.ausstehend) {page : Nat} (inside : token.contains page) :
    space.abbildung page = none := by
  unfold Adressraum.abbildung
  cases hfind : space.entries.find? (fun e => e.1 == page) with
  | none => simp only [Option.map_none]
  | some pair =>
      exfalso
      have hpMem : pair ∈ space.entries := List.mem_of_find?_eq_some hfind
      have hpEq : pair.1 = page := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hfind).1
      have hno := wf pair hpMem token tmem
      rw [hpEq] at hno
      exact hno inside

/-- Clearing a range and reserving it with a token leaves no entry in any pending token's range.
    This is what `unmap` contributes to the law: the entries of the range are gone from the send on. -/
theorem Adressraum.unmapFreiAusstehend (space : Adressraum) (sp base pages first : Nat)
    (wf : space.FreiAusstehend) :
    ({ space with
        entries := space.entries.filter (fun (pg, _) => !decide (pageRange base pages pg)),
        generation := space.generation + 1,
        ausstehend := ⟨sp, base, pages, space.generation + 1, first, false⟩ :: space.ausstehend }
      : Adressraum).FreiAusstehend := by
  intro entry hentry token' htmem
  have hentryOld : entry ∈ space.entries := (List.mem_filter.mp hentry).1
  have hq : (!decide (pageRange base pages entry.1)) = true := (List.mem_filter.mp hentry).2
  rcases List.mem_cons.mp htmem with htok | hold
  · subst token'
    have hdec : decide (pageRange base pages entry.1) = false := by
      simpa only [Bool.not_eq_true'] using hq
    exact decide_eq_false_iff_not.mp hdec
  · exact wf entry hentryOld token' hold

/-- The `mapSpace` guard makes every new entry lie outside every pending token's range. This is what
    `map` contributes: it cannot recreate an entry of a revoked page while the token is outstanding. -/
theorem mapSpace_neue_eintraege_fern (space : Adressraum) (base pages : Nat)
    (hall : space.ausstehend.all (fun token =>
      (List.range pages).all (fun i => decide (¬ token.contains (base + i)))) = true)
    (rights : List Speicherdienst) (von gen : Nat) :
    ∀ token ∈ space.ausstehend,
      ∀ e ∈ (List.range pages).map (fun i => (base + i, (⟨von + i, rights, gen⟩ : Seiteneintrag))),
        ¬ token.contains e.1 := by
  intro token' htmem e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have h1 := List.all_eq_true.mp hall token' htmem
  have h2 := List.all_eq_true.mp h1 i hi
  simpa only [decide_eq_true_eq] using h2

/-- Appending entries that are outside every pending range preserves the invariant. -/
theorem Adressraum.mapFreiAusstehend (space : Adressraum) (new : List (Nat × Seiteneintrag))
    (wf : space.FreiAusstehend)
    (fern : ∀ token ∈ space.ausstehend, ∀ e ∈ new, ¬ token.contains e.1) :
    ({ space with entries := space.entries ++ new } : Adressraum).FreiAusstehend := by
  intro entry hentry token' htmem
  rcases List.mem_append.mp hentry with hold | hnew
  · exact wf entry hold token' htmem
  · exact fern token' htmem entry hnew

/-- A fill of a page covered by a pending token is refused: the token owns the page, so no entry of
    that page is present to copy. -/
theorem tlbFuellen_verweigert_ausstehend (target : ZielDaten) (core sp page : Nat)
    (s : MemState) (c : Kontext) {space : Adressraum} {token : Zuruecknahme}
    (found : (s.lokal c).spaces[sp]? = some space) (tmem : token ∈ space.ausstehend)
    (wf : space.FreiAusstehend) (inside : token.contains page) :
    (MemInstruction.tlbFuellen core sp page).evaluate target s c = none := by
  have hnone := space.abbildung_none_im_ausstehend wf tmem inside
  simp only [MemInstruction.evaluate, found, hnone, Option.bind_eq_bind, Option.bind_some,
    Option.bind_none]

/-- Every instruction other than `tlbFuellen` keeps the cache or drops cells from it, so it cannot
    introduce a cell that was not already cached. -/
private theorem tlb_subset_ohne_fuellen (target : ZielDaten) (op : MemInstruction) (s : MemState)
    (c : Kontext) {next : MemFrame} (step : op.evaluate target s c = some next)
    (keinFuellen : ∀ core sp page, op ≠ .tlbFuellen core sp page) :
    ∀ zelle ∈ next.tlb.zellen, zelle ∈ (s.lokal c).tlb.zellen := by
  cases op with
  | tlbFuellen core sp page => exact (keinFuellen core sp page rfl).elim
  | splitRegion slot point =>
      have keep := erhaelt_splitRegion target slot point s c next step
      intro zelle hz
      rw [keep.1] at hz
      exact hz
  | splitPages slot pages =>
      have keep := erhaelt_splitPages target slot pages s c next step
      intro zelle hz
      rw [keep.1] at hz
      exact hz
  | mergeRegions first second =>
      have keep := erhaelt_mergeRegions target first second s c next step
      intro zelle hz
      rw [keep.1] at hz
      exact hz
  | newSpace tables =>
      simp only [MemInstruction.evaluate] at step
      cases hr : heldMemRegion target s c tables with
      | none => simp only [hr, Option.bind_eq_bind, Option.bind_none] at step <;> cases step
      | some region =>
          simp only [hr, Option.bind_eq_bind, Option.bind_some] at step
          split at step
          · simp only [Option.pure_def, Option.some.injEq] at step
            subst next
            intro zelle hz
            exact hz
          · cases step
  | mapSpace sp virt slot rights =>
      simp only [MemInstruction.evaluate] at step
      cases hs : (s.lokal c).spaces[sp]? with
      | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at step <;> cases step
      | some space =>
          cases hr : heldMemRegion target s c slot with
          | none => simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at step <;> cases step
          | some region =>
              simp only [hs, hr, Option.bind_eq_bind, Option.bind_some] at step
              split at step
              · simp only [Option.pure_def, Option.some.injEq] at step
                subst next
                intro zelle hz
                exact (List.mem_filter.mp hz).1
              · cases step
  | protectSpace sp virt pages rights =>
      simp only [MemInstruction.evaluate] at step
      cases hs : (s.lokal c).spaces[sp]? with
      | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at step <;> cases step
      | some space =>
          simp only [hs, Option.bind_eq_bind, Option.bind_some] at step
          split at step
          · simp only [Option.pure_def, Option.some.injEq] at step
            subst next
            intro zelle hz
            exact hz
          · cases step
  | unmapSpace sp virt pages =>
      simp only [MemInstruction.evaluate] at step
      cases hs : (s.lokal c).spaces[sp]? with
      | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at step <;> cases step
      | some space =>
          cases hf : space.abbildung (virt / target.seitengranule) with
          | none => simp only [hs, hf, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at step <;> cases step
          | some first =>
              simp only [hs, hf, Option.bind_eq_bind, Option.bind_some] at step
              split at step
              · simp only [Option.pure_def, Option.some.injEq] at step
                subst next
                intro zelle hz
                exact hz
              · cases step
  | flushSpace name =>
      simp only [MemInstruction.evaluate] at step
      cases hm : (s.lokal c).marken.find? (fun p => p.1.val == name.val) with
      | none => simp only [hm, Option.bind_eq_bind, Option.bind_none] at step <;> cases step
      | some pair =>
          obtain ⟨nm, token⟩ := pair
          simp only [hm, Option.bind_eq_bind, Option.bind_some] at step
          cases hs : (s.lokal c).spaces[token.raum]? with
          | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at step <;> cases step
          | some space =>
              simp only [hs, Option.bind_eq_bind, Option.bind_some] at step
              by_cases hnr : token.nurRechte = true
              · simp only [hnr, ↓reduceIte] at step
                split at step
                · simp only [Option.pure_def, Option.some.injEq] at step
                  subst next
                  intro zelle hz
                  exact hz
                · cases step
              · have hnr' : token.nurRechte = false := by
                  cases hb : token.nurRechte with
                  | false => rfl
                  | true => exact (hnr hb).elim
                simp only [hnr', Bool.false_eq_true, ↓reduceIte] at step
                split at step
                · simp only [Option.pure_def, Option.some.injEq] at step
                  subst next
                  intro zelle hz
                  exact hz
                · cases step
  | tlbVerdraengen core sp page =>
      simp only [MemInstruction.evaluate, Option.some.injEq] at step
      subst next
      intro zelle hz
      exact (List.mem_filter.mp hz).1
  | activateSpace sp =>
      have keep := erhaelt_activateSpace target sp s c next step
      intro zelle hz
      rw [keep.1] at hz
      exact hz
  | bindToken name =>
      have keep := erhaelt_bindToken target name s c next step
      intro zelle hz
      rw [keep.1] at hz
      exact hz

/-- **The memory machine's `keineFuellung` law.** While a token is pending, every cell of its range
    that is cached after one more step was already cached before the step. No step can newly create a
    translation of a revoked page: the sole cell-creating step, `tlbFuellen`, needs a table entry that
    `unmap` removed and `map` is forbidden to recreate. This is the premise of
    `FlushProtokoll.frei_bei_freigabe` for the memory machine. -/
theorem keineFuellung_speicher (target : ZielDaten) (op : MemInstruction) (s : MemState) (c : Kontext)
    {next : MemFrame} (step : op.evaluate target s c = some next)
    {token : Zuruecknahme} {space : Adressraum}
    (found : (s.lokal c).spaces[token.raum]? = some space)
    (tmem : token ∈ space.ausstehend) (wf : space.FreiAusstehend) :
    ∀ zelle, zelle.raum = token.raum → token.contains zelle.seite →
      zelle ∈ next.tlb.zellen → zelle ∈ (s.lokal c).tlb.zellen := by
  have rest : (∀ core sp page, op ≠ .tlbFuellen core sp page) →
      ∀ zelle, zelle.raum = token.raum → token.contains zelle.seite →
        zelle ∈ next.tlb.zellen → zelle ∈ (s.lokal c).tlb.zellen := by
    intro hne zelle _ _ hz
    exact tlb_subset_ohne_fuellen target op s c step hne zelle hz
  cases op with
  | tlbFuellen core sp page =>
      simp only [MemInstruction.evaluate] at step
      cases hs : (s.lokal c).spaces[sp]? with
      | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at step <;> cases step
      | some spaceF =>
          simp only [hs, Option.bind_eq_bind, Option.bind_some] at step
          cases hm : spaceF.abbildung page with
          | none => simp only [hm, Option.bind_none] at step <;> cases step
          | some entry =>
              simp only [hm, Option.bind_some, Option.pure_def, Option.some.injEq] at step
              subst next
              intro zelle hzraum hzpage hzmem
              change zelle ∈ (⟨core, sp, page, entry⟩ : TlbZelle) :: (s.lokal c).tlb.zellen at hzmem
              rcases List.mem_cons.mp hzmem with hznew | hzold
              · exfalso
                subst hznew
                by_cases same : sp = token.raum
                · have hs' : (s.lokal c).spaces[token.raum]? = some spaceF := by
                    rw [← same]
                    exact hs
                  have spcEq : spaceF = space := Option.some.inj (hs'.symm.trans found)
                  rw [spcEq] at hm
                  have hnone := space.abbildung_none_im_ausstehend wf tmem hzpage
                  rw [hnone] at hm
                  cases hm
                · exact same hzraum
              · exact hzold
  | splitRegion slot point => exact rest (by intro a b d e; cases e)
  | splitPages slot pages => exact rest (by intro a b d e; cases e)
  | mergeRegions first second => exact rest (by intro a b d e; cases e)
  | newSpace tables => exact rest (by intro a b d e; cases e)
  | mapSpace space virt frames rights =>
      exact rest (by intro a b d e; cases e)
  | protectSpace space virt pages rights =>
      exact rest (by intro a b d e; cases e)
  | unmapSpace space virt pages => exact rest (by intro a b d e; cases e)
  | flushSpace name => exact rest (by intro a b d e; cases e)
  | activateSpace space => exact rest (by intro a b d e; cases e)
  | tlbVerdraengen core sp page => exact rest (by intro a b d e; cases e)
  | bindToken name => exact rest (by intro a b d e; cases e)

end Gabbro.Core.Ast.LowLevel
