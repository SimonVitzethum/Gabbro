module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.RechteLauf
public import Core.Ast.LowLevel.Mem.Proofs.Flush.Flush

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # Why `protect` is staged, and what the stages give

The old `protect` narrowed the table and, in the same step, cleared the translation caches of every
core. No step of one core can do that to another core: the caches of the other cores are the work of
their handlers. A `protect` without staging narrows the table and leaves the caches alone, and then the
invariant breaks (`protect_ohne_stufung_unsicher`): another core may still write through a cached
translation that the table no longer grants. The staged `protect` records the narrowing in a token
(`verengt`), and the invariant `TlbRechteGedeckt` says that a cell is wider than the table ONLY while
such a token covers its page. The completion step (`flush` of the token) refuses while any cell of the
range is wider (`flush_abschluss_nicht_breiter`); afterwards the guarantee of the narrowing holds for
every cell of the range. -/

/-- The step a `protect` would be without staging: narrow the table, touch no cache, record nothing. -/
def MemFrame.protectOhneStufung (frame : MemFrame) (sp base pages : Nat)
    (rights : List Speicherdienst) (space : Adressraum) : MemFrame :=
  { frame with spaces := frame.spaces.set sp (narrowRights space base pages rights) }

/-- **The invariant breaks without staging.** If any core caches a translation of a page of the range
    that carries a right the narrowed table no longer grants, and no narrowing is pending for the page,
    the unstaged step leaves a cell wider than the table: that core can still use the right. -/
theorem protect_ohne_stufung_unsicher {frame : MemFrame} {sp base pages : Nat}
    {rights : List Speicherdienst} {space : Adressraum} {zelle : TlbZelle} {entry : Seiteneintrag}
    (found : frame.spaces[sp]? = some space) (mem : zelle ∈ frame.tlb.zellen)
    (raum : zelle.raum = sp) (inside : pageRange base pages zelle.seite)
    (table : space.abbildung zelle.seite = some entry) (same : entry.frame = zelle.eintrag.frame)
    (wider : ∃ right ∈ zelle.eintrag.rights, right ∉ rights)
    (nothing : ¬ frame.VerengtBei sp zelle.seite) :
    ¬ (frame.protectOhneStufung sp base pages rights space).TlbRechteGedeckt := by
  intro bad
  have lt : sp < frame.spaces.length := (List.getElem?_eq_some_iff.mp found).1
  have found' : (frame.protectOhneStufung sp base pages rights space).spaces[zelle.raum]? =
      some (narrowRights space base pages rights) := by
    change (frame.spaces.set sp (narrowRights space base pages rights))[zelle.raum]? = _
    rw [raum]
    exact List.getElem?_set_self lt
  rcases bad zelle mem _ found' with ok | ⟨t, tmem, traum, tcontains⟩
  · obtain ⟨right, hr, hnot⟩ := wider
    have narrowed : (narrowRights space base pages rights).abbildung zelle.seite =
        some { entry with rights } := by
      rw [abbildung_narrow space base pages rights zelle.seite inside, table]
      rfl
    exact hnot (ok { entry with rights } narrowed same right hr)
  · exact nothing ⟨t, tmem, by rw [← raum]; exact traum, tcontains⟩

/-- Outside every pending narrowing, a cell grants at most the table. -/
theorem MemFrame.TlbRechteGedeckt.ohne_verengung {frame : MemFrame} (inv : frame.TlbRechteGedeckt)
    {zelle : TlbZelle} (mem : zelle ∈ frame.tlb.zellen) {space : Adressraum}
    (found : frame.spaces[zelle.raum]? = some space)
    (nothing : ¬ frame.VerengtBei zelle.raum zelle.seite) : zelle.RechteGedeckt space := by
  rcases inv zelle mem space found with ok | pending
  · exact ok
  · exact (nothing pending).elim

/-- **A completed narrowing leaves no wider cell.** The completion step of a narrowing token succeeds
    only when no cell of its range is wider than the table, changes neither the table nor any cache, and
    ends the token. -/
theorem flush_abschluss_nicht_breiter (target : ZielDaten) (name : Identifier) (s : MemState)
    (c : Kontext) (token : Zuruecknahme) (space : Adressraum) {next : MemFrame}
    (hfind : ((s.lokal c).marken.find? (fun p => p.1.val == name.val)).map Prod.snd = some token)
    (hspace : (s.lokal c).spaces[token.raum]? = some space) (hnr : token.nurRechte = true)
    (h : (MemInstruction.flushSpace name).evaluate target s c = some next) :
    token ∈ (s.lokal c).verengt ∧ token ∉ next.verengt ∧
      (s.lokal c).tlb.NichtBreiter space token.raum token.seite token.seiten ∧
      next.tlb = (s.lokal c).tlb ∧ next.spaces = (s.lokal c).spaces ∧
      next.result = some .«protected» := by
  have meaning := (flush_aussage.2.1 target s c name token space hfind hspace).2 hnr
  by_cases guard : token ∈ (s.lokal c).verengt ∧
      (s.lokal c).tlb.NichtBreiter space token.raum token.seite token.seiten
  · obtain ⟨next', hnext', hres, hspaces, htlb, hgone, _⟩ := meaning.1 guard
    have eq : next = next' := Option.some.inj (h.symm.trans hnext')
    subst eq
    exact ⟨guard.1, hgone, guard.2, htlb, hspaces, hres⟩
  · have refused := meaning.2 (by
      by_cases mem : token ∈ (s.lokal c).verengt
      · exact Or.inr fun nb => guard ⟨mem, nb⟩
      · exact Or.inl mem)
    rw [h] at refused
    cases refused

/-! ## The translation a core uses

The MMU of a core translates through its cached cell when it has one (`uebersetze`). Whatever it grants
that way is a right of the cached entry, so by the invariant it is a right of the table unless a
narrowing of the page is pending. -/

/-- A translation granted through a cached entry grants a right of that entry. -/
theorem uebersetze_gecacht {z : ZielDaten} {sicht : MmuSicht} {core space addr : Nat}
    {right : Speicherdienst} {result : Nat × Nat}
    (ok : uebersetze z sicht core space addr right = .ok result) {entry : Seiteneintrag}
    (cached : sicht.tlb core space (addr / z.seitengranule) = some entry) : right ∈ entry.rights := by
  unfold uebersetze at ok
  split at ok
  · cases ok
  · simp only [cached, Option.orElse_some] at ok
    split at ok
    · cases ok
    · split at ok
      · rename_i hr
        exact hr
      · cases ok

/-- **A right used through a cached translation is a table right, or a narrowing is pending.** `view`
    says the MMU's cached entries are the cells of the frame. -/
theorem gecachte_rechte_gedeckt {frame : MemFrame} {sicht : MmuSicht}
    (view : ∀ core space page entry, sicht.tlb core space page = some entry →
      (⟨core, space, page, entry⟩ : TlbZelle) ∈ frame.tlb.zellen)
    (inv : frame.TlbRechteGedeckt) {core sp page : Nat} {entry : Seiteneintrag}
    (cached : sicht.tlb core sp page = some entry) {space : Adressraum}
    (hsp : frame.spaces[sp]? = some space) {right : Speicherdienst} (grants : right ∈ entry.rights) :
    frame.VerengtBei sp page ∨
      ∀ table, space.abbildung page = some table → table.frame = entry.frame → right ∈ table.rights := by
  rcases inv ⟨core, sp, page, entry⟩ (view core sp page entry cached) space hsp with ok | pending
  · exact Or.inr fun table found same => ok table found same right grants
  · exact Or.inl pending

end Gabbro.Core.Ast.LowLevel
