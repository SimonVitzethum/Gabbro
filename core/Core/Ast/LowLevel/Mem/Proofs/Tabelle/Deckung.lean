module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Sicht
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Fuellung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # Table entries stay covered by reservations

A table entry maps one virtual page to one physical frame. The invariant below says what a table
entry always satisfies: no pending `unmap` token of its space covers its page (entries and tokens
are disjoint, the refill-relevant part of `Adressraum.Wohlgeformt`), every pending `unmap` token of
the space owns frames (`nurRechte = false`) and belongs to the space, every entry carries a right
and a generation the space has reached, and every pending narrowing (`verengt`) owns no frame.
Together with the cache invariants this connects a translation served from the tables to a reserved
frame and a covered right. -/

/-- What every address space satisfies about its table: disjoint from pending `unmap` tokens,
    tokens own frames and belong to the space, entries carry rights and reached generations. -/
def Adressraum.TabellenGedeckt (space : Adressraum) (sp : Nat) : Prop :=
  space.FreiAusstehend ∧
    (∀ token ∈ space.ausstehend, token.nurRechte = false ∧ token.raum = sp) ∧
    (∀ entry ∈ space.entries, entry.2.rights ≠ [] ∧ entry.2.generation ≤ space.generation)

/-- Every table entry of every space is covered, and every pending narrowing owns no frame. -/
def MemFrame.TabellenGedeckt (frame : MemFrame) : Prop :=
  (∀ sp space, frame.spaces[sp]? = some space → space.TabellenGedeckt sp) ∧
    (∀ token ∈ frame.verengt, token.nurRechte = true)

/-- A fresh frame (no space) satisfies the table invariant. -/
theorem MemFrame.TabellenGedeckt.leer {frame : MemFrame} (empty : frame.spaces = []) :
    frame.TabellenGedeckt := by
  refine ⟨?spaces, ?narrow⟩
  · intro sp space found
    rw [empty] at found
    cases found
  · intro token mem
    rw [empty] at mem
    cases mem

theorem MemFrame.TabellenGedeckt.aus_gleich {frame next : MemFrame}
    (inv : frame.TabellenGedeckt)
    (spaces : next.spaces = frame.spaces) (verengt : next.verengt = frame.verengt) :
    next.TabellenGedeckt := by
  obtain ⟨hspaces, hnarrow⟩ := inv
  refine ⟨?spaces, ?narrow⟩
  · intro sp space found
    rw [spaces] at found
    exact hspaces sp space found
  · intro token mem
    rw [verengt] at mem
    exact hnarrow token mem

/-- A table hit serves the entry of its space. -/
theorem MemFrame.tabellenSicht_hit {frame : MemFrame} {sp page : Nat} {entry : Seiteneintrag}
    (hit : frame.tabellenSicht sp page = some entry) :
    ∃ space, frame.spaces[sp]? = some space ∧ space.abbildung page = some entry := by
  unfold MemFrame.tabellenSicht at hit
  cases hfound : frame.spaces[sp]? with
  | none =>
    simp only [hfound] at hit
    cases hit
  | some space =>
    simp only [hfound] at hit
    exact ⟨space, hfound, hit⟩

/-- A table entry makes its own single-page extent reserved: the space holding it overlaps it. -/
theorem Adressraum.eintrag_reserviert {frame : MemFrame} {sp : Nat} {space : Adressraum}
    (found : frame.spaces[sp]? = some space) {page : Nat} {entry : Seiteneintrag}
    (hit : space.abbildung page = some entry) {granule : Nat} (gpos : 0 < granule) :
    frame.unreserved granule ⟨entry.frame * granule, (entry.frame + 1) * granule⟩ = false := by
  have spaceMem : space ∈ frame.spaces := List.mem_of_getElem? found
  by_contra hne
  have htrue : frame.unreserved granule ⟨entry.frame * granule, (entry.frame + 1) * granule⟩ =
      true := by
    simpa only [Bool.not_eq_false] using hne
  unfold MemFrame.unreserved at htrue
  have hall := List.all_eq_true.mp htrue space spaceMem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨_, hentries⟩, _⟩ := hall
  unfold Adressraum.abbildung at hit
  cases hfind : space.entries.find? (fun e => e.1 == page) with
  | none =>
    simp only [hfind, Option.map_none] at hit
    cases hit
  | some pair =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hit
    have pairMem := List.mem_of_find?_eq_some hfind
    have sep := List.all_eq_true.mp hentries pair pairMem
    simp only [decide_eq_true_eq] at sep
    obtain ⟨pg, ent⟩ := pair
    simp only at hit
    subst hit
    have expand : (ent.frame + 1) * granule = ent.frame * granule + granule := by
      rw [Nat.add_mul]
      simp only [Nat.one_mul]
    have self : ¬ (⟨ent.frame * granule, (ent.frame + 1) * granule⟩ : Strecke).getrennt
        ⟨ent.frame * granule, (ent.frame + 1) * granule⟩ := by
      intro h
      rw [expand] at h
      rcases h with h | h
      · omega
      · omega
    exact self sep

end Gabbro.Core.Ast.LowLevel
