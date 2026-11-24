module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Lauf
public import Core.Ast.LowLevel.Mem.Proofs.Flush.Flush

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # A cached translation keeps its frame reserved, and the release step is necessary

`unreserved` is the test every region operation passes before it hands frames out again. A frame
a core still caches is never unreserved, so it cannot be mapped, split off or merged anew while a stale
translation of it exists. Without the release guard the invariant breaks. -/

theorem MemFrame.TlbGedeckt.nicht_unreserviert {frame : MemFrame} (inv : frame.TlbGedeckt)
    (granule : Nat) {zelle : TlbZelle} (mem : zelle ∈ frame.tlb.zellen) (extent : Strecke)
    (overlap : ¬ extent.getrennt ⟨zelle.eintrag.frame * granule, (zelle.eintrag.frame + 1) * granule⟩) :
    frame.unreserved granule extent = false := by
  obtain ⟨space, found, covered⟩ := inv zelle mem
  have spaceMem : space ∈ frame.spaces := List.mem_of_getElem? found
  by_contra hne
  have htrue : frame.unreserved granule extent = true := by simpa only [Bool.not_eq_false] using hne
  unfold MemFrame.unreserved at htrue
  have all := List.all_eq_true.mp htrue space spaceMem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at all
  obtain ⟨⟨_, hentries⟩, htokens⟩ := all
  rcases covered with ⟨entry, hmap, hframe⟩ | ⟨token, tmem, hcontains, hf⟩
  · unfold Adressraum.abbildung at hmap
    cases hfind : space.entries.find? (fun e => e.1 == zelle.seite) with
    | none => simp only [hfind, Option.map_none] at hmap <;> cases hmap
    | some pair =>
      simp only [hfind, Option.map_some, Option.some.injEq] at hmap
      have pairMem := List.mem_of_find?_eq_some hfind
      have sep := List.all_eq_true.mp hentries pair pairMem
      obtain ⟨page, entry'⟩ := pair
      simp only [decide_eq_true_eq] at sep
      simp only at hmap
      subst hmap
      rw [hframe] at sep
      exact overlap sep
  · have sep := List.all_eq_true.mp htokens token tmem
    simp only [decide_eq_true_eq] at sep
    unfold Zuruecknahme.frames at sep
    have lo : token.frameBasis * granule ≤ zelle.eintrag.frame * granule :=
      Nat.mul_le_mul_right granule (by rw [hf]; exact Nat.le_add_right _ _)
    have hi : (zelle.eintrag.frame + 1) * granule ≤ (token.frameBasis + token.seiten) * granule :=
      Nat.mul_le_mul_right granule (by
        have := hcontains.2
        have := hcontains.1
        omega)
    rcases sep with before | after
    · exact overlap (Or.inl (Nat.le_trans before lo))
    · exact overlap (Or.inr (Nat.le_trans hi after))

/-- The release step refuses while some core caches a translation of the range. -/
theorem flush_verweigert_gecachte_uebersetzung (target : ZielDaten) (s : MemState) (c : Kontext)
    (name : Identifier) (token : Zuruecknahme) (space : Adressraum)
    (hfind : ((s.lokal c).marken.find? (fun p => p.1.val == name.val)).map Prod.snd = some token)
    (hspace : (s.lokal c).spaces[token.raum]? = some space) {zelle : TlbZelle}
    (mem : zelle ∈ (s.lokal c).tlb.zellen) (inside : zelle.raum = token.raum)
    (page : token.contains zelle.seite) :
    (MemInstruction.flushSpace name).evaluate target s c = none := by
  refine ((flush_aussage.2.1 target s c name token space hfind hspace).2
    (Or.inr (Or.inr ?_)))
  intro frei
  have nofrei := frei zelle mem
  simp only [TlbZelle.imBereich, decide_eq_false_iff_not] at nofrei
  exact nofrei ⟨inside, page⟩

/-- Why the guard is necessary: a frame in which core 7 caches page 0 of a pending token (frame 5) is
    covered; the same frame with the token released, the cell kept, is not. A release that leaves
    the cell behind lets a core translate to a frame that is no longer reserved. -/
theorem freigabe_ohne_pflicht_unsicher :
    ∃ (before after : MemFrame), before.TlbGedeckt ∧ ¬ after.TlbGedeckt ∧
      after.tlb = before.tlb := by
  let token : Zuruecknahme := ⟨0, 0, 1, 1, 5⟩
  let cell : TlbZelle := ⟨7, 0, 0, ⟨5, [.read], 0⟩⟩
  refine ⟨{ spaces := [{ tabellen := ⟨0, 0⟩, entries := [], generation := 1, ausstehend := [token] }]
            tlb := ⟨[cell]⟩ },
    { spaces := [{ tabellen := ⟨0, 0⟩, entries := [], generation := 1, ausstehend := [] }]
      tlb := ⟨[cell]⟩ }, ?_, ?_, rfl⟩
  · intro zelle mem
    have : zelle = cell := List.mem_singleton.mp mem
    subst this
    refine ⟨_, rfl, Or.inr ⟨token, List.mem_singleton_self _, ?_, ?_⟩⟩
    · decide
    · rfl
  · intro covered
    obtain ⟨space, found, hd⟩ := covered cell (List.mem_singleton_self _)
    have eq : space = { tabellen := ⟨0, 0⟩, entries := [], generation := 1, ausstehend := [] } :=
      (Option.some.inj found).symm
    subst eq
    rcases hd with ⟨entry, hmap, _⟩ | ⟨t, tmem, _⟩
    · cases hmap
    · cases tmem

end Gabbro.Core.Ast.LowLevel
