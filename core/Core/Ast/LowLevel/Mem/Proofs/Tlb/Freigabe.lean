module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Deckung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # The release step keeps every cached translation covered

`flush` removes the pending token and returns the frames. A cell the removed token covered would be
left pointing at a released frame, so the release step is enabled only when no core caches a page of
the range: then no cell is covered by the removed token alone. -/

theorem tlbGedeckt_flush (target : ZielDaten) (name : Identifier) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.flushSpace name).evaluate target s c = some next)
    (inv : (s.lokal c).TlbGedeckt) : next.TlbGedeckt := by
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
      split at h
      · rename_i cond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
        have frei := TranslationCache.frei_eq_true.mp cond.2
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        intro zelle mem
        change zelle ∈ (s.lokal c).tlb.zellen at mem
        obtain ⟨space0, found0, covered0⟩ := inv zelle mem
        by_cases same : zelle.raum = token.raum
        · have lt : token.raum < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hs).1
          have unique : space0 = space := by
            rw [same] at found0
            exact Option.some.inj (found0.symm.trans hs)
          rw [unique] at covered0
          refine ⟨?w, ?hw, ?hd⟩
          case hw =>
            rw [same]
            exact List.getElem?_set_self lt
          case hd =>
            refine Adressraum.deckt_mit (space := space) (fun entry found => ⟨entry, found, rfl⟩)
              ?_ covered0
            intro t tmem own
            by_cases eq : t = token
            · subst eq
              have outside := frei zelle mem
              simp only [TlbZelle.imBereich, decide_eq_false_iff_not] at outside
              exact (outside ⟨same, own.1⟩).elim
            · exact ⟨t, List.mem_filter.mpr ⟨tmem, bne_iff_ne.mpr eq⟩, own⟩
        · refine ⟨space0, ?_, covered0⟩
          change ((s.lokal c).spaces.set token.raum _)[zelle.raum]? = _
          exact MemFrame.TlbGedeckt.set_fern same found0
      · cases h

end Gabbro.Core.Ast.LowLevel
