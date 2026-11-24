/-
  File:      Befunde.lean
  Subject:   Review findings on the low-level and catalogue statements. This module proves the
             vacuity of the narrowing-completion joint statement: the guard that the statement
             discharges is trivially satisfied by an empty translation cache, so the interesting
             case of a wider cached translation is not exercised. No existing statement is changed.
-/
module

public import Core.Ast.LowLevel.Mem.Meaning

@[expose] public section

namespace Gabbro.Core.Katalog.Review

open Gabbro.Core.Ast.LowLevel

/-- The completion guard of a narrowing: `TranslationCache.NichtBreiter` is the condition that
    `MemInstruction.evaluate` checks for a `nurRechte = true` token (Meaning.lean, `flushSpace`).
    With no cached cell the universal quantifier ranges over the empty list, so the guard holds
    for every space and every page range. This is the vacuity behind `FlushNarrowJointAussage`,
    whose run never fills a cell. -/
theorem nichtBreiter_leerer_cache_vakant (cache : TranslationCache) (space : Adressraum)
    (raum base pages : Nat) (h : cache.zellen = []) :
    cache.NichtBreiter space raum base pages := by
  intro zelle hz
  rw [h] at hz
  cases hz

/-- The release guard of an unmapped range: with no cached cell the universal quantifier in
    `TranslationCache.Frei` is empty, so the guard also holds for every space and range. -/
theorem frei_leerer_cache_vakant (cache : TranslationCache) (space base pages : Nat)
    (h : cache.zellen = []) : cache.Frei space base pages := by
  intro zelle hz
  rw [h] at hz
  cases hz

/-- The boolean form of the completion guard used by `evaluate` is likewise trivial with an
    empty cache. -/
theorem nichtBreiterBool_leerer_cache_vakant (cache : TranslationCache) (space : Adressraum)
    (raum base pages : Nat) (h : cache.zellen = []) :
    cache.nichtBreiter space raum base pages = true := by
  rw [TranslationCache.nichtBreiter, h]
  rfl

/-- The boolean form of the release guard, trivial with an empty cache. -/
theorem freiBool_leerer_cache_vakant (cache : TranslationCache) (space base pages : Nat)
    (h : cache.zellen = []) : cache.frei space base pages = true := by
  rw [TranslationCache.frei, h]
  rfl

/-- The closing clause of `FlushNarrowJointAussage` quantifies over `next.verengt`. In the
    witnessed run that list is empty, so the "no other pending token covers the range" claim is
    vacuous as well: no eviction and no second token are needed to discharge it. -/
theorem keinUeberlapp_vakant_leere_verengt (verengt : List Zuruecknahme) (token : Zuruecknahme)
    (h : verengt = []) : ∀ t ∈ verengt, ∀ pg, token.contains pg → ¬ t.contains pg := by
  intro t ht
  rw [h] at ht
  cases ht

end Gabbro.Core.Katalog.Review
