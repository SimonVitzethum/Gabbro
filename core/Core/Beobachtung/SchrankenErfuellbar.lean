module

public import Core.Beobachtung.Schranken
public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Annahme Katalog Maschine

/-- Both sides of a unit's concrete stack boundary occur on admitted runs with a successful load. -/
theorem schranken_erfuellbar (grenze : Nat) :
    ∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (h : Umgebung) (ρ : Lauf E),
      Laeufe E h ρ ∧ E.schranken.stapel = some grenze ∧ (ImSchranken E ρ ↔ 1 ≤ grenze) := by
  let E := { trivialeEinheit with
    laden := fun s _ => some (I.start trivialeEinheit s).2
    schranken := { Schrankendaten.leer with stapel := some grenze, stapelTiefe := fun _ => 1 } }
  have image : E.bild.gueltig E.katalog.plattform.ziel := by
    exact ⟨List.Mem.head _, (fun _ _ h => nomatch h), fun _ h => (List.not_mem_nil h).elim⟩
  obtain ⟨h, _, hw, _⟩ := katalog_nichtLeer E.katalog (Plattform.katalog_wohlgeformt .x86_64)
  obtain ⟨s, zul⟩ := zulStart_erfuellbar hw image
  obtain ⟨ρ, run, _⟩ := lauf_ab_start E hw zul
  refine ⟨E, h, ρ, run, rfl, ?_⟩
  constructor
  · intro bounded
    exact (bounded.2.2.2 0 _ run.2.2.2.1).2.1 (.faden 0) grenze rfl
  · intro bound
    exact ⟨(fun _ _ _ _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ _ _ c m hmem => (List.not_mem_nil hmem).elim),
      fun _ _ _ => ⟨(fun _ h => nomatch h), fun _ _ h => (Option.some.inj h) ▸ bound,
        fun _ _ h => (List.not_mem_nil h).elim⟩⟩

end Gabbro.Core.Beobachtung
