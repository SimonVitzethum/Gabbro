module

public import Core.Beobachtung.Fluss.Beweise.GeraetStart
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)

/-- Single-context invariant for device runs: only the declaring entry context
    ever carries a pending question; while the device authority is still the
    initial one, an empty pending slot means the ledgers agree in length.
    After a crash the booking is empty and no device step is enabled, so the
    length link is only required while the initial booking still holds. -/
def GeraeteInvariantAussage {k : Katalog} (binding : Binding k) (s : State) : Prop :=
  (∀ c, c ≠ entryContext → (s.lokal c).pending = none) ∧
    (s.buchung.geraet = (startBuchung binding.object binding.handle).geraet →
      ((s.lokal entryContext).pending = none → s.fragen.length = s.antworten.length) ∧
      ((s.lokal entryContext).pending ≠ none →
        s.fragen.length = s.antworten.length ∨ s.fragen.length = s.antworten.length + 1))

/-- The invariant holds for every loaded device state: other contexts are
    empty, the entry pending slot is empty and both ledgers are empty. -/
theorem geraete_invariante_start {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {start : AussenStart} {load : Ladung} {z : State}
    (geladen : (d.unit locals).laden start load = some z) :
    GeraeteInvariantAussage d.binding z := by
  have hledger := geraete_laden_ledger_leer geladen
  obtain ⟨hfragen, _, hantworten, _⟩ := hledger
  unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at geladen
  dsimp only at geladen
  split at geladen
  · obtain rfl := Option.some.inj geladen
    refine ⟨?_, ?_⟩
    · intro c hc
      dsimp only [bootFor, Zustand.start] at ⊢
      rw [if_neg hc]
      rfl
    · intro _
      refine ⟨?_, ?_⟩
      · intro _
        simp only [hfragen, hantworten]
      · intro hne
        dsimp only [bootFor, Zustand.start] at hne
        rw [if_pos rfl] at hne
        exact absurd rfl hne
  · cases geladen

end Gabbro.Core.Beobachtung
