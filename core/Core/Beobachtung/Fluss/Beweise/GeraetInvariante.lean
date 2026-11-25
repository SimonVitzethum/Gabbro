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
    length link is only required while the initial booking still holds.
    Pre-crash the epoch is zero, nothing is discarded and consumption counts
    the arrived answers (all arrived when idle, all but the last when a fresh
    answer waits). All questions and answers belong to the entry context, and
    recent questions are answered exactly when no fresh question waits.
    Questions are issued in order with fresh instances, and answers match the
    questions in order. -/
def GeraeteInvariantAussage {k : Katalog} (binding : Binding k) (s : State) : Prop :=
  (∀ c, c ≠ entryContext → (s.lokal c).pending = none ∧ s.verbraucht c = 0 ∧ s.verworfen c = 0) ∧
    (∀ q ∈ s.fragen, q.context = entryContext.nummer) ∧
    (∀ a ∈ s.antworten, a.context = entryContext.nummer) ∧
    (∀ i (h₁ : i < s.antworten.length) (h₂ : i < s.fragen.length),
      (s.antworten.get ⟨i, h₁⟩).zu (s.fragen.get ⟨i, h₂⟩)) ∧
    (∀ i (h : i < s.fragen.length), (s.fragen.get ⟨i, h⟩).questionInstance = i) ∧
    (s.buchung.geraet = (startBuchung binding.object binding.handle).geraet →
      s.epoche = 0 ∧ (∀ c, s.verworfen c = 0) ∧
      ((s.lokal entryContext).pending = none →
        s.fragen.length = s.antworten.length ∧ s.verbraucht entryContext = s.antworten.length ∧
        ∀ q ∈ s.fragen, s.epoche ≤ q.cut → ∃ a ∈ s.antworten, a.zu q) ∧
      ((s.lokal entryContext).pending ≠ none →
        (s.fragen.length = s.antworten.length ∧ s.verbraucht entryContext + 1 = s.antworten.length ∧
          ∀ q ∈ s.fragen, s.epoche ≤ q.cut → ∃ a ∈ s.antworten, a.zu q) ∨
        (s.fragen.length = s.antworten.length + 1 ∧ s.verbraucht entryContext = s.antworten.length ∧
          ∃ q ∈ s.fragen, s.epoche ≤ q.cut ∧ ∀ a ∈ s.antworten, ¬ a.zu q)))

/-- The invariant holds for every loaded device state: other contexts are
    empty, the entry pending slot is empty and both ledgers are empty. -/
theorem geraete_invariante_start {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {start : AussenStart} {load : Ladung} {z : State}
    (geladen : (d.unit locals).laden start load = some z) :
    GeraeteInvariantAussage d.binding z := by
  unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at geladen
  dsimp only at geladen
  split at geladen
  · obtain rfl := Option.some.inj geladen
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      dsimp only [bootFor, Zustand.start] at ⊢
      rw [if_neg hc]
      exact ⟨rfl, rfl, rfl⟩
    · intro q hq
      cases hq
    · intro a ha
      cases ha
    · intro i h₁ _
      exact absurd h₁ (Nat.not_lt_zero _)
    · intro i h
      exact absurd h (Nat.not_lt_zero _)
    · intro _
      refine ⟨rfl, fun _ => rfl, ?_, ?_⟩
      · intro _
        refine ⟨rfl, rfl, ?_⟩
        intro q hq _
        cases hq
      · intro hne
        dsimp only [bootFor, Zustand.start] at hne
        rw [if_pos rfl] at hne
        exact absurd rfl hne
  · cases geladen

end Gabbro.Core.Beobachtung
