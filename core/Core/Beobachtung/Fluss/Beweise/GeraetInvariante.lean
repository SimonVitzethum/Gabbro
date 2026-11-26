module

public import Core.Beobachtung.Fluss.Beweise.GeraetStart
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)

/-- Single-context invariant for device runs, pre- and post-crash. Pre-crash
    (while the device authority is still the initial one) only the declaring
    entry context ever carries a pending question, nothing is discarded, the
    epoch is zero, and consumption counts the arrived answers (all arrived when
    idle, all but the last when a fresh answer waits). All questions and answers
    belong to the entry context, recent questions are answered exactly when no
    fresh question waits, questions are issued in order with fresh instances,
    and answers match the questions in order. Post-crash (any other authority)
    the booking is empty, no context carries a pending question, and every
    recorded question predates the crash epoch, so no arrival can match it. -/
def GeraeteInvariantAussage {k : Katalog} (binding : Binding k) (s : State) : Prop :=
  (∀ c, c ≠ entryContext → (s.lokal c).pending = none ∧ s.verbraucht c = 0 ∧ s.verworfen c = 0) ∧
  (∀ q ∈ s.fragen, q.context = entryContext.nummer) ∧
  (∀ a ∈ s.antworten, a.context = entryContext.nummer) ∧
  List.Forall₂ (fun a q => a.zu q) s.antworten (s.fragen.take s.antworten.length) ∧
  List.map (fun q : FrageEreignis => q.questionInstance) s.fragen =
    List.range s.fragen.length ∧
  (s.buchung.geraet = (startBuchung binding.object binding.handle).geraet →
    (∀ c, s.verworfen c = 0) ∧ s.epoche = 0 ∧
    ((s.lokal entryContext).pending = none →
      s.fragen.length = s.antworten.length ∧ s.verbraucht entryContext = s.antworten.length ∧
      ∀ q ∈ s.fragen, s.epoche ≤ q.cut → ∃ a ∈ s.antworten, a.zu q) ∧
    ((s.lokal entryContext).pending ≠ none →
      (s.fragen.length = s.antworten.length ∧ s.verbraucht entryContext + 1 = s.antworten.length ∧
        ∀ q ∈ s.fragen, s.epoche ≤ q.cut → ∃ a ∈ s.antworten, a.zu q) ∨
      (s.fragen.length = s.antworten.length + 1 ∧ s.verbraucht entryContext = s.antworten.length ∧
        ∃ q ∈ s.fragen, s.epoche ≤ q.cut ∧ ∀ a ∈ s.antworten, ¬ a.zu q))) ∧
  (s.buchung.geraet ≠ (startBuchung binding.object binding.handle).geraet →
    s.buchung.geraet = (fun _ => none) ∧
    (∀ c, (s.lokal c).pending = none) ∧
    (∀ q ∈ s.fragen, q.cut < s.epoche))

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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      dsimp only [bootFor, Zustand.start] at ⊢
      rw [if_neg hc]
      exact ⟨rfl, rfl, rfl⟩
    · intro q hq
      cases hq
    · intro a ha
      cases ha
    · exact List.Forall₂.nil
    · rfl
    · intro _
      refine ⟨fun _ => rfl, rfl, ?_, ?_⟩
      · intro _
        refine ⟨rfl, rfl, ?_⟩
        intro q hq _
        cases hq
      · intro hne
        dsimp only [bootFor, Zustand.start] at hne
        rw [if_pos rfl] at hne
        exact absurd rfl hne
    · intro hne
      exact (hne rfl).elim
  · cases geladen

end Gabbro.Core.Beobachtung
