module

public import Core.Maschine.Speicherfolge

@[expose] public section

namespace Gabbro.Core.Maschine

open Speicher (Etikett)

variable {Ort Wert : Type}

private theorem hatQuelle_gleich {g h : SpeicherGraph Ort Wert} {x : Ort} (ev : g.ev = h.ev) :
    HatQuelle g x ↔ HatQuelle h x := by
  unfold HatQuelle
  rw [ev]

/-- The prior event list fixes whether the location's initial write must be materialised. -/
theorem Initialisierung.ausgabe {anfang : Ort → Wert} {l : Etikett Ort Wert}
    {g g' h h' : SpeicherGraph Ort Wert} {xs ys}
    (a : Initialisierung anfang l g xs g') (b : Initialisierung anfang l h ys h')
    (ev : g.ev = h.ev) : xs = ys ∧ g'.ev = h'.ev := by
  cases a with
  | ohne old =>
    cases b with
    | ohne => exact ⟨rfl, ev⟩
    | erste access fresh _ =>
      exact (old.elim access (fun found => fresh ((hatQuelle_gleich ev).mp found))).elim
  | erste access fresh first =>
    cases b with
    | ohne old =>
      exact (old.elim access (fun found => fresh ((hatQuelle_gleich ev).mpr found))).elim
    | erste _ _ second =>
      exact ⟨rfl, first.ev.trans ((congrArg (· ++ [_]) ev).trans second.ev.symm)⟩

/-- For fixed input events and labels, an append fixes the emitted events. The order
    relations remain the memory model's choices. -/
theorem Speicherfolge.ausgabe {anfang : Ort → Wert} {f : SpeicherAkteur Ort}
    {g g' h h' : SpeicherGraph Ort Wert} {ls xs ys}
    (a : Speicherfolge anfang f g ls xs g') (b : Speicherfolge anfang f h ls ys h')
    (ev : g.ev = h.ev) : xs = ys ∧ g'.ev = h'.ev := by
  induction a generalizing h ys h' with
  | nil =>
    cases b
    exact ⟨rfl, ev⟩
  | cons init step _ ih =>
    cases b with
    | cons init' step' rest' =>
      obtain ⟨sameInit, initEvents⟩ := init.ausgabe init' ev
      have stepEvents := step.ev.trans ((congrArg (· ++ [_]) initEvents).trans step'.ev.symm)
      obtain ⟨sameRest, finalEvents⟩ := ih rest' stepEvents
      exact ⟨by rw [sameInit, sameRest], finalEvents⟩

/-- RC11 order resolutions are separate from the events and the state they determine. -/
def SpeicherWahlGleich (g h : SpeicherGraph Ort Wert) : Prop :=
  g.po = h.po ∧ g.rf = h.rf ∧ g.mo = h.mo

theorem Speicherfolge.bestimmt {anfang : Ort → Wert} {f : SpeicherAkteur Ort}
    {g g' h' : SpeicherGraph Ort Wert} {ls xs ys}
    (a : Speicherfolge anfang f g ls xs g') (b : Speicherfolge anfang f g ls ys h')
    (wahl : SpeicherWahlGleich g' h') : xs = ys ∧ g' = h' := by
  obtain ⟨trace, events⟩ := a.ausgabe b rfl
  refine ⟨trace, ?_⟩
  cases g'
  cases h'
  obtain ⟨rfl, rfl, rfl⟩ := wahl
  cases events
  rfl

end Gabbro.Core.Maschine
