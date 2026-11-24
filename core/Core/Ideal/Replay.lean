module

public import Core.Maschine.Aussen

@[expose] public section

namespace Gabbro.Core.Maschine.I

variable {S Op : Type}

/-- Replay the private operations of one unit in their source order. The operation type can
    include the recorded choice of each operation. -/
inductive Replay (step : S → Op → S → Prop) : S → List Op → S → Prop where
  | nil (s : S) : Replay step s [] s
  | cons {s m t op ops} (h : step s op m) (rest : Replay step m ops t) : Replay step s (op :: ops) t

/-- Agreement of two memory projections on the footprint of the running unit. -/
def StimmtUeberein {X V : Type} (fuss : X → Prop) (a b : X → V) : Prop :=
  ∀ x, fuss x → a x = b x

theorem replay_rahmen {step : S → Op → S → Prop} {gleich : S → S → Prop}
    (rahmen : ∀ s op t, step s op t → ∀ s', gleich s s' → ∃ t', step s' op t' ∧ gleich t t')
    {s t s' : S} {ops : List Op} (replay : Replay step s ops t) (start : gleich s s') :
    ∃ t', Replay step s' ops t' ∧ gleich t t' := by
  induction replay generalizing s' with
  | nil s => exact ⟨s', .nil s', start⟩
  | cons h _ ih =>
    obtain ⟨m', h', middle⟩ := rahmen _ _ _ h _ start
    obtain ⟨t', rest', last⟩ := ih middle
    exact ⟨t', .cons h' rest', last⟩

/-- Between units the local states agree. Before the linearisation point the implementation is
    a replay of a prefix from the ideal state. After that point the private suffix remains to run. -/
inductive EinheitsBezug (step : S → Op → S → Prop) : S → S → Prop where
  | zwischen (s : S) : EinheitsBezug step s s
  | vor {impl ideal ops} (anfang : Replay step ideal ops impl) : EinheitsBezug step impl ideal
  | nach {impl ideal ops} (suffix : Replay step impl ops ideal) : EinheitsBezug step impl ideal

theorem replay_erfuellbar {X V : Type} (fuss : X → Prop) (update : Op → (X → V) → X → V)
    (lokal : ∀ op a b, StimmtUeberein fuss a b → StimmtUeberein fuss (update op a) (update op b))
    (a b : X → V) (eq : StimmtUeberein fuss a b) (op : Op) :
    Replay (fun s action t => t = update action s) b [op] (update op b) ∧
      StimmtUeberein fuss (update op a) (update op b) :=
  ⟨.cons rfl (.nil _), lokal op a b eq⟩

variable {L Ort Wert Raum Lok Grund : Type}

/-- Question, arrival and consumption accounting is shared at every matched cut, even when a
    context is inside a unit. -/
structure AussenBezug (impl ideal : Zustand L Ort Wert Raum Lok Grund) : Prop where
  fragen : impl.fragen = ideal.fragen
  antworten : impl.antworten = ideal.antworten
  verbraucht : impl.verbraucht = ideal.verbraucht
  verlauf : impl.verlauf = ideal.verlauf

theorem aussen_refl (s : Zustand L Ort Wert Raum Lok Grund) : AussenBezug s s :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem aussen_ankunft {s i : Zustand L Ort Wert Raum Lok Grund} (h : AussenBezug s i)
    (a : Katalog.AntwortEreignis) : AussenBezug (s.antwort a) (i.antwort a) :=
  ⟨h.fragen, congrArg (· ++ [a]) h.antworten, h.verbraucht,
    congrArg (· ++ [(a.cut, Katalog.AussenEreignis.antwort a.question a.reply)]) h.verlauf⟩

theorem aussen_verbrauch {s i : Zustand L Ort Wert Raum Lok Grund} (h : AussenBezug s i)
    (c : Kontext) : AussenBezug (s.verbrauche c) (i.verbrauche c) :=
  ⟨h.fragen, h.antworten, congrArg (fun p : Kontext → Nat => Function.update p c (p c + 1)) h.verbraucht,
    h.verlauf⟩

end Gabbro.Core.Maschine.I
