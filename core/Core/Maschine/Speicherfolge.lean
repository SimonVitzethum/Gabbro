module

public import Core.Maschine.Kontext
public import Core.Speicher.Viele

@[expose] public section

namespace Gabbro.Core.Maschine

open Speicher

/-- Initialisation at each location has its own actor. It adds no program order to a context. -/
inductive SpeicherAkteur (Ort : Type) where
  | kontext (c : Kontext)
  | initial (x : Ort)
  | aussen

abbrev SpeicherGraph (Ort Wert : Type) := Speicher.Zustand (SpeicherAkteur Ort) Ort Wert

variable {Ort Wert : Type}

/-- An already recorded write at this location. -/
def HatQuelle (g : SpeicherGraph Ort Wert) (x : Ort) : Prop :=
  ∃ i, ∃ h : i < g.ev.length, (g.ev[i]'h).lab.art.schreibt ∧ (g.ev[i]'h).lab.ort = x

/-- A single lazily materialised initial write, immediately before the first memory access. -/
inductive Initialisierung (anfang : Ort → Wert) (l : Etikett Ort Wert) :
    SpeicherGraph Ort Wert → List (SpeicherAkteur Ort × Etikett Ort Wert) → SpeicherGraph Ort Wert → Prop
  | ohne {g} (h : l.art = .aussen ∨ HatQuelle g l.ort) : Initialisierung anfang l g [] g
  | erste {g g'} (mem : l.art ≠ .aussen) (neu : ¬ HatQuelle g l.ort)
      (schritt : g.Schritt (.initial l.ort) ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩ g') :
      Initialisierung anfang l g
        [(.initial l.ort, ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩)] g'

theorem Initialisierung.viele {anfang : Ort → Wert} {l : Etikett Ort Wert} {g g' : SpeicherGraph Ort Wert}
    {es} (h : Initialisierung anfang l g es g') : g.Viele es g' := by
  cases h with
  | ohne _ => exact .nil _
  | erste _ _ hs => exact .cons hs (.nil _)

theorem Initialisierung.quelle {anfang : Ort → Wert} {l : Etikett Ort Wert} {g g' : SpeicherGraph Ort Wert}
    {es} (h : Initialisierung anfang l g es g') (reads : l.art.liest) : HatQuelle g' l.ort := by
  cases h with
  | ohne hh =>
    rcases hh with outside | found
    · rw [outside] at reads
      exact False.elim reads
    · exact found
  | erste _ _ hs =>
    have idx : g.ev.length < g'.ev.length := by
      rw [hs.ev, List.length_append, List.length_singleton]
      exact Nat.lt_succ_self _
    refine ⟨g.ev.length, idx, ?_⟩
    have eq : g'.ev[g.ev.length]'idx = ⟨SpeicherAkteur.initial l.ort,
        ⟨Art.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩⟩ := by
      simp only [hs.ev, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    rw [eq]
    exact ⟨trivial, rfl⟩

/-- Initialisation is always possible from a consistent, complete prefix. -/
theorem initialisierung_existiert (anfang : Ort → Wert) (l : Etikett Ort Wert) {g : SpeicherGraph Ort Wert}
    (hk : g.graph.Konsistent) (hv : g.graph.Vollstaendig) :
    ∃ es g', Initialisierung anfang l g es g' := by
  by_cases outside : l.art = .aussen
  · exact ⟨[], g, .ohne (Or.inl outside)⟩
  by_cases found : HatQuelle g l.ort
  · exact ⟨[], g, .ohne (Or.inr found)⟩
  obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen hk hv (.initial l.ort)
    ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩ id
  exact ⟨_, g', .erste outside found hs⟩

/-- Extend one RC11 prefix with the designated labels. An initial write is part of the append,
    with its own reads-from and modification-order constraints from the graph machine. -/
inductive Speicherfolge (anfang : Ort → Wert) (f : SpeicherAkteur Ort) :
    SpeicherGraph Ort Wert → List (Etikett Ort Wert) →
      List (SpeicherAkteur Ort × Etikett Ort Wert) → SpeicherGraph Ort Wert → Prop
  | nil (g) : Speicherfolge anfang f g [] [] g
  | cons {g g₀ g₁ g₂ l ls init es}
      (vor : Initialisierung anfang l g init g₀) (hs : g₀.Schritt f l g₁)
      (nach : Speicherfolge anfang f g₁ ls es g₂) :
      Speicherfolge anfang f g (l :: ls) (init ++ (f, l) :: es) g₂

theorem Speicherfolge.viele {anfang : Ort → Wert} {f : SpeicherAkteur Ort} {g g' : SpeicherGraph Ort Wert}
    {ls es} (h : Speicherfolge anfang f g ls es g') : g.Viele es g' := by
  induction h with
  | nil _ => exact .nil _
  | cons vor hs _ ih => exact vor.viele.append (.cons hs ih)

/-- A read or update can always take the latest write, including at the first access. Any other
    consistent source remains available through the step relation. -/
theorem speicherzug_existiert (anfang : Ort → Wert) (f : SpeicherAkteur Ort)
    {g : SpeicherGraph Ort Wert} (hk : g.graph.Konsistent) (hv : g.graph.Vollstaendig)
    (a : Art) (x : Ort) (m : Modus) (v : Wert) (hrmw : a = .rmw → m ≠ .na) :
    ∃ r es g', Speicherfolge anfang f g [⟨a, x, m, r, v⟩] es g' := by
  obtain ⟨init, g₀, hz⟩ := initialisierung_existiert anfang ⟨a, x, m, v, v⟩ hk hv
  have gut := hz.viele.gut hk hv
  obtain ⟨r, g₁, hs, _⟩ :=
    Speicher.Zustand.schritt_existiert gut.1 gut.2 f a x m v (fun hr => hz.quelle hr) hrmw
  have hz' : Initialisierung anfang ⟨a, x, m, r, v⟩ g init g₀ := by
    cases hz with
    | ohne h => exact .ohne h
    | erste mem neu h => exact .erste mem neu h
  exact ⟨r, _, g₁, .cons hz' hs (.nil _)⟩

theorem speicherfolge_erfuellbar (anfang : Ort → Wert) (c : Kontext) (x : Ort) (m : Modus) :
    ∃ r es g', Speicherfolge anfang (.kontext c) Speicher.Zustand.leer
      [⟨.lesen, x, m, r, anfang x⟩] es g' :=
  speicherzug_existiert anfang _ Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    .lesen x m (anfang x) (fun h => by cases h)

end Gabbro.Core.Maschine
