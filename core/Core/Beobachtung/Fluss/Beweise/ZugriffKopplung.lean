/-
  File:      core/Core/Beobachtung/Fluss/Beweise/ZugriffKopplung.lean
  Subject:   THE MISSING RUN-LEVEL PREMISE FOR `ZugriffNIAussage` (MK-13). The step-level part of access
             noninterference is proved in `ZugriffSchritt`: two steps of one access form from public-equal
             source states keep equal plan and output views, and one access label fixes the memory-event list
             once the pre-graph is fixed. What is NOT carried by `Kopplung` is the memory graph: two coupled
             states can differ in `HatQuelle` for a cell, so the lazily materialised initial write can appear
             on one side only and `speicherBeob` can observe different events. This file names exactly that
             missing step as the pinned `SpeicherGraphKopplungAussage` (the graph coupling of public cells,
             maintained along coupled runs) and proves the single-cut lemmas that consume it: with equal
             `HatQuelle` on the two pre-graphs and the same context actor, one access label gives equal
             memory-event lists and hence equal observed low memory events.
-/
module

public import Core.Beobachtung.Fluss.Beweise.ZugriffSchritt
public import Core.Beobachtung.Nichtinterferenz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl Plan)

/-- The graph coupling of two states for the publicly visible cells: a cell whose place label is
    public has a recorded write in the left state's graph exactly when it has one in the right
    state's graph. This is the `HatQuelle` predicate the lazy initial write of `Speicherfolge` reads. -/
def SpeicherGraphKopplungZustand [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (v w : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ x : Ort, oeffentlich (E.etiketten.ort x) = true →
    (HatQuelle v.graph x ↔ HatQuelle w.graph x)

/-- The graph coupling along two compared runs at one same cut. -/
def SpeicherGraphKopplung [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ₁ ρ₂ : Lauf E) (predictor : Praediktor) (t : Nat) : Prop :=
  ∀ v w, ρ₁.zeit.zustand t = some v → ρ₂.zeit.zustand t = some w →
    SpeicherGraphKopplungZustand E v w

/-- **The missing run-level premise of access noninterference**: the graph coupling of public cells
    holds at every same cut of two compared, coupled runs. Difficulty: schwer (the step of an access
    instruction can materialise a lazy initial write on one side only; the coupling invariant must carry
    the graph relation for public cells and maintain it step by step). This is the single statement the
    step-level results of `ZugriffSchritt` lack; the lemmas below show it is exactly what closes one cut. -/
def SpeicherGraphKopplungAussage : Prop :=
  ∀ (p : Fragment) (plattform : Plattform) {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (p.einheit plattform)},
    Vergleich (p.einheit plattform) h₁ h₂ ρ₁ ρ₂ → ∀ (predictor : Praediktor) (t : Nat),
      Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor t t →
        SpeicherGraphKopplung (p.einheit plattform) ρ₁ ρ₂ predictor t

/-- Two one-label `Speicherfolge` derivations from graphs that merely agree on `HatQuelle` at the
    accessed cell record the same memory events: the optional initial write is decided by `HatQuelle`
    alone, the actor and the label are the same, and reads-from resolution changes only the successor
    graph. This is the precise upgrade of `zugriffSpeicherfolge_gleich` from equal graphs to the
    public-cell graph coupling. -/
theorem zugriffSpeicherfolge_gleich_hatquelle
    {Ort Wert : Type} {anfang : Ort → Wert} {c : Kontext}
    {g₁ g₂ : Maschine.SpeicherGraph Ort Wert} {l : Speicher.Etikett Ort Wert}
    {es₁ es₂ : List (Maschine.SpeicherAkteur Ort × Speicher.Etikett Ort Wert)}
    {g₁' g₂' : Maschine.SpeicherGraph Ort Wert}
    (hg : (l.art ≠ .aussen) → (HatQuelle g₁ l.ort ↔ HatQuelle g₂ l.ort))
    (h₁ : Maschine.Speicherfolge anfang (.kontext c) g₁ [l] es₁ g₁')
    (h₂ : Maschine.Speicherfolge anfang (.kontext c) g₂ [l] es₂ g₂') :
    es₁ = es₂ := by
  cases h₁ with
  | cons vor₁ hs₁ nach₁ =>
    cases nach₁
    cases h₂ with
    | cons vor₂ hs₂ nach₂ =>
      cases nach₂
      cases vor₁ with
      | ohne hh₁ =>
        cases vor₂ with
        | ohne hh₂ => rfl
        | erste mem₂ neu₂ hs =>
          exfalso
          rcases hh₁ with outside | found
          · exact mem₂ outside
          · exact neu₂ ((hg mem₂).mp found)
      | erste mem₁ neu₁ hs =>
        cases vor₂ with
        | ohne hh₂ =>
          exfalso
          rcases hh₂ with outside | found
          · exact mem₁ outside
          · exact neu₁ ((hg mem₁).mpr found)
        | erste mem₂ neu₂ hs₂' => rfl

/-- Equal memory-event lists give equal observed low memory events. Combined with the step-level
    `zugriffSpeicherfolge_gleich`, this closes the memory-event part of one access cut from the graph
    coupling: equal plan views fix the label, the graph coupling fixes the optional initial write. -/
theorem zugriffSpeicherbeob_gleich_aus_kopplung
    {Ort Wert Grund Form : Type} (label : Etiketten Ort) {anfang : Ort → Wert} {c : Kontext}
    {g₁ g₂ : Maschine.SpeicherGraph Ort Wert} {l : Speicher.Etikett Ort Wert}
    {es₁ es₂ : List (Maschine.SpeicherAkteur Ort × Speicher.Etikett Ort Wert)}
    {g₁' g₂' : Maschine.SpeicherGraph Ort Wert}
    (hg : (l.art ≠ .aussen) → (HatQuelle g₁ l.ort ↔ HatQuelle g₂ l.ort))
    (h₁ : Maschine.Speicherfolge anfang (.kontext c) g₁ [l] es₁ g₁')
    (h₂ : Maschine.Speicherfolge anfang (.kontext c) g₂ [l] es₂ g₂') :
    es₁.filterMap (speicherBeob (Grund := Grund) (Form := Form) label) =
      es₂.filterMap (speicherBeob (Grund := Grund) (Form := Form) label) := by
  rw [zugriffSpeicherfolge_gleich_hatquelle hg h₁ h₂]

end Gabbro.Core.Beobachtung
