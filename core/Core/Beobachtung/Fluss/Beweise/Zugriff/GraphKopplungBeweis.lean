/-
  The final deduction of `SpeicherGraphKopplungAussage` from one single-run invariant: for a public cell,
  `HatQuelle` of the graph at a cut is exactly a public write of that cell observed after the last crash
  boundary. With that invariant the graph coupling at one cut is read off the equality of the two low
  prefixes in `Kopplung`: for a fragment the event relation is equality, and a write observation transfers
  verbatim. The invariant itself is the open obligation; the lemmas that prepare it are in `GraphBeob`.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphBeob

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl Plan)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- For a fragment the event relation is plain equality: its flow data declares no release. -/
theorem ereignisAequiv_fragment (p : Fragment) (plattform : Plattform)
    {a b : NiedrigesEreignis Ast.Semantik.Zelle Int Grund Befehl}
    (h : EreignisAequiv (p.einheit plattform).fluss.freigabe a b) : a = b := by
  cases h with
  | gleich e => rfl
  | freigabe c id links rechts g deklaration =>
    change none = some g at deklaration
    cases deklaration

/-- A pointwise-equal relation relates two lists only when they are equal. -/
theorem forall2_gleich {α : Type} {a b : List α} {r : α → α → Prop}
    (h : List.Forall₂ r a b) (heq : ∀ {u v}, r u v → u = v) : a = b := by
  induction h with
  | nil => rfl
  | cons head tail ih => rw [heq head, ih]

/-- The graph coupling follows from one single-run invariant and the prefix equality already carried
     by `Kopplung`. The invariant is left as a hypothesis: for a public cell, `HatQuelle` of the graph
     at a cut equals a public write of that cell observed after the last crash boundary. Difficulty:
     schwer. The crash case resets the graph but not the low trace, so a plain prefix reading is false;
     the graph-side step is `hatQuelle_nach_viele`, the observation-side step needs the low trace's
     write events to come only from `spur.speicher`. -/
theorem speicherGraphKopplung_aus_invariante
    (inv : ∀ (p : Fragment) (plattform : Plattform) {h : Umgebung} {ρ : Lauf (p.einheit plattform)},
      Laeufe (p.einheit plattform) h ρ → ∀ (predictor : Praediktor) (t : Nat) (x : Ast.Semantik.Zelle),
        match ρ.zeit.zustand t with
        | none => True
        | some s =>
          HatQuelle s.graph x ↔
            SchreibSeitAbsturz x (NiedrigeBeob (p.einheit plattform) ρ predictor t)) :
    SpeicherGraphKopplungAussage := by
  intro p plattform h₁ h₂ ρ₁ ρ₂ vergleich predictor t kopplung v w hv hw x hpub
  let E := p.einheit plattform
  have inv1base := inv p plattform (h := h₁) (ρ := ρ₁) vergleich.links predictor t x
  have inv2base := inv p plattform (h := h₂) (ρ := ρ₂) vergleich.rechts predictor t x
  rw [hv] at inv1base
  rw [hw] at inv2base
  have inv1 : HatQuelle v.graph x ↔ SchreibSeitAbsturz x (NiedrigeBeob E ρ₁ predictor t) := inv1base
  have inv2 : HatQuelle w.graph x ↔ SchreibSeitAbsturz x (NiedrigeBeob E ρ₂ predictor t) := inv2base
  have len : (NiedrigeBeob E ρ₁ predictor t).length = (NiedrigeBeob E ρ₂ predictor t).length :=
    kopplung.2.2
  have cov := kopplung.1
  have takeEq : (NiedrigeBeob E ρ₂ predictor t).take (NiedrigeBeob E ρ₁ predictor t).length =
      NiedrigeBeob E ρ₂ predictor t := List.take_of_length_le (le_of_eq len.symm)
  rw [takeEq] at cov
  have tracesEq : NiedrigeBeob E ρ₁ predictor t = NiedrigeBeob E ρ₂ predictor t :=
    forall2_gleich cov (fun {u v} h => ereignisAequiv_fragment p plattform h)
  rw [inv1, inv2, tracesEq]

end Gabbro.Core.Beobachtung
