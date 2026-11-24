/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Mittel.lean
  Subject:   The medium M9 B9/B21 boundary duties pinned in `SchrankenB9B21Pflichten`.
-/
module

public import Core.Beobachtung.SchrankenB9B21Pflichten

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast

/-- A step that adds no live cell preserves the memory bound: the live set only shrinks. -/
theorem speicherErhalten : speicherErhaltenAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E vor nach speicherVor wachstum n grenze
  exact le_trans (Set.encard_le_encard wachstum) (speicherVor n grenze)

/-- A crash reinstalls the recovery entry: its start data supplies both bounds, and the
    durable booking contributes no live cell. -/
theorem absturzSchranken : absturzSchrankenAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E region w k run t spur s s'
    startDaten stapelVor speicherVor schritt
  rw [schritt.genau.2]
  constructor
  · intro c n grenze
    exact (startDaten (nachAbsturz s.persistenz) c).1 n grenze
  · intro n grenze
    have leer : LebendeZellen (s.wiederanlauf w t (nachAbsturz s.persistenz)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z zLive
      exact (startDaten (nachAbsturz s.persistenz) w.eintritt).2 z (by
        simpa only [Zustand.wiederanlauf, Zustand.start] using zLive)
    rw [leer, Set.encard_empty]
    exact zero_le

/-- Whole-run transfer: the ideal prefix bounds move to every implementation cut through
    the per-tick state relation, with the depth-respecting local relation for the stack. -/
theorem schrankenTransfer : schrankenTransferAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ η pflicht idealLauf bezug t s cut
  obtain ⟨s', cut', bezugCut⟩ := bezug t
  have eq : s' = s := Option.some.inj (cut'.symm.trans cut)
  subst s'
  have idealPrefix := schranken_prefix_aus_lokal pflicht idealLauf t
  exact ⟨(stapel_bezug pflicht.bezug bezugCut).mpr idealPrefix.1,
    (speicher_bezug bezugCut).mpr idealPrefix.2⟩

variable {Ort Wert Wahl : Type}

/-- A matched trace keeps the event; a private or idle trace cannot carry a protocol choice. -/
private theorem spurIdeal {K J : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (h : I.SpurAbgleich K J) {w spur} (konkret : K = some (w, spur))
    (wahl : ProtokollB8Wahl w) : J = some (w, spur) := by
  cases h with
  | pause => cases konkret
  | privat c w' =>
    cases w with
    | kontext c' w'' => exact False.elim wahl
    | antwort a => simp at konkret
    | interrupt id => simp at konkret
    | absturz => simp at konkret
  | schritt event => exact konkret

/-- The protocol duty: answers, interrupts and crashes match the ideal step at the same
    tick, so the checker row's bounds transfer back to the implementation post-state. -/
theorem schrankenProtokollAusLokal : schrankenProtokollAusLokalAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E pflicht simulation h ρ lauf t w spur
    vor nach vorEq labelEq wahl nachEq konkret stapelVor speicherVor
  obtain ⟨η, idealLauf, sim⟩ := simulation lauf
  obtain ⟨_, abgleich, _⟩ := sim
  have idealPrefix := schranken_prefix_aus_lokal pflicht idealLauf t
  have idealSpur : η.zeit.spur t = some (w, spur) :=
    spurIdeal (abgleich.spur t) labelEq wahl
  have idealNach : StapelZustand E (η.zeit.zustand (t + 1)) ∧
      SpeicherZustand E (η.zeit.zustand (t + 1)) := by
    cases η.zeit.takt t with
    | wartet no gleich ruhe => cases no.symm.trans idealSpur
    | schritt label step =>
      have evEq := Option.some.inj (label.symm.trans idealSpur)
      rw [evEq] at step
      cases step with
      | kontext normal bereit regel aus => exact False.elim wahl
      | antwort normal step =>
        exact pflicht.protokoll idealLauf t _ _ _ _ rfl idealSpur trivial rfl
          (.antwort normal step) idealPrefix.1 idealPrefix.2
      | interrupt normal step =>
        exact pflicht.protokoll idealLauf t _ _ _ _ rfl idealSpur trivial rfl
          (.interrupt normal step) idealPrefix.1 idealPrefix.2
      | absturz step =>
        exact pflicht.protokoll idealLauf t _ _ _ _ rfl idealSpur trivial rfl
          (.absturz step) idealPrefix.1 idealPrefix.2
  obtain ⟨sN, cutN, bezugN⟩ := abgleich.zustand (t + 1)
  have eqN : sN = nach := Option.some.inj (cutN.symm.trans nachEq)
  subst sN
  exact ⟨(stapel_bezug pflicht.bezug bezugN).mpr idealNach.1,
    (speicher_bezug bezugN).mpr idealNach.2⟩

end Gabbro.Core.Beobachtung
