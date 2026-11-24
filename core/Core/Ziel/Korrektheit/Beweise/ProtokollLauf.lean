/-
  File:      core/Core/Ziel/Korrektheit/Beweise/ProtokollLauf.lean
  Subject:   THE PROTOCOL INVARIANTS HOLD AT THE START AND AT EVERY CUT OF BOTH MACHINES. This file proves the
             start and run statements pinned in `Core/Ziel/Korrektheit/Maschine.lean`; the step preservation
             statement is taken as a hypothesis proved by another agent.

  The loaded start is proved by unfolding `Ast.Semantik.laden`: a successful load is exactly a
  `Maschine.Zustand.start`, whose invariants come from `Zustand.start_gut` (memory and consumption) and from
  the empty ticket queue of `SperrZustand.frei`. The run statements then follow by induction over the hardware
  ticks of the `Zeitlauf`, as in `Core/Ideal/Komposition.lean`'s `speicher_gut_im_lauf`: a step is handed to
  `ProtokollSchrittErhaeltAussage` with the invariant of the preceding state, a pause keeps that state. The
  implementation run stores its states as `Option Zustand`, so its induction additionally shows that a cut
  with a loaded successor has a loaded predecessor (the implementation step relation has no transition from
  `none`); the ideal run stores states directly and needs no such case.
-/
module

public import Core.Ziel.Korrektheit.Maschine

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine

/-- A start state satisfies the protocol invariants. Feeds: `Zustand.start_gut` (consistent complete graph and
    consumption of a fresh state) and `SperrZustand.frei` (an empty, duplicate-free queue with no owner).
    Kept separate from the loader so both machines can use it at their initial cut. -/
theorem zustand_start_protokoll_gut
    (lok : Kontext → Ast.Semantik.Rahmen) (st : Kontext → Status Int PUnit)
    (kerne : Kern → KernZustand Nat) (r : Rechte)
    (initial : Ast.Semantik.Zelle → Int) (medium : Katalog.PersistZustand)
    (k : Katalog.Katalog) (sicht : Nat → Katalog.AussenSicht) :
    ProtokollGut (Zustand.start (L := Nat) (Ort := Ast.Semantik.Zelle) (Wert := Int)
      (Raum := Nat) (Lok := Ast.Semantik.Rahmen) (Grund := PUnit)
      lok st kerne r initial medium) := by
  have g := Zustand.start_gut (L := Nat) (Ort := Ast.Semantik.Zelle) (Wert := Int)
    (Raum := Nat) (Lok := Ast.Semantik.Rahmen) (Grund := PUnit)
    lok st kerne r initial medium k sicht
  refine ⟨g.1, g.2.1, ?_⟩
  intro l
  change ([] : List Kontext).Nodup ∧ ∀ c : Kontext, none = some c → c ∉ ([] : List Kontext)
  exact ⟨List.nodup_nil, fun c hc => by cases hc⟩

/-- THE LOADED START SATISFIES THE INVARIANTS (`ProtokollStartGutAussage`). Feeds:
    `zustand_start_protokoll_gut`, `Ast.Semantik.laden`, `Ast.Semantik.Fragment.einheit`. Proof sketch: unfold
    the elaborated loader; a successful load has a condition that selects the `Zustand.start` branch, so the
    loaded state is a start state; a failed load cannot equal `some z`. -/
theorem protokoll_start_gut : ProtokollStartGutAussage := by
  intro P t H s z loaded
  simp only [einheitVon, Ast.Semantik.elaborieren, Ast.Semantik.Fragment.einheit] at loaded
  unfold Ast.Semantik.laden at loaded
  split at loaded
  · cases loaded
    exact zustand_start_protokoll_gut _ _ _ _ _ _ (einheitVon P t).katalog
      (fun n => H.politik.sicht n [])
  · cases loaded

/-- THE INVARIANTS HOLD AT EVERY CUT OF EVERY IMPLEMENTATION RUN (`ProtokollGutImLaufAussage`), given the step
    preservation statement. Feeds: `protokoll_start_gut`, `ProtokollSchrittErhaeltAussage`,
    `speicher_gut_im_lauf` (the induction shape). Proof sketch: induction over the ticks; at the initial cut use
    the loader equation of `Laeufe`; at a step, cases of `Lauffolge` give a loaded predecessor and an
    `ImplSchritt`, to which the step premise applies; at a pause the state is unchanged. -/
theorem protokoll_gut_im_lauf_aus (h : ProtokollSchrittErhaeltAussage) : ProtokollGutImLaufAussage := by
  intro P t H ρ lauf n
  induction n with
  | zero =>
      intro z atCut
      have loaded : (einheitVon P t).laden ρ.start (H.lade (einheitVon P t).bild) = some z := by
        rw [← atCut]
        exact lauf.2.2.2.symm
      exact protokoll_start_gut P t H ρ.start z loaded
  | succ n ih =>
      intro z atCut
      cases current : ρ.zeit.zustand n with
      | none =>
          have tick := ρ.zeit.takt n
          rw [current] at tick
          cases tick with
          | schritt _ step => cases step
          | wartet _ eq _pause =>
              rw [eq] at atCut
              cases atCut
      | some s =>
          have vorher : ProtokollGut s := ih s current
          have tick := ρ.zeit.takt n
          rw [current] at tick
          rw [atCut] at tick
          cases tick with
          | schritt _ step =>
              rename_i event
              cases step with
              | schritt impl =>
                  have pres := h _ _ _ _ _ _ _ _ _
                    (einheitVon P t).einrichtung (einheitVon P t).system
                    (einheitVon P t).katalog ρ.hw n s z event vorher
                  exact pres.1 impl
          | wartet _ eq _pause =>
              exact ih z (current.trans eq.symm)

/-- THE INVARIANTS HOLD AT EVERY CUT OF EVERY IDEAL RUN (`IdealProtokollGutImLaufAussage`), given the same step
    preservation statement. Feeds: `zustand_start_protokoll_gut`, `Maschine.I.start`,
    `ProtokollSchrittErhaeltAussage`. Proof sketch: the same induction over the ticks; the initial state is the
    canonical `I.start`, and an ideal step is discharged by the second conjunct of the step premise. -/
theorem ideal_protokoll_gut_im_lauf_aus (h : ProtokollSchrittErhaeltAussage) :
    IdealProtokollGutImLaufAussage := by
  intro P t η lauf n
  induction n with
  | zero =>
      rw [lauf.2.2.2.1]
      change ProtokollGut (Zustand.start _ _ _ _ _ _)
      exact zustand_start_protokoll_gut _ _ _ _ _ _ (einheitVon P t).katalog
        (fun m => η.umgebung.politik.sicht m [])
  | succ n ih =>
      cases η.zeit.takt n with
      | schritt _ step =>
          rename_i event
          have pres := h _ _ _ _ _ _ _ _ _
            (einheitVon P t).einrichtung (einheitVon P t).system
            (einheitVon P t).katalog η.hw n (η.zeit.zustand n) (η.zeit.zustand (n + 1)) event ih
          exact pres.2 step
      | wartet _ eq _pause =>
          rw [eq]
          exact ih

end Gabbro.Core.Ziel.Korrektheit
