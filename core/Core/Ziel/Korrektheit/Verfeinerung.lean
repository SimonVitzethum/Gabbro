/-
  File:      core/Core/Ziel/Korrektheit/Verfeinerung.lean
  Subject:   CORRECTNESS OF THE RELATION IMPLEMENTATION ⊑ `I` (M7, M8): refinement, today's guarantee and progress
             for EVERY accepted elaborated unit, and the statements that make the form duties falsifiable.

  The refinement theorem is stated for every accepted source unit, not for a free frame: its premises are the
  acceptance of `einheitVon P t` and a run of it, and its conclusion the existence of one ideal run that matches.
  For the current instruction set it is a theorem (`verfeinerung_akzeptiert`, from `sim_elaborierter_lauf` and
  `klassenSim`); the finding that goes with it is in the docstring of `RegelSimDiskriminiertAussage`: every form
  duty of the current set is proved by the shared template `Befehl.impl ≡ Befehl.ideal` with stutter bound zero, so
  the theorem is TRUE BUT NOT YET INFORMATIVE about memory, locks, questions or threads — those instructions do not
  exist in `Befehl` yet (MK-03, MK-04, MK-05). The refutability statement below is the guard against pinning a
  duty that no unit can violate.

  The three family statements `FlushSimAussage`, `LockFreeSimAussage` and `StotterMassAussage` of
  `Verfeinerung/Abnahme` take free function parameters (decoder, abstract specification, mass) with no binding to
  the unit: for each, a degenerate choice proves it for every unit (`Verfeinerung/Review/Befunde.lean`). The
  design that binds them (diff D-K3 in the report) puts the decoder in the UNIT (`Einrichtung.sicht`), derives the
  sequential history of a lock-free family from a faithful abstraction function (so linearisability is a theorem,
  not an obligation), and states the stutter duty as `RegelStotterSchranke` (the mass is a proof device). Until
  those forms enter the model the three statements must not be relied upon; they are not restated here.
-/
module

public import Core.Ziel.Korrektheit.Maschine
public import Core.Verfeinerung.Formen.Abdeckung
public import Core.Verfeinerung.Fortschritt

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine

/-- REFINEMENT FOR EVERY ACCEPTED ELABORATED UNIT: every maximal implementation run has ONE ideal run whose
state-and-step simulation holds on the whole run (matching effects, authority on every tick, stutter bound,
monotone cut map, both runs covered). Feeds: `sim_elaborierter_lauf`, `sim_akzeptierter_lauf`, `sim_im_lauf`,
`klassenSim`, `Fragment.simBasis`. Proved for the current instruction set. -/
def VerfeinerungAkzeptiertAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      ∃ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η ∧ Maschine.I.Sim (einheitVon P t) ρ η

theorem verfeinerung_akzeptiert : VerfeinerungAkzeptiertAussage := by
  intro P t akzeptiert H ρ lauf
  exact Ast.Semantik.sim_elaborierter_lauf (Ast.Semantik.klassenSim Ast.Semantik.Wirkungsklasse.lokal)
    (Ast.Semantik.klassenSim Ast.Semantik.Wirkungsklasse.ruf)
    (Ast.Semantik.elab_korrekt P (category := Ast.Category.unit) t) akzeptiert lauf

/-- TODAY'S GUARANTEE ON EVERY CUT OF EVERY RUN of an accepted elaborated unit: at every cut the loaded state
holds a consistent complete memory, consumption never exceeds arrival, every earlier access was authorised when it
occurred, and the outcomes come from the typed status or the recorded catalogue events (`ZielFX`). Proved for the
current instruction set from the simulation duties. -/
def ZielFXAkzeptiertAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      ∀ k : Maschine.Schnitt (einheitVon P t) ρ, Maschine.ZielFX (einheitVon P t) H ρ k

theorem zielFX_akzeptiert : ZielFXAkzeptiertAussage := by
  intro P t _ H ρ lauf k
  have pflicht : Maschine.I.SimPflichten (einheitVon P t) :=
    (Ast.Semantik.Fragment.simBasis (Ast.Semantik.fragment Ast.Category.unit t) P).mit_formen
      (Ast.Semantik.sim_formen (Ast.Semantik.klassenSim Ast.Semantik.Wirkungsklasse.lokal)
        (Ast.Semantik.klassenSim Ast.Semantik.Wirkungsklasse.ruf)
        (Ast.Semantik.fragment Ast.Category.unit t) P)
  exact pflicht.zielFX lauf k

/-- PROGRESS FOR EVERY ACCEPTED ELABORATED UNIT on a hardware-fair history: the matched ideal run exists, no
context hangs, and the per-cut progress alternatives hold. Feeds: `sim_ziel_fortschritt_im_lauf`,
`Laufabgleich.fortschritt`, `deadlockfrei_aus_waechter`. Open: `FortschrittsPflichten` for the elaborated unit
(`angebot`, `wahl`, `individuell`, `systemweit`: the dispatch and selection duties of the hardware-fair scheduler
over `Fortschritt/Verzoegerung` and `Verhungern`) — M8 (Prover, after the scheduler duties are stated for
`einheitVon`). -/
def FortschrittAkzeptiertAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ → Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw →
      ∃ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η ∧ Maschine.I.Sim (einheitVon P t) ρ η ∧
        (∀ c, ¬ Maschine.I.Haengt (einheitVon P t) ρ η c) ∧
        Maschine.I.FortschrittDerKlasse
          (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl) η

/-- THE FORM DUTY IS FALSIFIABLE: some unit has a rule whose implementation step the ideal rule does not allow,
and for it the per-form simulation duty `RegelSimSchritt` is false. Without this statement a duty proved by the
template `impl ≡ ideal` (as every duty of the current instruction set is, `klassenSim`) cannot be told from a
vacuous one: here the same duty fails for a rule whose two sides differ, so its truth for the elaborated forms
says that their two sides agree. Feeds: `RegelSimSchritt`, `RegelAbgleich`, `Zustandsbezug`. Open: the witness
unit (Prover). -/
def RegelSimDiskriminiertAussage : Prop :=
  ∃ (E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (f : Unit),
    ¬ Maschine.I.RegelSimSchritt E f

/-- THE SIMULATION SEPARATES IDEAL RUNS: for some unit and some implementation run, one ideal run matches and
another ideal run of the same unit does not. If every ideal run matched, `Sim` would only assert that an ideal
run exists and the matching would carry no information. Feeds: `Sim`, `Laufabgleich`, `nicht_sim_bei_stotterueberlauf`.
Open: the witness (Prover). -/
def SimTrenntAussage : Prop :=
  ∃ (E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (ρ : Maschine.Lauf E)
    (η₁ η₂ : Maschine.I.Lauf E),
    Maschine.I.Laeufe E η₁ ∧ Maschine.I.Sim E ρ η₁ ∧ Maschine.I.Laeufe E η₂ ∧ ¬ Maschine.I.Sim E ρ η₂

/-- THE REFINEMENT HAS NO UNIT THAT ESCAPES IT, in the refusal direction: some unit has an implementation run
that no ideal run matches (the model refuses the unit; it cannot be accepted). This is the statement that
`VerfeinerungAkzeptiertAussage` needs its premise `Akzeptiert`: without refutable units the premise would be
decoration. Feeds: `nicht_sim_bei_stotterueberlauf`, `Akzeptiert`'s refusal examples. Open: the witness (Prover). -/
def SimRefutierbarAussage : Prop :=
  ∃ (E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (H : Katalog.Umgebung)
    (ρ : Maschine.Lauf E), Maschine.Laeufe E H ρ ∧
      ∀ η : Maschine.I.Lauf E, Maschine.I.Laeufe E η → ¬ Maschine.I.Sim E ρ η

end Gabbro.Core.Ziel.Korrektheit
