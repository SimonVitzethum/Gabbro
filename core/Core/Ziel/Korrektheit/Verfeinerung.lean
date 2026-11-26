/-
  File:      core/Core/Ziel/Korrektheit/Verfeinerung.lean
  Subject:   CORRECTNESS OF THE RELATION IMPLEMENTATION ⊑ `I` (M7, M8): refinement, today's guarantee and progress
             for EVERY accepted elaborated unit, and the statements that make the form duties falsifiable.

  The refinement theorem is stated for every accepted source unit, not for a free frame: its premises are the
  acceptance of `einheitVon P t` and a run of it, and its conclusion the existence of one ideal run that matches.
  For the current instruction set it is a theorem (`verfeinerung_akzeptiert`, from `sim_elaborierter_lauf` and
  the class theorem `klassenSim`); the finding that goes with it is in the docstring of
  `RegelSimDiskriminiertAussage`: every instruction an elaborated source unit contains is frame-only
  (`Befehl.Privat`), its rule is the template `impl ≡ ideal` of the classes `lokal` and `ruf`, so the theorem is
  TRUE BUT NOT YET INFORMATIVE about memory, locks, questions or threads: the source forms of those classes enter
  the grammar later. Since MK-04 `Befehl` HAS instructions of the classes `lesen`, `schreiben` and `rmw`
  (`Befehl.zugriff`, `Runtime/Atom/Form`); the generic proofs split on the class (`Befehl.Privat` for the frame-only
  part, the class theorems for the rest), and the kernel statements of the access instructions are pinned under
  `AtomAussagen`.
  The classes themselves exist (MK-03): they carry real plans that depend on the frame (`Wirkungsklasse.plan`),
  an authority guard with refusal, and a booked ledger entry, their duties are stated once per class
  (`KlassenAussagen`) and are informative (`klassenNichtTrivial`: dropping the guard breaks locality). The next
  instruction of a class (MK-05, MK-06) is a constructor of `Befehl` (or a form of `Zugriffsform`), a class
  assignment and its frame operand and transfer. The refutability statement below is the guard against pinning a
  duty that no unit can violate.

  The three former family statements `FlushSimAussage`, `LockFreeSimAussage` and `StotterMassAussage`
  of `Verfeinerung/Abnahme` took free function parameters (decoder, abstract specification, mass) with no
  binding to the unit: a degenerate choice proved each for every unit. D-K3 closes this. The decoder,
  together with family membership and, for lock-free, the abstraction function, its start and its abstract
  specification, is declared data of the family's unit wrapper (`FlushEinheit`, `LockFreeEinheit`); the
  lock-free sequential history is derived by theorem from an abstraction faithfulness duty, so linearisability
  is proved and not an obligation; the stutter duty is the per-rule `RegelStotterSchranke`, with the mass an
  internal proof device. Each family statement records a satisfiable and a refutable case next to it; the old
  free-parameter forms are deleted.
-/
module

public import Core.Ziel.Korrektheit.Maschine
public import Core.Verfeinerung.Formen.Abdeckung
public import Core.Verfeinerung.Fortschritt
public import Core.Maschine.Start

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
  exact Ast.Semantik.sim_elaborierter_lauf
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
      (Ast.Semantik.sim_formen (Ast.Semantik.fragment Ast.Category.unit t) P)
  exact pflicht.zielFX lauf k

/-- PROGRESS FOR EVERY ACCEPTED ELABORATED UNIT on a hardware-fair history, under the two run
premises of the progress leg: the matched ideal run exists, no context hangs, and the per-cut
progress alternatives hold. Feeds: `sim_ziel_fortschritt_im_lauf`, `Laufabgleich.fortschritt`,
`deadlockfrei_aus_waechter`. The premises are `Maschine.SchedulerFair` (a continuously
dispatched, live and rule-enabled context with infinitely many opportunities on its dispatch
core is stepped infinitely often) and `Maschine.VerdraengungKehrtZurueck` (a live context
displaced by an interrupt is dispatched again at a strictly later cut); both are properties of
the execution model, not catalogue rows, and both are owner-approved (MK-11 decisions 1 and 2).
Proved for the current instruction set in `Beweise/Fortschritt/SchedulerEinheit.lean`. -/
def FortschrittAkzeptiertAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ → Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw →
      Maschine.SchedulerFair (einheitVon P t) ρ →
      Maschine.VerdraengungKehrtZurueck (einheitVon P t) ρ →
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
