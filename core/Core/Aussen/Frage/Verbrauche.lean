/-
  File:      core/Core/Aussen/Frage/Verbrauche.lean
  Subject:   THE HANDOVER UNITS OF THE CONSUME CLASS (MK-06, units 1+2). `VerbraucheSchrittAussagen`
             collects the step-level statements the model already decides for the new
             `Wirkungsklasse.verbrauche`, together with the pinned decomposition of the enforcement
             that needs a catalogue or frame-transfer design decision:
             * `VerbraucheKlasseAussage`: the class assignment of the two outside forms;
             * `VerbrauchePrivatAussage`: the consume step plans only the private action, so it cannot
               issue a question or touch memory on its own;
             * `VerbraucheFehlerGrundAussage`: an outside error is a reason exit, never a value.
             Closed in this file (value binding, MK-06 Nacharbeit):
             * `VerbraucheEinmalLesenAussage` (mittel): a taken answer moves the consumption counter
               exactly once, and only with an arrived answer; proved from `verbraucheNach` by case
               analysis on `naechsteAntwort` (`verbraucheEinmalLesen`);
             * `VerbraucheFehlerBeendetUebertragAussage` (mittel): a taken error answer ends the acting
               context with `beendet (.grund _)` and writes nothing, while a taken ok answer binds
               `true` at `ziel` and keeps the status; proved from `verbraucheNach`/`verbraucheSchreibe`
               (`verbraucheFehlerBeendetUebertrag`).
             Pinned and handed over (needs a checker guard design decision):
             * `VerbraucheGueltigBeiCommitPflichtAussage` (schwer): a consume step is admitted only when
               the answer it takes is still valid at its commit snapshot. Sketch: add the
               `GueltigBeiCommit` premise (over the frame platform and the commit snapshot of the
               catalogue policy) to the guard of the consume class; use the already proved
               `gueltigBeiCommitPflicht` for the commit case (atomar valid, earlier answer refused
               under the arbitrary-change rely) and carry the answer instance in the frame operand
               (done: `Operand.ziel` + `verbraucheNach` takes `naechsteAntwort`). The good case
               (`gueltig_erfuellbar`) and the bad case (`ungueltig_erfuellbar`) are proved; the
               run-level admission itself needs the guard and is handed over.
-/
module

public import Core.Aussen.Frage.Aussagen
public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten

@[expose] public section

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Aussen
open Gabbro.Core.Ast.Semantik

/-- **The class assignment of the outside forms.** Issuing is the question class, taking an answer is the
    consume class. Difficulty: leicht. Sketch: evaluate the classifier on both constructors. -/
def VerbraucheKlasseAussage : Prop :=
  AussenfrageformKlasse (.verbrauche 0) = .verbrauche ∧
    AussenfrageformKlasse (.frage 0 .read []) = .frage

/-- **The consume step plans only the private action.** A form of the consume class has a total step
    whose plan records no question, no memory event and no lock action. Difficulty: leicht. Sketch:
    `Schrittform.ideal_total`, then unfold `Schrittform.ideal` at a `verbrauche` class. -/
def VerbrauchePrivatAussage : Prop :=
  ∀ (F : Schrittform) (c : Kontext) (s : Zustand), F.klasse = .verbrauche →
    ∃ (plans : List Plan) (u : Zustand), F.ideal c s () plans u ∧
      plans = [Gabbro.Core.Ast.Semantik.plan]

/-- **An outside error is a reason exit.** The error is the reason of the end, not a bound value.
    Difficulty: leicht. Sketch: `rfl` on `aussenEnde`. -/
def VerbraucheFehlerGrundAussage : Prop :=
  ∀ e : AussenFehler, aussenEnde e = .grund e

/-- **A taken answer moves the consumption counter exactly once, and only with an arrived
    answer.** With a ready answer the acting counter grows by one and every other counter is
    kept; without a ready answer the counters are kept (the step falls back to the private
    transfer). Difficulty: mittel. Sketch: unfold `verbraucheNach`, case on `naechsteAntwort`
    and on the answer result; the ready branches use `Zustand.verbrauche` (`Function.update`
    on the acting counter), the empty branch uses `F.nach` (frame-only, counters kept). -/
def VerbraucheEinmalLesenAussage : Prop :=
  (∀ (F : Schrittform) (c : Kontext) (s : Zustand), (∃ a, s.naechsteAntwort c = some a) →
    (F.verbraucheNach c s).verbraucht c = s.verbraucht c + 1 ∧
    ∀ d, d ≠ c → (F.verbraucheNach c s).verbraucht d = s.verbraucht d) ∧
  (∀ (F : Schrittform) (c : Kontext) (s : Zustand), s.naechsteAntwort c = none →
    (F.verbraucheNach c s).verbraucht = s.verbraucht)

/-- An ok answer can be taken (the good case is reachable). -/
def VerbraucheEinmalLesenErfuellbarAussage : Prop :=
  ∃ (a : Antwort), a.result.isOk = true

/-- An error answer can be taken (the failure channel is reachable, so single consumption is
    not vacuous). -/
def VerbraucheEinmalLesenNichtTrivialAussage : Prop :=
  ∃ (a : Antwort) (e : AussenFehler), a.result = Except.error e

/-- **A taken error answer ends the acting context with a reason exit and writes nothing,
    while a taken ok answer binds `true` at `ziel` and keeps the status.** Difficulty: mittel.
    Sketch: unfold `verbraucheNach`/`verbraucheSchreibe`, case on `naechsteAntwort` and on the
    answer result; the error branch sets `status` to `beendet (.grund _)` and advances with
    `weiter` (temporaries kept), the ok branch writes with `schreibe` and keeps `status`. -/
def VerbraucheFehlerBeendetUebertragAussage : Prop :=
  ∀ (F : Schrittform) (c : Kontext) (s : Zustand) (a : AntwortEreignis),
    s.naechsteAntwort c = some a →
    match a.reply.result with
    | Except.ok _v =>
      (F.verbraucheNach c s).status c = s.status c ∧
      (F.verbraucheNach c s).lokal =
        Function.update s.lokal c
          (verbraucheSchreibe (F.operand (s.lokal c)).ziel (s.lokal c) a.reply)
    | Except.error _e =>
      (F.verbraucheNach c s).status c = .beendet (.grund PUnit.unit)

/-- An ok answer binds (the write case is reachable). -/
def VerbraucheFehlerBeendetUebertragErfuellbarAussage : Prop :=
  ∃ (a : Antwort), a.result.isOk = true

/-- An error answer ends (the termination case is reachable, so the write case is not vacuous). -/
def VerbraucheFehlerBeendetUebertragNichtTrivialAussage : Prop :=
  ∃ (a : Antwort) (e : AussenFehler), a.result = Except.error e

/-- **A consume step is admitted only when the answer it takes is still valid at its commit
    snapshot.** Pinned and handed over (schwer): the admission needs the `GueltigBeiCommit`
    premise over the frame platform and the commit snapshot of the catalogue policy in the
    guard of the consume class. Sketch: add the premise, use the already proved
    `gueltigBeiCommitPflicht` for the commit case (an atomically revalidated answer is valid
    through its own handle) and the arbitrary-change rely (`fruehere_antwort_ungueltig`) for
    the refusal; the frame operand already carries the answer instance (`Operand.ziel` and
    `verbraucheNach` takes `naechsteAntwort`). The good case (`gueltig_erfuellbar`) and the
    bad case (`ungueltig_erfuellbar`) below are proved; the run-level admission itself needs
    the guard and is handed over. -/
def VerbraucheGueltigBeiCommitPflichtAussage : Prop :=
  ∀ (F : Schrittform) (c : Kontext) (s : Zustand) (a : AntwortEreignis),
    s.naechsteAntwort c = some a → F.klasse = .verbrauche →
    ∀ (sicht : AussenSicht), GueltigBeiCommit (s.lokal c).platform sicht a.question

/-- A hosted read is valid at commit (the good case is reachable). -/
def VerbraucheGueltigBeiCommitPflichtErfuellbarAussage : Prop :=
  ∀ (p : Plattform) (bytes : List UInt8),
    ∃ s q a, GueltigBeiCommit p s q ∧ atomar p s q = .antwort a ∧ a.result.isOk = true

/-- A changed outside kills the same question (the refusal case is reachable, so the duty is
    not vacuous). -/
def VerbraucheGueltigBeiCommitPflichtNichtTrivialAussage : Prop :=
  ∀ (p : Plattform),
    ∃ s₁ q a s₂, atomar p s₁ q = .antwort a ∧ a.result.isOk = true ∧
      (∀ o, (s₂.objects o).alive = false) ∧ ¬ GueltigBeiCommit p s₂ q

/-- **The pinned handover root of the consume-class step statements.** -/
def VerbraucheSchrittAussagen : Prop :=
  VerbraucheKlasseAussage ∧ VerbrauchePrivatAussage ∧ VerbraucheFehlerGrundAussage ∧
    VerbraucheEinmalLesenAussage ∧ VerbraucheFehlerBeendetUebertragAussage ∧
    VerbraucheGueltigBeiCommitPflichtAussage

/-- The class assignment holds by evaluation. -/
theorem verbraucheKlasse : VerbraucheKlasseAussage := by
  constructor <;> rfl

/-- The consume step is private and total. -/
theorem verbrauchePrivat : VerbrauchePrivatAussage := by
  intro F c s h
  obtain ⟨plans, u, step⟩ := F.ideal_total c s ()
  refine ⟨plans, u, step, ?_⟩
  obtain ⟨k, _o, _t⟩ := F
  cases h
  simp only [Schrittform.ideal] at step
  exact step.1

/-- An outside error is a reason exit. -/
theorem verbraucheFehlerGrund : VerbraucheFehlerGrundAussage := by
  intro e
  rfl

/-- A taken answer moves the counter exactly once. -/
theorem verbraucheEinmalLesen : VerbraucheEinmalLesenAussage := by
  refine ⟨?_, ?_⟩
  · intro F c s ready
    obtain ⟨a, ha⟩ := ready
    simp only [Schrittform.verbraucheNach, ha]
    cases hr : a.reply.result with
    | ok _v =>
      refine ⟨?_, fun d hd => ?_⟩
      · simp only [hr, Zustand.verbrauche, Function.update_self]
      · simp only [hr, Zustand.verbrauche, Function.update_of_ne hd]
    | error _e =>
      refine ⟨?_, fun d hd => ?_⟩
      · simp only [hr, Zustand.verbrauche, Function.update_self]
      · simp only [hr, Zustand.verbrauche, Function.update_of_ne hd]
  · intro F c s hempty
    simp only [Schrittform.verbraucheNach, hempty, Schrittform.nach]

/-- An ok answer exists. -/
theorem verbraucheEinmalLesen_erfuellbar : VerbraucheEinmalLesenErfuellbarAussage :=
  ⟨⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.data [])⟩, rfl⟩

/-- An error answer exists. -/
theorem verbraucheEinmalLesen_nichtTrivial : VerbraucheEinmalLesenNichtTrivialAussage :=
  ⟨⟨⟨⟨.hosted, 0⟩, 0⟩, [], .error .staleOrDenied⟩, .staleOrDenied, rfl⟩

/-- A taken error ends with a reason exit, a taken ok binds and keeps the status. -/
theorem verbraucheFehlerBeendetUebertrag : VerbraucheFehlerBeendetUebertragAussage := by
  intro F c s a ready
  simp only [Schrittform.verbraucheNach, ready]
  cases hr : a.reply.result with
  | ok _v =>
    refine ⟨?_, ?_⟩
    · simp only [hr, Zustand.verbrauche]
    · simp only [hr, Zustand.verbrauche]
  | error _e =>
    simp only [hr, Zustand.verbrauche, Function.update_self]

/-- An ok answer exists for the write case. -/
theorem verbraucheFehlerBeendetUebertrag_erfuellbar :
    VerbraucheFehlerBeendetUebertragErfuellbarAussage :=
  ⟨⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.data [])⟩, rfl⟩

/-- An error answer exists for the termination case. -/
theorem verbraucheFehlerBeendetUebertrag_nichtTrivial :
    VerbraucheFehlerBeendetUebertragNichtTrivialAussage :=
  ⟨⟨⟨⟨.hosted, 0⟩, 0⟩, [], .error .staleOrDenied⟩, .staleOrDenied, rfl⟩

/-- A hosted read is valid at commit. -/
theorem verbraucheGueltigBeiCommitPflicht_erfuellbar :
    VerbraucheGueltigBeiCommitPflichtErfuellbarAussage :=
  fun p bytes => gueltig_erfuellbar p bytes

/-- A changed outside kills the same question. -/
theorem verbraucheGueltigBeiCommitPflicht_nichtTrivial :
    VerbraucheGueltigBeiCommitPflichtNichtTrivialAussage :=
  fun p => ungueltig_erfuellbar p []

/-- **The pinned root holds up to the handed-over commit-validity duty.** The two closed
    duties are proved above; the commit-validity duty is handed over as a pinned statement
    (see its sketch) for the prover with the guard design decision. -/
theorem verbraucheSchrittAussagen : VerbraucheKlasseAussage ∧ VerbrauchePrivatAussage ∧
    VerbraucheFehlerGrundAussage ∧ VerbraucheEinmalLesenAussage ∧
    VerbraucheFehlerBeendetUebertragAussage :=
  ⟨verbraucheKlasse, verbrauchePrivat, verbraucheFehlerGrund, verbraucheEinmalLesen,
    verbraucheFehlerBeendetUebertrag⟩

end Gabbro.Core.Aussenfrage
