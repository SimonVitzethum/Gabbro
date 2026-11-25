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
             Open proof units (handed over, not closed here):
             * `VerbraucheGueltigBeiCommitPflicht` (schwer): a consume step is admitted only when the
               answer it takes is still valid at its commit snapshot. Sketch: add the
               `GueltigBeiCommit` premise to the guard of the consume class, use the already proved
               `gueltigBeiCommitPflicht` for the commit case and the arbitrary-change rely for the
               refusal; needs the frame operand to carry the answer instance.
             * `VerbraucheEinmalLesen` (mittel): one outside object is fetched by one atomic question
               and the answer is consumed once. Sketch: book the question instance in the ledger and
               use `FrageSimAussage` plus `verbrauche_verbrauch` for the single consumption counter.
             * `VerbraucheFehlerBeendetUebertrag` (mittel): wire `aussenEnde` into the frame transfer so
               that a taken error answer leaves the acting context at `.beendet (.grund e)`. Sketch:
               case the answer's result in the consume transfer and write the status as the lifecycle
               classes do; needs the value binding of an answer into a frame slot.
-/
module

public import Core.Aussen.Frage.Aussagen
public import Core.Ast.Semantik.Runtime.Klasse.Schritt

@[expose] public section

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
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
    ∃ (plans : List Plan) (u : Zustand), F.ideal c s () plans u ∧ plans = [Semantik.plan]

/-- **An outside error is a reason exit.** The error is the reason of the end, not a bound value.
    Difficulty: leicht. Sketch: `rfl` on `aussenEnde`. -/
def VerbraucheFehlerGrundAussage : Prop :=
  ∀ e : AussenFehler, aussenEnde e = .grund e

/-- **The pinned handover root of the consume-class step statements.** -/
def VerbraucheSchrittAussagen : Prop :=
  VerbraucheKlasseAussage ∧ VerbrauchePrivatAussage ∧ VerbraucheFehlerGrundAussage

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
  exact step.1

/-- An outside error is a reason exit. -/
theorem verbraucheFehlerGrund : VerbraucheFehlerGrundAussage := by
  intro e
  rfl

/-- **The pinned root holds.** -/
theorem verbraucheSchrittAussagen : VerbraucheSchrittAussagen :=
  ⟨verbraucheKlasse, verbrauchePrivat, verbraucheFehlerGrund⟩

end Gabbro.Core.Aussenfrage
