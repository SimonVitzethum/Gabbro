/-
  File:      core/Core/Aussen/Frage/Verbrauche.lean
  Subject:   THE HANDOVER UNITS OF THE CONSUME CLASS (MK-06, units 1+2, Nacharbeit).
              `VerbraucheSchrittAussagen` collects the step-level statements the model decides.
              The value of an ok answer is bound by the declared return kind of the catalogue row
              (`RueckgabeArt`, `Antwort.uebersetzt`), not by a success constant; an answer of another
              kind or an error answer ends the context with a reason exit. The consume guard takes
              an answer only when it still carries its commit revalidation evidence
              (`AntwortEreignis.gueltigBeiCommit`, bound over `ReihenStabil`); an invalid answer is
              refused with a named halt and is not consumed.

              Closed here:
              * `VerbraucheKlasseAussage`, `VerbrauchePrivatAussage`, `VerbraucheFehlerGrundAussage`;
              * `VerbraucheEinmalLesenAussage` (mittel): a valid answer moves the counter once, an
                invalid answer not at all;
              * `VerbraucheFehlerBeendetUebertragAussage` (mittel): a fitting ok answer writes exactly
                its translated value and keeps the status; an untranslatable answer ends with
                `beendet (.grund _)`;
              * `VerbraucheGueltigBeiCommitPflichtAussage` (mittel): an atomic ok answer is valid at
                its commit and carries that evidence, an arbitrary change outside the stable objects
                destroys it, and the step refuses an answer without it.

              Satisfiability (`…ErfuellbarAussage`) and non-triviality (`…NichtTrivialAussage`)
              accompany every bundle; all are proved, none by a witness run of a compiler.
-/
module

public import Core.Aussen.Frage.Aussagen
public import Core.Aussen.Frage.Beweise
public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Aussen.Frage.Wert
public import Core.Aussen.Frage.Commit

@[expose] public section

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Aussen
open Gabbro.Core.Ast
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

/-- **A taken answer moves the consumption counter exactly once, and only with an arrived answer
    that still carries its commit evidence.** A valid answer grows the acting counter by one and
    keeps every other counter; an invalid answer is refused and no counter moves; without an arrived
    answer the step falls back to the private transfer. Difficulty: mittel. Sketch: unfold
    `verbraucheNach`, case on `naechsteAntwort` and on `gueltigBeiCommit`. -/
def VerbraucheEinmalLesenAussage : Prop :=
  (∀ (F : Schrittform) (c : Kontext) (s : Zustand) (a : AntwortEreignis),
    s.naechsteAntwort c = some a → AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a →
      (F.verbraucheNach c s).verbraucht c = s.verbraucht c + 1 ∧
      ∀ d, d ≠ c → (F.verbraucheNach c s).verbraucht d = s.verbraucht d) ∧
  (∀ (F : Schrittform) (c : Kontext) (s : Zustand) (a : AntwortEreignis),
    s.naechsteAntwort c = some a → ¬ AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a →
      (F.verbraucheNach c s).verbraucht = s.verbraucht) ∧
  (∀ (F : Schrittform) (c : Kontext) (s : Zustand), s.naechsteAntwort c = none →
    (F.verbraucheNach c s).verbraucht = s.verbraucht)

/-- A commit-valid ok answer is reachable (the single-consumption case is not vacuous). -/
def VerbraucheEinmalLesenErfuellbarAussage : Prop :=
  ∃ (ev : AntwortEreignis) (p : Plattform),
    AntwortEreignis.gueltigBeiCommit p ev ∧ ev.reply.result.isOk = true

/-- An ok answer without commit evidence is reachable (the refusal case is not vacuous). -/
def VerbraucheEinmalLesenNichtTrivialAussage : Prop :=
  ∃ (ev : AntwortEreignis) (p : Plattform),
    ¬ AntwortEreignis.gueltigBeiCommit p ev ∧ ev.reply.result.isOk = true

/-- **A fitting ok answer binds exactly the translated value; an untranslatable answer ends the
    acting context with a reason exit.** With a valid answer the status is kept and the target slot
    holds the value the declared return kind assigns to the answer; an answer that cannot be
    translated ends with `beendet (.grund _)` and writes nothing. Difficulty: mittel. Sketch: unfold
    `verbraucheNach`/`verbraucheSchreibe`, case on the guard and on `Antwort.uebersetzt`. -/
def VerbraucheFehlerBeendetUebertragAussage : Prop :=
  ∀ (F : Schrittform) (c : Kontext) (s : Zustand) (a : AntwortEreignis),
    s.naechsteAntwort c = some a → AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a →
    match Antwort.uebersetzt a.question a.reply with
    | some v =>
      (F.verbraucheNach c s).status c = s.status c ∧
      (F.verbraucheNach c s).lokal =
        Function.update s.lokal c
          (verbraucheSchreibe (F.operand (s.lokal c)).ziel a.question (s.lokal c) a.reply) ∧
      ((F.verbraucheNach c s).lokal c).temp (F.operand (s.lokal c)).ziel = some v
    | none =>
      (F.verbraucheNach c s).status c = .beendet (.grund PUnit.unit) ∧
      (F.verbraucheNach c s).lokal = Function.update s.lokal c ((s.lokal c).weiter)

/-- The matching binding case is jointly satisfiable with the guard. -/
def VerbraucheFehlerBeendetUebertragErfuellbarAussage : Prop :=
  ∃ (ev : AntwortEreignis) (p : Plattform) (v : Dynamisch),
    AntwortEreignis.gueltigBeiCommit p ev ∧ Antwort.uebersetzt ev.question ev.reply = some v

/-- The termination case is jointly satisfiable with the guard: a valid error answer translates
    to nothing, so the write case is not vacuous. -/
def VerbraucheFehlerBeendetUebertragNichtTrivialAussage : Prop :=
  ∃ (ev : AntwortEreignis) (p : Plattform),
    AntwortEreignis.gueltigBeiCommit p ev ∧ Antwort.uebersetzt ev.question ev.reply = none

/-- **A consume step is admitted only for an answer still valid at its commit.** An atomic ok answer
    is valid at its commit snapshot and carries that evidence; a changed outside outside the stable
    objects destroys it; and the step refuses an answer without the evidence with a named halt
    without consuming it. Difficulty: mittel. Sketch: the first two conjuncts come from
    `gueltigBeiCommitPflicht` and the arbitrary-change rely, the third from `commitGueltig_von_atomar`,
    the fourth by unfolding `verbraucheNach`. -/
def VerbraucheGueltigBeiCommitPflichtAussage : Prop :=
  (∀ (p : Plattform) (s : AussenSicht) (q : Frage) (a : Antwort),
    atomar p s q = .antwort a → a.result.isOk = true → GueltigBeiCommit p s q) ∧
  (∀ (p : Plattform) (s : AussenSicht) (q : Frage) (t : Zugriff) (mem : t ∈ q.zugriffe),
    ¬ ReihenStabil p t.handle.origin.object →
    ∃ s₂ : AussenSicht, (∀ o, (s₂.objects o).alive = false) ∧ ¬ GueltigBeiCommit p s₂ q) ∧
  (∀ (p : Plattform) (s : AussenSicht) (q : Frage) (a : Antwort),
    atomar p s q = .antwort a → a.result.isOk = true → Antwort.commitGueltig p q a) ∧
  (∀ (F : Schrittform) (c : Kontext) (s : Zustand) (a : AntwortEreignis),
    s.naechsteAntwort c = some a →
    ¬ AntwortEreignis.gueltigBeiCommit (s.lokal c).platform a →
      (F.verbraucheNach c s).verbraucht = s.verbraucht ∧
      (F.verbraucheNach c s).lokal c = (s.lokal c).halt .ungueltigerWert)

/-- A hosted read is valid at commit (the good case is reachable). -/
def VerbraucheGueltigBeiCommitPflichtErfuellbarAussage : Prop :=
  ∀ (p : Plattform) (bytes : List UInt8),
    ∃ s q a, GueltigBeiCommit p s q ∧ atomar p s q = .antwort a ∧ a.result.isOk = true

/-- A changed outside kills the same question (the refusal case is reachable). -/
def VerbraucheGueltigBeiCommitPflichtNichtTrivialAussage : Prop :=
  ∀ (p : Plattform),
    ∃ s₁ q a s₂, atomar p s₁ q = .antwort a ∧ a.result.isOk = true ∧
      (∀ o, (s₂.objects o).alive = false) ∧ ¬ GueltigBeiCommit p s₂ q

/-- **The pinned handover root of the consume-class step statements.** -/
def VerbraucheSchrittAussagen : Prop :=
  VerbraucheKlasseAussage ∧ VerbrauchePrivatAussage ∧ VerbraucheFehlerGrundAussage ∧
    VerbraucheEinmalLesenAussage ∧ VerbraucheFehlerBeendetUebertragAussage ∧
    VerbraucheGueltigBeiCommitPflichtAussage ∧ VerbraucheWertErfuellbarAussage ∧
    VerbraucheWertNichtTrivialAussage

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

/-- A taken answer moves the counter exactly once, and only when it is still valid. -/
theorem verbraucheEinmalLesen : VerbraucheEinmalLesenAussage := by
  refine ⟨?_, ?_, ?_⟩
  · intro F c s a ready hg
    simp only [Schrittform.verbraucheNach, ready, hg, if_true, if_false]
    cases htr : Antwort.uebersetzt a.question a.reply with
    | none =>
      refine ⟨?_, fun d hd => ?_⟩
      · simp only [htr, Zustand.verbrauche, Function.update_self]
      · simp only [htr, Zustand.verbrauche, Function.update_of_ne hd]
    | some _v =>
      refine ⟨?_, fun d hd => ?_⟩
      · simp only [htr, Zustand.verbrauche, Function.update_self]
      · simp only [htr, Zustand.verbrauche, Function.update_of_ne hd]
  · intro F c s a ready hval
    simp only [Schrittform.verbraucheNach, ready, hval, if_true, if_false]
  · intro F c s hempty
    simp only [Schrittform.verbraucheNach, hempty, Schrittform.nach]

/-- A commit-valid ok answer exists. -/
theorem verbraucheEinmalLesen_erfuellbar : VerbraucheEinmalLesenErfuellbarAussage := by
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let a : Antwort := ⟨handle.origin, [handle.origin], .ok (.data [])⟩
  let ev : AntwortEreignis := ⟨0, 0, 0, q, a⟩
  refine ⟨ev, .x86_64, ?_, ?_⟩
  · left
    intro t mem
    have singleton : t = (⟨handle, .read⟩ : Zugriff) := by
      have : t ∈ [⟨handle, .read⟩] := mem
      exact List.mem_singleton.mp this
    subst singleton
    exact List.mem_cons_self
  · rfl

/-- An ok answer without commit evidence exists. -/
theorem verbraucheEinmalLesen_nichtTrivial : VerbraucheEinmalLesenNichtTrivialAussage := by
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let a : Antwort := ⟨handle.origin, [], .ok (.data [])⟩
  let ev : AntwortEreignis := ⟨0, 0, 0, q, a⟩
  refine ⟨ev, .x86_64, ?_, ?_⟩
  · exact Antwort.commitGueltig_nicht_leer .x86_64 q a rfl
      (⟨handle, .read⟩ : Zugriff) List.mem_cons_self
      (hosted_nicht_stabil .x86_64 ⟨.hosted, 0⟩ rfl)
  · rfl

/-- A fitting ok answer ends nothing, writes its translated value and keeps the status; an
    untranslatable answer ends with a reason exit. -/
theorem verbraucheFehlerBeendetUebertrag : VerbraucheFehlerBeendetUebertragAussage := by
  intro F c s a ready hg
  simp only [Schrittform.verbraucheNach, ready, hg, if_true, if_false]
  cases h : Antwort.uebersetzt a.question a.reply with
  | some v =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [Zustand.verbrauche]
    · simp only [Zustand.verbrauche]
    · simp only [Zustand.verbrauche, verbraucheSchreibe, h, Rahmen.schreibe,
        Function.update_self]
  | none =>
    refine ⟨?_, ?_⟩
    · simp only [Zustand.verbrauche, Function.update_self]
    · simp only [Zustand.verbrauche]

/-- The matching binding case is jointly satisfiable. -/
theorem verbraucheFehlerBeendetUebertrag_erfuellbar :
    VerbraucheFehlerBeendetUebertragErfuellbarAussage := by
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let a : Antwort := ⟨handle.origin, [handle.origin], .ok (.data [])⟩
  let ev : AntwortEreignis := ⟨0, 0, 0, q, a⟩
  refine ⟨ev, .x86_64, (AussenWert.data []).alsDynamisch, ?_, ?_⟩
  · left
    intro t mem
    have singleton : t = (⟨handle, .read⟩ : Zugriff) := List.mem_singleton.mp mem
    subst singleton
    exact List.mem_cons_self
  · exact Antwort.uebersetzt_von_ok q a (.data []) rfl rfl

/-- The termination case is jointly satisfiable with a valid error answer. -/
theorem verbraucheFehlerBeendetUebertrag_nichtTrivial :
    VerbraucheFehlerBeendetUebertragNichtTrivialAussage := by
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let a : Antwort := ⟨handle.origin, [handle.origin], .error .staleOrDenied⟩
  let ev : AntwortEreignis := ⟨0, 0, 0, q, a⟩
  refine ⟨ev, .x86_64, ?_, ?_⟩
  · left
    intro t mem
    have singleton : t = (⟨handle, .read⟩ : Zugriff) := List.mem_singleton.mp mem
    subst singleton
    exact List.mem_cons_self
  · exact Antwort.uebersetzt_fehler q a .staleOrDenied rfl

/-- A hosted read is valid at commit. -/
theorem verbraucheGueltigBeiCommitPflicht_erfuellbar :
    VerbraucheGueltigBeiCommitPflichtErfuellbarAussage :=
  fun p bytes => gueltig_erfuellbar p bytes

/-- A changed outside kills the same question. -/
theorem verbraucheGueltigBeiCommitPflicht_nichtTrivial :
    VerbraucheGueltigBeiCommitPflichtNichtTrivialAussage :=
  fun p => ungueltig_erfuellbar p []

/-- An atomic ok answer carries the evidence of its commit; an answer without the evidence is
    refused and not consumed. -/
theorem verbraucheGueltigBeiCommitPflicht : VerbraucheGueltigBeiCommitPflichtAussage := by
  refine ⟨gueltigBeiCommitPflicht.1, gueltigBeiCommitPflicht.2, ?_, ?_⟩
  · intro p s q a antwort erfolg
    exact Antwort.commitGueltig_von_atomar antwort erfolg
  · intro F c s a ready hval
    simp only [Schrittform.verbraucheNach, ready, hval, if_true, if_false, Function.update_self]
    exact ⟨True.intro, True.intro⟩

/-- **The pinned root holds.** Every unit above is proved; none is a pinned handover now. -/
theorem verbraucheSchrittAussagen : VerbraucheSchrittAussagen :=
  ⟨verbraucheKlasse, verbrauchePrivat, verbraucheFehlerGrund, verbraucheEinmalLesen,
    verbraucheFehlerBeendetUebertrag, verbraucheGueltigBeiCommitPflicht,
    verbraucheWert_erfuellbar, verbraucheWert_nichtTrivial⟩

end Gabbro.Core.Aussenfrage
