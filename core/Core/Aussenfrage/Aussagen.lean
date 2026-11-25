/-
  File:      core/Core/Aussenfrage/Aussagen.lean
  Subject:   THE PINNED OUTSIDE-QUESTION STATEMENTS (MK-06, design). Four kernel statements
             under one pinned root `AussenFrageAussagen`, each with its satisfiability
             (`…ErfuellbarAussage`: the model reaches the good case) and its non-triviality
             (`…NichtTrivialAussage`: the model also represents the error, only the checker
             excludes it):
             * `FrageSimAussage`: a question leaves in program order, arrival is global and
               consumption is local (`stelleFrage` appends, `antwort` appends globally without
               touching counters, `verbrauche` moves only the acting context's counter);
             * `GueltigBeiCommitPflichtAussage`: a committed outside operation is valid at
               commit (`atomar_gueltig`), and an effect whose authorisation rests only on an
               earlier answer is refused under the arbitrary-change rely
               (`fruehere_antwort_ungueltig`): one atomic outside read, no double fetch;
             * `ProvenienzTraegtAussage`: propagation only grows the label
               (`propagierung_monoton`) and every value derived from an outside answer carries
               its provenance (`abgeleitet_traegt`);
             * `GleitAntwortZulaessigAussage`: the reference float hardware answers every
               question kind with the matching answer kind (arithmetic with bits,
               comparisons with truth values); the value comes from the answer.
             The step-level enforcement for the new `verbrauche` class (refusal on
             `¬ GueltigBeiCommit`, the single atomic read, the error-as-reason-exit transfer)
             is follow-up work once `Befehl` and `Wirkungsklasse` grow; it is decomposed into
             independent proof units in the design report.
-/
module

public import Core.Maschine.Aussen
public import Core.Maschine.Zustand
public import Core.Katalog.Aussen
public import Core.Katalog.Gleit
public import Core.Katalog.Lauf
public import Core.Aussen.Bindung
public import Core.Aussen.Provenienz

@[expose] public section

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Aussen

/-- **A question leaves in program order, arrival is global, consumption is local.**
    Issuing appends the question event; an arrival appends the answer event globally and
    touches no consumption counter; consuming moves only the acting context's counter. -/
def FrageSimAussage : Prop :=
  (∀ (L Ort Wert Raum Lok Grund : Type) (z : Zustand L Ort Wert Raum Lok Grund)
      (t : Nat) (c : Kontext) (q : Frage),
    (z.frage (z.stelleFrage t c q)).fragen = z.fragen ++ [z.stelleFrage t c q]) ∧
  (∀ (L Ort Wert Raum Lok Grund : Type) (z : Zustand L Ort Wert Raum Lok Grund)
      (a : AntwortEreignis),
    (z.antwort a).antworten = z.antworten ++ [a] ∧
      (z.antwort a).verbraucht = z.verbraucht) ∧
  (∀ (L Ort Wert Raum Lok Grund : Type) (z : Zustand L Ort Wert Raum Lok Grund)
      (c : Kontext),
    (z.verbrauche c).antworten = z.antworten ∧
      (z.verbrauche c).verbraucht c = z.verbraucht c + 1 ∧
      ∀ d, d ≠ c → (z.verbrauche c).verbraucht d = z.verbraucht d)

/-- The order/global/local facts hold on every state. -/
def FrageSimErfuellbarAussage : Prop :=
  FrageSimAussage

/-- **The model represents outside disagreement.** The same question may receive two
    different answers: arrival is an event, not a function, so consumption must track
    arrival separately and `GueltigBeiCommit` must revalidate at commit. -/
def FrageSimNichtTrivialAussage : Prop :=
  ∃ (q : Frage) (r₁ r₂ : Antwort), r₁ ≠ r₂

/-- **Validity at commit, as a checker duty.** A successful atomic answer establishes
    `GueltigBeiCommit` at its commit snapshot; an effect whose authorisation rests only
    on an earlier answer finds the same question invalid on a changed outside, unless a
    row states stability. -/
def GueltigBeiCommitPflichtAussage : Prop :=
  (∀ (p : Plattform) (s : AussenSicht) (q : Frage) (a : Antwort),
    atomar p s q = .antwort a → a.result.isOk = true → GueltigBeiCommit p s q) ∧
  (∀ (p : Plattform) (s₁ : AussenSicht) (q : Frage) (t : Zugriff) (mem : t ∈ q.zugriffe),
    ¬ ReihenStabil p t.handle.origin.object →
    ∃ s₂ : AussenSicht, (∀ o, (s₂.objects o).alive = false) ∧ ¬ GueltigBeiCommit p s₂ q)

/-- A hosted read is valid at commit. -/
def GueltigBeiCommitErfuellbarAussage : Prop :=
  ∀ (p : Plattform) (bytes : List UInt8),
    ∃ s q a, GueltigBeiCommit p s q ∧ atomar p s q = .antwort a ∧ a.result.isOk = true

/-- **The error is representable.** An earlier hosted answer succeeds, and the same
    question is invalid on a changed outside with no row stability: only the checker
    excludes it. -/
def GueltigBeiCommitNichtTrivialAussage : Prop :=
  ∀ (p : Plattform),
    ∃ s₁ q a s₂, atomar p s₁ q = .antwort a ∧ a.result.isOk = true ∧
      (∀ o, (s₂.objects o).alive = false) ∧ ¬ GueltigBeiCommit p s₂ q

/-- **Provenance is carried.** Propagation only grows the label, and every value derived
    from an outside answer carries the answer's object and generation. -/
def ProvenienzTraegtAussage : Prop :=
  (∀ {A : Type} (u : Wert A) (a : Antwort), Abgeleitet u a → u.spur a.origin) ∧
  (∀ {P P' : Provenienz} (step : PropSchritt P P') (q : Herkunft), P q → P' q)

/-- A value read from a hosted answer carries that answer's provenance. -/
def ProvenienzTraegtErfuellbarAussage : Prop :=
  ∃ (a : Antwort) (u : Wert Nat), Abgeleitet u a ∧ u.spur a.origin

/-- **Fresh values carry nothing.** A derived value carries its answer's provenance
    while a fresh value carries none: provenance distinguishes them. -/
def ProvenienzTraegtNichtTrivialAussage : Prop :=
  ∃ (a : Antwort) (u v : Wert Nat), Abgeleitet u a ∧ u.spur a.origin ∧ ¬ v.spur a.origin

/-- **A float answer is admissible.** The reference hardware answers every 32-bit and
    64-bit question kind with the matching answer kind: arithmetic, roots, fused
    multiply-add and conversions with bits, comparisons with truth values. -/
def GleitAntwortZulaessigAussage : Prop :=
  (∀ (op : GleitVergleich) (a b : UInt32), ∃ w : Bool, binary32.rechne (.vergleich op a b) = .wahr w) ∧
  (∀ (op : GleitBinaer) (a b : UInt32), ∃ w : UInt32, binary32.rechne (.binaer op a b) = .bits w) ∧
  (∀ (a : UInt32), ∃ w : UInt32, binary32.rechne (.sqrt a) = .bits w) ∧
  (∀ (a b c : UInt32), ∃ w : UInt32, binary32.rechne (.fma a b c) = .bits w) ∧
  (∀ (n : Int), ∃ w : UInt32, binary32.rechne (.vonInt n) = .bits w) ∧
  (∀ (op : GleitVergleich) (a b : UInt64), ∃ w : Bool, binary64.rechne (.vergleich op a b) = .wahr w) ∧
  (∀ (op : GleitBinaer) (a b : UInt64), ∃ w : UInt64, binary64.rechne (.binaer op a b) = .bits w) ∧
  (∀ (a : UInt64), ∃ w : UInt64, binary64.rechne (.sqrt a) = .bits w) ∧
  (∀ (a b c : UInt64), ∃ w : UInt64, binary64.rechne (.fma a b c) = .bits w) ∧
  (∀ (n : Int), ∃ w : UInt64, binary64.rechne (.vonInt n) = .bits w)

/-- Conformant float hardware exists. -/
def GleitAntwortErfuellbarAussage : Prop :=
  ∃ hw : GleitHardware, nativeFloat hw

/-- **Answer kinds never confuse.** A bits answer is never equal to a truth answer, in
    either width: the kind of the answer is fixed by the kind of the question. -/
def GleitAntwortNichtTrivialAussage : Prop :=
  (∀ (x : UInt32) (b : Bool), ¬ binary32.antwortGleich (.bits x) (.wahr b)) ∧
  (∀ (x : UInt64) (b : Bool), ¬ binary64.antwortGleich (.bits x) (.wahr b))

/-- **The pinned root of the outside-question statements.** -/
def AussenFrageAussagen : Prop :=
  FrageSimAussage ∧ GueltigBeiCommitPflichtAussage ∧ ProvenienzTraegtAussage ∧
    GleitAntwortZulaessigAussage

end Gabbro.Core.Aussenfrage
