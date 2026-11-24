/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Aussagen.lean
  Subject:   The pinned proof obligations of M9P for Hy4 (B11, one per form plus lift).

  Each `…Aussage` is one independent unit a prover closes without design decisions:
  every name it mentions exists (in this directory, in `core/`, or in Mathlib), and
  the statement says exactly what its name claims. The designer proved the finite
  core (`Quelle`, `Hebung`, `massEindeutig`, the coin); what remains open is the
  infinite lift and the per-form bounds.

  Map (B11(c) statement forms → inventory → Aussage):
  - lift (B11(a)): `hebeAussage`
  - `planned.probability.event`: `prEreignisAussage`
  - `planned.probability.cost`: `kostenErwartungAussage`
  - `planned.probability.termination`: `fastSicherAbschlussAussage`
  - `planned.probability.progress`: `fastSicherFortschrittAussage`
  - `planned.probability.informationTheoretic`: `infoTheoretischAussage`
  - `planned.probability.reduction`: `reduktionAussage`

  The declaration discipline (B11(d), model side) is proved, not pinned:
  `Erfuellbar.quelleDeklariert` shows every selected `.zufall` row is backed by
  exactly one platform-declared source.

  The image/compiler distribution lift (B11(e)) is transport work (M11): it reuses
  these statements and is documented in the report, not pinned here.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Form

@[expose] public section

namespace Gabbro.Core.Beobachtung

/-- The lift exists (B11(a), model side): for every binding, scheduler and
    environment with hardware and a selected source row, a lift bundle exists.
    The bundle's fields (cylinder-faithful measure, admitted replay, causality,
    scheduler discipline, band answers) are the whole specification; the proof is
    the model-side Ionescu-Tulcea construction, replaying the machine
    deterministically and consuming band draws in trace order.
    Difficulty: schwer. Sketch: build the replay by recursion over cuts (always
    step the scheduler's choice when enabled, else any enabled step); the band
    measure is the Kolmogorov extension of the cylinder weights, which agree on
    intersections by the product form of `ZylinderGewicht`. -/
def hebeAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung),
    Katalog.Hardware E.katalog h →
    E.katalog.enthaelt (Katalog.Zeile.zufall B.quelle.id) →
    ∃ _ : Hebebuendel B S E h, True

/-- `planned.probability.event`: every declared event bound holds on the lift.
    Difficulty: mittel. Sketch: unfold the declared event to its cylinder cover
    and apply the bundle's `massErhalt` on each cylinder; countable subadditivity
    does the rest. -/
def prEreignisAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h) (ann : ProbAnnahmen B hb)
    (Ereignis : Maschine.Lauf E → Prop) (p : ENNReal),
    ann.prBehauptet Ereignis p → PrForm B hb Ereignis p

/-- `planned.probability.cost`: every declared expected-cost bound holds.
    Difficulty: schwer. Sketch: the cost function is the B8 step count, hence
    measurable and bounded on finite prefixes; monotone convergence lifts the
    finite-prefix expectations to the run, and `massErhalt` fixes each prefix. -/
def kostenErwartungAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h) (ann : ProbAnnahmen B hb)
    (kosten : Maschine.Lauf E → Nat) (b : ENNReal),
    ann.kostenBehauptet kosten b → KostenForm B hb kosten b

/-- `planned.probability.termination`: every declared almost-sure termination
    holds: randomized loops terminate with probability one.
    Difficulty: schwer. Sketch: the loop's exit event is a countable union of
    cylinders, one per exit cut; the per-cut weights sum to one by the finite
    Markov-chain analysis the checker certifies. -/
def fastSicherAbschlussAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h) (ann : ProbAnnahmen B hb)
    (Ziel : Maschine.Lauf E → Prop),
    ann.abschlussBehauptet Ziel → AbschlussForm B hb Ziel

/-- `planned.probability.progress`: every declared almost-sure progress holds:
    randomized backoff and lock-free retry succeed with probability one.
    Difficulty: schwer. Sketch: as for termination, with the retry count (not the
    cut) as the union index; fairness of the hardware history keeps every retry
    enabled. -/
def fastSicherFortschrittAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h) (ann : ProbAnnahmen B hb)
    (Ziel : Maschine.Lauf E → Prop),
    ann.fortschrittBehauptet Ziel → FortschrittForm B hb Ziel

/-- `planned.probability.informationTheoretic`: every in-budget adversary has
    advantage at most `eps`, against every scheduler and policy.
    Difficulty: schwer. Sketch: the adversary is a Lean function over the history,
    so fix it and count its queries in the trace prefix; the advantage is a
    difference of two cylinder measures, bounded by the union bound over the
    queried positions. -/
def infoTheoretischAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h) (ann : ProbAnnahmen B hb)
    (imBudget : Gegner → Prop) (eps : ENNReal)
    (spiel : Gegner → Maschine.Lauf E → Prop),
    ann.schrankeBehauptet imBudget eps spiel → SchrankenForm B hb imBudget eps spiel

/-- `planned.probability.reduction`: every scheme advantage reduces to a primitive
    advantage, whose hardness is the named assumption in (c).
    Difficulty: mittel. Sketch: the reduction is a fixed Lean function on
    adversaries (no design choice: it is part of the declared claim); push the
    scheme game through it and read the bound off the primitive game. -/
def reduktionAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h) (ann : ProbAnnahmen B hb)
    (spielS spielP : Gegner → Maschine.Lauf E → Prop) (c δ : ENNReal),
    ann.reduktionBehauptet spielS spielP c δ → ReduktionForm B hb spielS spielP c δ

end Gabbro.Core.Beobachtung
