/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Form.lean
  Subject:   The shape of the probabilistic statement beside the goal (M9P, B11(c)).

  `GabbroZielProb` is the quantitative statement beside `GabbroZielForm`, reusing
  every safety leg: safety already holds for every random outcome, and this shape
  adds the six B11(c) statement forms over the lift bundle of `Hebung`:
  probability bounds on run events, expected cost, almost-sure termination and
  progress of randomized loops, and the two cryptographic adversary forms.

  The (c)-side (named assumptions and declared bounds: the source law, the claimed
  `p`, `b`, budgets, hardness) enters as `ProbAnnahmen`: what the program declares
  through its clause forms. Checking those declarations (B11(d): decide exactly on
  finite state, refuse on infinite state) is the checker's obligation, pinned in
  `Aussagen`; this file fixes the statement shape only.

  Like `Ziel/Form.lean`, this file proves nothing about runs: the force lies in the
  pinned lift (`hebeAussage`) and the per-form obligations, never in this shape
  alone. Non-vacuity is `ProbNichtLeer`, discharged by the coin in `Erfuellbar`.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog

/-- The (c)-side: what the program declares. Each field is one claimed bound, as the
    future clause forms (`planned.probability.*`) will state it; the checker decides
    them, the statements below give them meaning over the lift. -/
structure ProbAnnahmen (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h) where
  prBehauptet : (Maschine.Lauf E → Prop) → ENNReal → Prop
  kostenBehauptet : (Maschine.Lauf E → Nat) → ENNReal → Prop
  abschlussBehauptet : (Maschine.Lauf E → Prop) → Prop
  fortschrittBehauptet : (Maschine.Lauf E → Prop) → Prop
  schrankeBehauptet : (Gegner → Prop) → ENNReal → (Gegner → Maschine.Lauf E → Prop) → Prop
  reduktionBehauptet : (Gegner → Maschine.Lauf E → Prop) →
    (Gegner → Maschine.Lauf E → Prop) → ENNReal → ENNReal → Prop

/-- `planned.probability.event`: the run event holds with probability at least `p`,
    under every scheduler and every non-random policy (the bundle quantifies them). -/
def PrForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h)
    (Ereignis : Maschine.Lauf E → Prop) (p : ENNReal) : Prop :=
  hb.mu {band | Ereignis (hb.replay band)} ≥ p

/-- `planned.probability.cost`: the expected cost is at most `b`, building on the
    cost model the run carries. -/
def KostenForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h)
    (kosten : Maschine.Lauf E → Nat) (b : ENNReal) : Prop :=
  MeasureTheory.lintegral hb.mu (fun band => (kosten (hb.replay band) : ENNReal)) ≤ b

/-- `planned.probability.termination`: almost-sure termination of a randomized loop. -/
def AbschlussForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h)
    (Ziel : Maschine.Lauf E → Prop) : Prop :=
  hb.mu {band | Ziel (hb.replay band)} = 1

/-- `planned.probability.progress`: almost-sure progress of a randomized operation
    (randomized backoff, lock-free retry). Same measure-one shape as termination,
    over a progress predicate instead of a termination predicate. -/
def FortschrittForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h)
    (Ziel : Maschine.Lauf E → Prop) : Prop :=
  hb.mu {band | Ziel (hb.replay band)} = 1

/-- `planned.probability.informationTheoretic`: every adversary in budget has
    advantage at most `eps`. The adversary is any Lean function over the history
    (B11), never assumed to be a Gabbro program. -/
def SchrankenForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h)
    (imBudget : Gegner → Prop) (eps : ENNReal)
    (spiel : Gegner → Maschine.Lauf E → Prop) : Prop :=
  ∀ A : Gegner, imBudget A → hb.mu {band | spiel A (hb.replay band)} ≤ eps

/-- `planned.probability.reduction`: the scheme's advantage reduces to the
    primitive's, whose hardness is a named assumption in (c). -/
def ReduktionForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h)
    (spielS spielP : Gegner → Maschine.Lauf E → Prop)
    (c δ : ENNReal) : Prop :=
  ∀ A : Gegner, ∃ D : Gegner,
    hb.mu {band | spielS A (hb.replay band)} ≤
      c * hb.mu {band | spielP D (hb.replay band)} + δ

/-- The probabilistic statement beside the goal: every declared bound holds on the
    lift, for every bundle (hence every scheduler and every non-random policy). -/
def GabbroZielProb (B : Zufallsbindung) (S : Scheduler)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) : Prop :=
  ∀ hb : Hebebuendel B S E h, ∀ ann : ProbAnnahmen B hb,
    (∀ Ereignis p, ann.prBehauptet Ereignis p → PrForm B hb Ereignis p) ∧
    (∀ kosten b, ann.kostenBehauptet kosten b → KostenForm B hb kosten b) ∧
    (∀ Ziel, ann.abschlussBehauptet Ziel → AbschlussForm B hb Ziel) ∧
    (∀ Ziel, ann.fortschrittBehauptet Ziel → FortschrittForm B hb Ziel) ∧
    (∀ imBudget eps spiel, ann.schrankeBehauptet imBudget eps spiel →
      SchrankenForm B hb imBudget eps spiel) ∧
    (∀ spielS spielP c δ, ann.reduktionBehauptet spielS spielP c δ →
      ReduktionForm B hb spielS spielP c δ)

/-- Non-vacuity of the probabilistic shape: the source admits an event strictly
    inside `(0, 1)`. A degenerate source (or a degenerate instantiation) satisfies
    no instance of this; the coin discharges it in `Erfuellbar`. -/
def ProbNichtLeer (Q : Zufallsquelle) : Prop :=
  ∃ E : Fin Q.anz → Prop, ∃ _ : DecidablePred E,
    0 < Wahrscheinlichkeit Q E ∧ Wahrscheinlichkeit Q E < 1

end Gabbro.Core.Beobachtung
