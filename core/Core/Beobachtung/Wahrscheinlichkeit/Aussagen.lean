/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Aussagen.lean
  Subject:   The pinned obligations of the probabilistic statement (M9P, B11(c)).

  `hebeAussage` carries the whole lift: one pinned statement whose proof shows
  every isometry, colour and finite-path weight on the replay. Everything below
  is a corollary over that lift — nothing here reaches the runs directly.

  Map (each obligation states what the checker decides, then what remains a
  per-program duty; every premise is specific, never a free proposition):
  - `planned.probability.event`: `prEreignisAussage`
  - `planned.probability.cost`: `kostenErwartungAussage`
  - `planned.probability.termination`: `fastSicherAbschlussAussage`
  - `planned.probability.progress`: `fastSicherFortschrittAussage`
  - `planned.probability.informationTheoretic`: `infoTheoretischAussage`
  - `planned.probability.reduction`: `reduktionAussage`
  - `planned.probability.draw` is decided by finite catalogue-row lookup (B11(d)),
    hence a checker rule by construction and needs neither an obligation here nor
    an undecidability proof.

  The two cryptographic obligations are GabbroProve user duties, proved per
  program over the generic model: their statements quantify over every adversary,
  so no finite checker clause captures them (`Unentscheidbar.lean` pins why).
  They are kept here as vocabulary, not as part of `GabbroZielProb`.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Form

@[expose] public section

namespace Gabbro.Core.Beobachtung

/-- `planned.probability.event`: every declared event bound holds on the lift.
    Difficulty: medium (cylinder rewriting plus measure monotonicity).
    Sketch: unfold the obligation; checker-true gives `schluesselNodupB`, hence
    key-`Nodup` of the mapped path, so `massErhalt` applies; the weight premise
    identifies the cylinder weight with the certified rational by the declared
    source law; the run event's preimage contains the cylinder, so the checker's
    inequality `w ≥ p` carries over. -/
def prEreignisAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h)
    (pfad : List (Nat × Nat)) (wNum wDen pNum pDen : Nat),
    ereignisPflicht B hb pfad wNum wDen pNum pDen

/-- `planned.probability.cost`: every declared expected-cost bound holds.
    Difficulty: hard (shell sum over the exit shells).
    Sketch: unfold the obligation; monotonicity and the exit link partition the
    bands by exit index; on shell `n` the cost is at most `n * c` and the shell
    has measure at most `(1 - q)^n` by decay; the geometric series sums to
    `c / q ≤ b` by the checker's certificate. -/
def kostenErwartungAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h)
    (kosten : Maschine.Lauf E → Nat) (cNum cDen qNum qDen bNum bDen : Nat),
    kostenPflicht B hb kosten cNum cDen qNum qDen bNum bDen

/-- `planned.probability.termination`: every declared almost-sure termination
    holds: the surviving set shrinks to nothing, so the target has measure one.
    Difficulty: hard (continuity of the measure from above).
    Sketch: unfold the obligation; the survival family is decreasing with
    measures tending to zero by the geometric decay, so its intersection has
    measure zero; the exit link puts the target's preimage above the complement,
    hence measure one. -/
def fastSicherAbschlussAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h)
    (Ziel : Maschine.Lauf E → Prop) (qNum qDen : Nat),
    abschlussPflicht B hb Ziel qNum qDen

/-- `planned.probability.progress`: every declared almost-sure progress holds:
    the retry that has not yet succeeded shrinks to nothing.
    Difficulty: hard (same continuity argument as termination).
    Sketch: as for termination, read as retry progress: the survival family is
    the set of bands that have not yet succeeded by cut `n`; geometric decay
    drives it to zero, the exit link yields the goal with measure one. -/
def fastSicherFortschrittAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h)
    (Ziel : Maschine.Lauf E → Prop) (qNum qDen : Nat),
    fortschrittPflicht B hb Ziel qNum qDen

/-- `planned.probability.informationTheoretic`: every in-budget adversary has
    advantage at most `eps`. GabbroProve user duty: the statement quantifies over
    every adversary, so no finite checker clause captures it.
    Difficulty: per program (the user proves it over the generic model).
    Sketch: fix the program; bound the adversary's distinguishing advantage by
    the query budget and the primitive's named hardness; no checker step. -/
def infoTheoretischAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h)
    (imBudget : Gegner → Prop)
    (eps : ENNReal)
    (spiel : Gegner → Maschine.Lauf E → Prop),
    SchrankenForm B hb imBudget eps spiel

/-- `planned.probability.reduction`: every scheme advantage reduces to a primitive
    with named hardness. GabbroProve user duty: the statement quantifies over
    every scheme adversary, so no finite checker clause captures it.
    Difficulty: per program (the user proves it over the generic model).
    Sketch: fix program and reduction; the reduction adversary runs the scheme
    adversary as a black box, so its success bounds the scheme's success up to
    the stated factor; the primitive's hardness stays a named assumption. -/
def reduktionAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung)
    (hb : Hebebuendel B S E h)
    (schemaGegner : Gegner → Prop)
    (reduktion : Gegner → Gegner)
    (primitivGegner : Gegner → Prop)
    (c : ENNReal)
    (spiel ziel : Gegner → Maschine.Lauf E → Prop),
    ReduktionForm B hb schemaGegner reduktion primitivGegner c spiel ziel

/-- The lift exists (B11(a), model side): for every binding, scheduler and
    environment with hardware and a selected source row, a lift bundle exists.
    The bundle's fields (cylinder-faithful measure, admitted replay, causality,
    scheduler discipline, band answers) are the whole specification; the proof is
    the model-side Ionescu-Tulcea construction, replaying the machine
    deterministically and consuming band draws in trace order.
    Consistency (Hy4): `massErhalt` quantifies only over key-`Nodup` cylinders —
    a contradictory path (one position, two outcomes) denotes the empty band set
    while the law product is positive, so no law mentions such objects.
    Difficulty: schwer. Sketch: build the replay by recursion over cuts (always
    step the scheduler's choice when enabled, else any enabled step); the band
    measure is the Kolmogorov extension of the cylinder weights over the
    consistent family, which agree on intersections by the product form of
    `ZylinderGewicht`. -/
def hebeAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung),
    Katalog.Hardware E.katalog h →
    E.katalog.enthaelt (Katalog.Zeile.zufall B.quelle.id) →
    ∃ _ : Hebebuendel B S E h, True

end Gabbro.Core.Beobachtung
