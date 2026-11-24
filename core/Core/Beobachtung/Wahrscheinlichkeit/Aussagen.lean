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
  - `planned.probability.informationTheoretic`: `InfoTheoretischPflicht`
  - `planned.probability.reduction`: `ReduktionPflicht`
  - `planned.probability.draw` is decided by finite catalogue-row lookup (B11(d)),
    hence a checker rule by construction and needs neither an obligation here nor
    an undecidability proof.

  The two cryptographic obligations are GabbroProve user duties, proved per
  program over the generic model: their bodies quantify over every adversary,
  so no finite checker clause captures them (`Unentscheidbar.lean` pins why).
  Their bound data is fixed by the program, so they are predicates over declared
  data here, never ∀-sentences over parameters the language may instantiate.
  They stay outside `GabbroZielProb`.
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
    Difficulty: hard (tail sum of the survival family).
    Sketch: unfold the obligation; the survivor intersection is null by
    continuity from above, so off a null set every band has a first exit; the
    cost premise bounds its cost by that first exit times `c`; the tail sum of
    the survival measures is at most the geometric series `1 / q`, and the
    checker's certificate gives `c / q ≤ b`. -/
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

/-- `planned.probability.informationTheoretic` as a GabbroProve duty: the program
    declares its budget class, bound and game, then proves the resulting
    `SchrankenForm` over the generic model. No `∀` over those parameters — they
    are program-fixed; instantiating a zero bound is no longer a move the language
    can make (the former free-bound `Aussage` was refuted). Difficulty: per program.
    Sketch: bound the declared adversary's distinguishing advantage by its query
    budget and the primitive's named hardness; no checker step. -/
def InfoTheoretischPflicht (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Katalog.Umgebung}
    (hb : Hebebuendel B S E h)
    (deklaration : InfoDeklaration L Ort Wert Raum Lok Grund Bedingung Wahl Form E) : Prop :=
  SchrankenForm B hb deklaration.imBudget deklaration.eps deklaration.spiel

/-- `planned.probability.reduction` as a GabbroProve duty: the program declares
    its scheme class, reduction, primitive class, factor and games, then proves
    the resulting `ReduktionForm`. `primitivGegner` is consumed by the form: the
    reduction must land in the declared primitive class, which carries the named
    hardness assumption. No `∀` over the program-fixed parameters (the former
    free-bound `Aussage`, whose `primitivGegner` was unused, was refuted).
    Difficulty: per program. Sketch: run the declared scheme adversary as a black
    box; its declared success bounds the scheme's success up to the factor. -/
def ReduktionPflicht (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Katalog.Umgebung}
    (hb : Hebebuendel B S E h)
    (deklaration : ReduktionDeklaration L Ort Wert Raum Lok Grund Bedingung Wahl Form E) : Prop :=
  ReduktionForm B hb deklaration.schemaGegner deklaration.reduktion
    deklaration.primitivGegner deklaration.c deklaration.spiel deklaration.ziel

/-- The lift exists (B11(a), model side): for every binding, scheduler and
    environment with hardware, a selected source row and an admissible start, a
    lift bundle exists. The admissible start is necessary: `replayZulaessig`
    contains `ZulStart`, whose first conjunct is image validity, so an otherwise
    admissible unit with an invalid image has no bundle (the former unsharpened
    form was refuted). The bundle's fields (cylinder-faithful measure, admitted
    replay, causality, scheduler discipline, band answers) are the whole
    specification; the proof is the model-side Ionescu-Tulcea construction,
    replaying the machine deterministically and consuming band draws in trace
    order. Consistency (Hy4): `massErhalt` quantifies only over key-`Nodup`
    cylinders — a contradictory path (one position, two outcomes) denotes the
    empty band set while the law product is positive, so no law mentions such
    objects. Difficulty: schwer. Sketch: build the replay by recursion over cuts
    (always step the scheduler's choice when enabled, else any enabled step); the
    band measure is the Kolmogorov extension of the cylinder weights over the
    consistent family, which agree on intersections by the product form of
    `ZylinderGewicht`. -/
def hebeAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Katalog.Umgebung),
    Katalog.Hardware E.katalog h →
    E.katalog.enthaelt (Katalog.Zeile.zufall B.quelle.id) →
    (∃ s : Katalog.AussenStart, E.ZulStart h s) →
    ∃ _ : Hebebuendel B S E h, True

end Gabbro.Core.Beobachtung
