/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Form.lean
  Subject:   The shape of the probabilistic statement beside the goal (M9P, B11(c)).

  `GabbroZielProb` is the quantitative statement beside `GabbroZielForm`, reusing
  every safety leg: safety already holds for every random outcome, and this shape
  adds the four B11(c) statement forms the checker decides over the lift bundle of
  `Hebung`: probability bounds on finite-cylinder run events, expected cost under a
  geometric exit summary, almost-sure termination and progress of randomized loops
  with per-iteration exit probability at least `q > 0`.

  The (c)-side no longer contains free propositions (Hy4 refuted the old
  `ProbAnnahmen` shape: six unconstrained `Prop` fields admit `fun _ … => True`,
  which demands e.g. `μ univ ≤ 0`). Every premise below is specific: the checker's
  computable verdict `pruefeProb k = true` over finite clause data (rationals as
  `Nat` pairs, drawn from the program's loop summary), plus certified facts about
  the declared source law (`ZylinderGewicht`) or the loop's survival family. The
  checker decides or refuses; nothing is derived, no refusal becomes a warning.

  The two cryptographic forms (`SchrankenForm`, `ReduktionForm`) have no decidable
  fragment: they quantify over every adversary (an arbitrary Lean function), so no
  finite clause captures them. They are GabbroProve user duties, proved per program
  over the generic model, with the primitive's hardness kept as a named assumption
  in (c) — never as a free premise. They stay here as vocabulary, not as part of
  `GabbroZielProb`; `Unentscheidbar.lean` pins why no checker decides them.

  Like `Ziel/Form.lean`, this file proves nothing about runs: the force lies in the
  pinned lift (`hebeAussage`) and the per-form obligations, never in this shape
  alone. Non-vacuity is `ProbNichtLeer`, discharged by the coin in `Erfuellbar`.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog

/-- Finite clause syntax: the form plus finite data from the program (a finite
    cylinder path or a loop summary with rational weights as `Nat` pairs).
    The cryptographic forms have no constructor: they are GabbroProve duties. -/
inductive ProbKlausel where
  | ereignis (pfad : List (Nat × Nat)) (wNum wDen pNum pDen : Nat) : ProbKlausel
  | kosten (cNum cDen qNum qDen bNum bDen : Nat) : ProbKlausel
  | abschluss (qNum qDen : Nat) : ProbKlausel
  | fortschritt (qNum qDen : Nat) : ProbKlausel

/-- Key consistency of a raw clause path: no draw position appears twice.
    Computable, no `Classical`. The checker refuses inconsistent finite paths, so
    every accepted clause denotes a genuine partial function and `massErhalt`
    applies to it. -/
def schluesselNodupB : List (Nat × Nat) → Bool
  | [] => true
  | p :: rest =>
      schluesselNodupB rest && !(rest.any fun q => decide (q.1 = p.1))

/-- The checker's verdict: pure `Nat` arithmetic, computable, no `Classical`.
    - `ereignis`: the path is key-consistent and the certified cylinder weight `w`
      is a well-formed rational in `[0, 1]` dominating the claimed bound `p`
      (exactness for loop-free, finite-path programs: the weight is computed by
      the checker over the finite state and certified in Lean against the
      declared law).
    - `kosten`: the geometric certificate `c / q ≤ b` with exit rate `q ∈ (0, 1]`.
    - `abschluss` / `fortschritt`: a nontrivial geometric exit rate `q ∈ (0, 1]`. -/
def pruefeProb : ProbKlausel → Bool
  | .ereignis pfad wNum wDen pNum pDen =>
      schluesselNodupB pfad &&
        decide (wDen ≠ 0 ∧ pDen ≠ 0 ∧ wNum * pDen ≥ pNum * wDen ∧ wNum ≤ wDen)
  | .kosten cNum cDen qNum qDen bNum bDen =>
      decide (cDen ≠ 0 ∧ qDen ≠ 0 ∧ bDen ≠ 0 ∧ 0 < qNum ∧ qNum ≤ qDen ∧
        cNum * qDen * bDen ≤ bNum * cDen * qNum)
  | .abschluss qNum qDen =>
      decide (qDen ≠ 0 ∧ 0 < qNum ∧ qNum ≤ qDen)
  | .fortschritt qNum qDen =>
      decide (qDen ≠ 0 ∧ 0 < qNum ∧ qNum ≤ qDen)

/-- A finite `Nat` path as a cylinder over `Q`: outcomes reduced modulo `Q.anz`
    (the same reduction as `Ziehung`, so the clause always denotes). -/
def natZylinder (Q : Zufallsquelle) (pfad : List (Nat × Nat)) : Zylinder Q :=
  ⟨pfad.map fun p => (p.1, ⟨p.2 % Q.anz, Nat.mod_lt _ Q.pos⟩)⟩

/-- The band event of a clause path: exactly the set `massErhalt` speaks about,
    so the lift proof rewrites with it directly. -/
def zylinderEreignis (Q : Zufallsquelle) (pfad : List (Nat × Nat)) : Set Band :=
  {band | ∀ p ∈ (natZylinder Q pfad).pfad, band Q.id p.1 % Q.anz = p.2.val}

/-- The run event of a clause path: runs whose replay comes from the cylinder.
    The preimage `{band | Ereignis (replay band)}` in `PrForm` contains the
    cylinder, so the cylinder bound carries over by monotonicity of the measure. -/
def laufZylinderEreignis (B : Zufallsbindung) (S : Scheduler)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form} {h : Umgebung}
    (hb : Hebebuendel B S E h) (pfad : List (Nat × Nat)) : Maschine.Lauf E → Prop :=
  fun ρ => ∃ band, hb.replay band = ρ ∧ band ∈ zylinderEreignis B.quelle pfad

/-- `planned.probability.event`: the run event holds with probability at least `p`,
    exactly the bound the checker certified on the finite cylinder. -/
def PrForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (Ereignis : Maschine.Lauf E → Prop) (p : ENNReal) : Prop :=
  hb.mu {band | Ereignis (hb.replay band)} ≥ p

/-- `planned.probability.cost`: the expected cost is at most `b`, building on the
    geometric summary the checker certified. -/
def KostenForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (kosten : Maschine.Lauf E → Nat) (b : ENNReal) : Prop :=
  MeasureTheory.lintegral hb.mu (fun band => (kosten (hb.replay band) : ENNReal)) ≤ b

/-- `planned.probability.termination`: almost-sure termination of a randomized loop. -/
def AbschlussForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (Ziel : Maschine.Lauf E → Prop) : Prop :=
  hb.mu {band | Ziel (hb.replay band)} = 1

/-- `planned.probability.progress`: almost-sure progress of a randomized operation
    toward its goal. -/
def FortschrittForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (Ziel : Maschine.Lauf E → Prop) : Prop :=
  hb.mu {band | Ziel (hb.replay band)} = 1

/-- `planned.probability.event` as a checker obligation: the computable verdict,
    plus the certified weight equation against the declared source law (proved in
    Lean from the platform table, not assumed). The weight equation is a premise,
    not part of the verdict, because only the platform table knows the law: the
    checker computes the weight from the program's finite state, Lean certifies it
    against the declared law. -/
def ereignisPflicht (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (pfad : List (Nat × Nat))
    (wNum wDen pNum pDen : Nat) : Prop :=
  pruefeProb (.ereignis pfad wNum wDen pNum pDen) = true →
    ZylinderGewicht B.quelle (natZylinder B.quelle pfad)
      = (wNum : ENNReal) / (wDen : ENNReal) →
    PrForm B hb (laufZylinderEreignis B S hb pfad)
      ((pNum : ENNReal) / (pDen : ENNReal))

/-- `planned.probability.cost` as a checker obligation: the computable verdict on
    the geometric certificate, plus the loop's survival family (monotone,
    geometric decay, cost linear in the FIRST exit index). The checker's loop
    summary (per-iteration cost at most `c`, exit rate at least `q`) yields the
    decay by induction; the pinned premise is the decay itself. The cost must be
    bound at the first exit: with only some exit index the obligation is false. -/
def kostenPflicht (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (kosten : Maschine.Lauf E → Nat)
    (cNum cDen qNum qDen bNum bDen : Nat) : Prop :=
  pruefeProb (.kosten cNum cDen qNum qDen bNum bDen) = true →
    ∀ ueberlebt : Nat → Set Band, (∀ n, MeasurableSet (ueberlebt n)) →
    (∀ n, ueberlebt (n + 1) ⊆ ueberlebt n) →
    (∀ n, hb.mu (ueberlebt n) ≤ (1 - (qNum : ENNReal) / (qDen : ENNReal)) ^ n) →
    (∀ band n, band ∉ ueberlebt n → (∀ m < n, band ∈ ueberlebt m) →
      (kosten (hb.replay band) : ENNReal) ≤
        (n : ENNReal) * ((cNum : ENNReal) / (cDen : ENNReal))) →
    KostenForm B hb kosten ((bNum : ENNReal) / (bDen : ENNReal))

/-- `planned.probability.termination` as a checker obligation: the computable
    verdict on the exit rate, plus the loop's survival family with geometric
    decay and the exit link (leaving the family means reaching the goal). -/
def abschlussPflicht (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (Ziel : Maschine.Lauf E → Prop)
    (qNum qDen : Nat) : Prop :=
  pruefeProb (.abschluss qNum qDen) = true →
    ∀ ueberlebt : Nat → Set Band, (∀ n, MeasurableSet (ueberlebt n)) →
    (∀ n, ueberlebt (n + 1) ⊆ ueberlebt n) →
    (∀ n, hb.mu (ueberlebt n) ≤ (1 - (qNum : ENNReal) / (qDen : ENNReal)) ^ n) →
    (∀ band, (∃ n, band ∉ ueberlebt n) → Ziel (hb.replay band)) →
    AbschlussForm B hb Ziel

/-- `planned.probability.progress` as a checker obligation: same geometric shape
    as termination, read as retry progress toward the goal. -/
def fortschrittPflicht (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h) (Ziel : Maschine.Lauf E → Prop)
    (qNum qDen : Nat) : Prop :=
  pruefeProb (.fortschritt qNum qDen) = true →
    ∀ ueberlebt : Nat → Set Band, (∀ n, MeasurableSet (ueberlebt n)) →
    (∀ n, ueberlebt (n + 1) ⊆ ueberlebt n) →
    (∀ n, hb.mu (ueberlebt n) ≤ (1 - (qNum : ENNReal) / (qDen : ENNReal)) ^ n) →
    (∀ band, (∃ n, band ∉ ueberlebt n) → Ziel (hb.replay band)) →
    FortschrittForm B hb Ziel

/-- `planned.probability.informationTheoretic`: every adversary in budget has
    advantage at most `eps`. GabbroProve user duty, proved per program: the
    statement quantifies over every adversary, so no finite clause captures it.
    The primitive's hardness stays a named assumption, never a free premise. -/
def SchrankenForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h)
    (imBudget : Gegner → Prop)
    (eps : ENNReal)
    (spiel : Gegner → Maschine.Lauf E → Prop) : Prop :=
  ∀ A : Gegner, imBudget A →
    hb.mu {band | spiel A (hb.replay band)} ≤ eps

/-- `planned.probability.reduction`: the scheme's advantage reduces to a
    primitive with named hardness. GabbroProve user duty, proved per program:
    the statement quantifies over every scheme adversary, so no finite clause
    captures it. -/
def ReduktionForm (B : Zufallsbindung)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung}
    (hb : Hebebuendel B S E h)
    (schemaGegner : Gegner → Prop)
    (reduktion : Gegner → Gegner)
    (primitivGegner : Gegner → Prop)
    (c : ENNReal) (spiel ziel : Gegner → Maschine.Lauf E → Prop) : Prop :=
  ∀ A : Gegner, schemaGegner A →
    hb.mu {band | spiel A (hb.replay band)} ≤
      c * hb.mu {band | ziel (reduktion A) (hb.replay band)}

/-- The language's promise beside the goal: every clause the checker accepts
    holds on the lift. The cryptographic forms are not part of this sentence;
    they are GabbroProve duties (see `SchrankenForm`, `ReduktionForm`). -/
def GabbroZielProb (B : Zufallsbindung) (S : Scheduler)
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) : Prop :=
  ∀ hb : Hebebuendel B S E h,
    (∀ pfad wNum wDen pNum pDen, ereignisPflicht B hb pfad wNum wDen pNum pDen) ∧
    (∀ kosten cNum cDen qNum qDen bNum bDen,
      kostenPflicht B hb kosten cNum cDen qNum qDen bNum bDen) ∧
    (∀ Ziel qNum qDen, abschlussPflicht B hb Ziel qNum qDen) ∧
    (∀ Ziel qNum qDen, fortschrittPflicht B hb Ziel qNum qDen)

/-- Non-vacuity of the probabilistic shape: the source admits an event strictly
    inside `(0, 1)`. A degenerate source (or a degenerate instantiation) satisfies
    no instance of this; the coin discharges it in `Erfuellbar`. -/
def ProbNichtLeer (Q : Zufallsquelle) : Prop :=
  ∃ E : Fin Q.anz → Prop, ∃ _ : DecidablePred E,
    0 < Wahrscheinlichkeit Q E ∧ Wahrscheinlichkeit Q E < 1

end Gabbro.Core.Beobachtung
