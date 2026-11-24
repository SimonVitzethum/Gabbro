/-
  File:      core/Core/Beobachtung/SchrankenB9B21Pflichten.lean
  Subject:   Pinned stack and memory duties for Hy4 provers (PERFECT-MODEL §3.7, step M9 B9/B21).

  These `...Aussage` pin the open proof work that turns the checker's bounds row
  (`Annahme.SchrankenLokal`, proved satisfiable with a real finite bound by
  `Annahme.schrankenLokal_erfuellbar`) into the implementation-side obligations of
  `RessourcenPflichten`:

  * helpers (`stapelErhalten`, `speicherErhalten`, `antwortErhalten`,
    `unterbrechungErhalten`, `absturzSchranken`): measure-level preservation facts about
    the machine's protocol transitions — no program content;
  * bridge (`schrankenStartAusLokal`, `schrankenRegelAusLokal`,
    `schrankenProtokollAusLokal`, `schrankenTransfer`): from the checker row (plus the
    simulation matching, M6 side) to the per-form implementation obligations;
  * families (`rufSchranken`, `aggregatSchranken`, `textSchranken`,
    `speicherverwaltungSchranken`, `regionSchranken`, `kontrollflussSkalarSchranken`):
    the `RegelSchranken` instances for the growing forms — each states the bound premise
    (refuse instead of exceed) its ideal rule must carry. Undecidable static bounds refuse
    the unit; open regions stay admitted.

  Blast-radius note: `Mem/Proofs/Flush` and `Mem/Execution` are untouched (the Sonnet
  flush work runs there); the flush-family statement lives here and constrains only the
  rule-level bound premise, not the execution proofs.
-/
module

public import Core.Beobachtung.SchrankenB9B21
public import Core.Annahme.Schranken
public import Core.Verfeinerung.Simulation
public import Core.Ast.Semantik.Runtime.Regeln
public import Core.Ast.LowLevel.Mem.Meaning

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast

/-- A step that grows no context's declared depth preserves the stack bound.
    Difficulty: leicht. Sketch: unfold `StapelZustand`/`UnterGrenze`; the need only
    shrinks, so `le_trans` with the depth hypothesis closes each bound. -/
def stapelErhaltenAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (vor nach : Zustand L Ort Wert Raum Lok Grund),
    StapelZustand E vor →
    (∀ c, E.schranken.stapelTiefe (nach.lokal c) ≤ E.schranken.stapelTiefe (vor.lokal c)) →
    StapelZustand E nach

/-- A step that adds no live cell preserves the memory bound.
    Difficulty: mittel. Sketch: the live set only shrinks, so Mathlib `encard`
    monotonicity for subsets (`Set.encard_le_encard`) transports the bound. -/
def speicherErhaltenAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (vor nach : Zustand L Ort Wert Raum Lok Grund),
    SpeicherZustand E vor →
    LebendeZellen nach ⊆ LebendeZellen vor →
    SpeicherZustand E nach

/-- An answer arrival preserves both bounds: it appends only to the answer log and the
    outside history, leaving rights, booking extents and locals untouched.
    Difficulty: leicht. Sketch: destructure `AntwortSchritt`; rewrite with
    `Antwort.antwort_global` (`antworten`/`verbraucht` only); rights, booking and locals
    are syntactically unchanged, so both predicates transfer by `rfl`-rewrites. -/
def antwortErhaltenAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {k run t a spur s s'},
    StapelZustand E s → SpeicherZustand E s →
    AntwortSchritt E.einrichtung k run t a s spur s' →
    StapelZustand E s' ∧ SpeicherZustand E s'

/-- An interrupt delivery preserves both bounds: the entry starts a fresh handler on its
    core and records the consumed offer, leaving rights, booking extents and locals
    (including the handler's) untouched.
    Difficulty: leicht. Sketch: unfold `Zustandseintritt` (only `kerne`/`status`/
    `geliefert` change); both predicates quantify over unchanged fields only. -/
def unterbrechungErhaltenAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {run t id spur s s'},
    StapelZustand E s → SpeicherZustand E s →
    UnterbrechungsSchritt E.einrichtung run t id s spur s' →
    StapelZustand E s' ∧ SpeicherZustand E s'

/-- A crash preserves both bounds provided the recovery entry's start data meets them:
    its locals are within the stack bound and its rights admit no live cell on the
    durable booking, so the wiped volatile state contributes nothing. Without that
    start-data discipline the memory leg is false (durable allocations survive the crash
    by design).
    Difficulty: mittel. Sketch: rewrite with `AbsturzSchritt.genau` to
    `s.wiederanlauf`; the post-state takes locals and rights from `w.daten` and booking
    from the durable snapshot; apply the two start-data hypotheses. -/
def absturzSchrankenAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {region w k run t spur s s'},
    (∀ (p : PersistZustand) (c : Kontext),
      UnterGrenze E.schranken.stapel
        (E.schranken.stapelTiefe ((w.daten p.dauerhaft).lokal c)) ∧
      ∀ z, z ∈ LebendeZellen { s.wiederanlauf w t p with
        rechte := (w.daten p.dauerhaft).rechte } → False) →
    StapelZustand E s → SpeicherZustand E s →
    AbsturzSchritt region w k run t s spur s' →
    StapelZustand E s' ∧ SpeicherZustand E s'

/-- The loader duty follows from the checker row: the implementation cut zero is related
    to the ideal cut zero, which meets the bounds by `SchrankenStart`.
    Difficulty: leicht-mittel. Sketch: the simulation gives `I.Sim`; `Laufabgleich.zustand`
    at `0` yields the related ideal state; `SchrankenStart` at the ideal cut zero plus
    `speicher_bezug`/`stapel_bezug` (with `pflicht.bezug`) transfer both legs. -/
def schrankenStartAusLokalAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form),
    SchrankenLokal E →
    (∀ {h : Umgebung} {ρ : Maschine.Lauf E}, Laeufe E h ρ →
      ∃ η : I.Lauf E, I.Laeufe E η ∧ I.Sim E ρ η) →
    ressourcenStartAussage E

/-- The per-form implementation duty follows from the checker row plus the step match: a
    matched ideal step preserves bounds by `RegelSchranken` (ideal pre-bounds come from
    `schranken_prefix_aus_lokal` at the aligned tick, post-bounds transfer back across the
    match); a private stutter has an empty trace and keeps the relation, so memory is kept
    by the empty-trace `Speicherfolge` lemmas and the stack by the form's mid-unit lokal
    invariant (per-form private-step discipline, M6 side).
    Difficulty: schwer. Sketch: as above; the matched case chains
    `schranken_prefix_aus_lokal`, `pflicht.regel f`, `speicher_bezug`/`stapel_bezug`; the
    private case is `SpurAbgleich.privat` plus the two preservation halves. -/
def schrankenRegelAusLokalAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (f : Form),
    SchrankenLokal E →
    (∀ {h : Umgebung} {ρ : Maschine.Lauf E}, Laeufe E h ρ →
      ∃ η : I.Lauf E, I.Laeufe E η ∧ I.Sim E ρ η) →
    I.RegelSimSchritt E f → ressourcenRegelAussage E f

/-- The protocol duty follows from the checker row: answers and interrupts match ideal
    steps across the protocol relation (`ProtokollBezug.antwort`/`.interrupt`, which keep
    the local state), crashes share the identical `AbsturzSchritt` on both machines.
    Difficulty: mittel. Sketch: match each protocol step to its ideal counterpart, apply
    `pflicht.protokoll` with ideal pre-bounds from `schranken_prefix_aus_lokal`, transfer
    back with the bezug lemmas; the crash case additionally needs the recovery start-data
    discipline of `absturzSchrankenAussage`. -/
def schrankenProtokollAusLokalAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form),
    SchrankenLokal E →
    (∀ {h : Umgebung} {ρ : Maschine.Lauf E}, Laeufe E h ρ →
      ∃ η : I.Lauf E, I.Laeufe E η ∧ I.Sim E ρ η) →
    ressourcenProtokollAussage E

/-- The whole-run transfer, cut by cut: the ideal bounds conclusion
    (`schranken_prefix_aus_lokal`, proved) moves across the per-tick state relation to
    every implementation cut. This is the generic half of the bridge; the simulation
    itself (`I.Sim` from acceptance, M6) is the hypothesis.
    Difficulty: mittel. Sketch: induction-free — at each tick `t`, the related ideal
    state satisfies both legs by `schranken_prefix_aus_lokal`; `speicher_bezug` and
    `stapel_bezug` (with `pflicht.bezug`) move them across `I.Zustandsbezug`. -/
def schrankenTransferAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Maschine.Lauf E) (η : I.Lauf E),
    SchrankenLokal E → I.Laeufe E η →
    (∀ t, ∃ s, ρ.zeit.zustand t = some s ∧ I.Zustandsbezug E s (η.zeit.zustand t)) →
    ∀ t, RessourcenPrefix E ρ t

/-- The call form meets the checker row once its ideal rule refuses over-bound calls:
    every ideal `rufe` step either fits the pushed frame under a declared finite stack
    bound or takes a named halt (`abstieg`, `ungueltigerRuf`) without pushing. The static
    never-fires argument (S5 `rufTief` over finite call trees, `function_rekursionstiefe`
    for `decreases`-measured recursion) is progress-side follow-up; for the bounds leg
    refusal suffices. Joint satisfiability with a refusing rule is M6 elaboration work;
    the row-level finite-bound witness is `Annahme.schrankenLokal_erfuellbar`.
    Difficulty: schwer. Sketch: case split on the rule premise; the fit case pushes
    exactly one continuation (`Rahmen.ruf`) so depth grows by one under the bound; the
    halt case keeps `fortsetzungen` (`Rahmen.halt` only sets `stopp`), so
    `stapelErhaltenAussage` applies; memory is untouched by the `intern` wrapper
    (`FuehrtAus.intern` keeps rights and booking). -/
def rufSchrankenAussage : Prop :=
  ∀ (E : Einheit PUnit PUnit Int PUnit Semantik.Rahmen PUnit PUnit PUnit Semantik.Befehl)
    (tiefe : ∀ r : Semantik.Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length)
    (name : Identifier) (args : List (Ty .value)) (bind : Option (Ty .value)),
    (∀ (c : Kontext) (s u : Semantik.Zustand) (w : PUnit) (plans : List Semantik.Plan),
      (E.system.regel (Semantik.Befehl.rufe name args bind)).ideal c s w plans u →
      ∀ n, E.schranken.stapel = some n →
        ((s.lokal c).fortsetzungen.length + 1 ≤ n ∨ (u.lokal c).stopp.isSome) ∧
        ((u.lokal c).stopp.isSome →
          (u.lokal c).fortsetzungen = (s.lokal c).fortsetzungen)) →
    RegelSchranken E (Semantik.Befehl.rufe name args bind)

/-- Aggregate construction meets the checker row: `baueArray`/`baueTupel`/`baueRecord`/
    `baueVariante` build values inside the frame's temporaries (no booking change), so
    both legs are preserved once the depth interpretation is fixed.
    Difficulty: mittel. Sketch: `Befehl.auswerten` for these constructors only writes
    `temp` slots (`Rahmen.schreibe`); continuations, rights and booking are unchanged, so
    both legs follow by `stapelErhaltenAussage`/`speicherErhaltenAussage` with reflexive
    inclusions, through the `intern` wrapper. -/
def aggregatSchrankenAussage : Prop :=
  ∀ (E : Einheit PUnit PUnit Int PUnit Semantik.Rahmen PUnit PUnit PUnit Semantik.Befehl)
    (tiefe : ∀ r : Semantik.Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length),
    (∀ (ziel : Nat) (element : Ty .value) (count : Nat),
      RegelSchranken E (Semantik.Befehl.baueArray ziel element count)) ∧
    (∀ (ziel : Nat) (types : List (Ty .value)),
      RegelSchranken E (Semantik.Befehl.baueTupel ziel types)) ∧
    (∀ (ziel : Nat) (name : List Char) (labels : List Identifier) (types : List (Ty .value))
      (sources : List Nat),
      RegelSchranken E (Semantik.Befehl.baueRecord ziel name labels types sources)) ∧
    (∀ (ziel : Nat) (name : List Char) (labels : List Identifier) (cases : List (Option (Ty .value)))
      (index : Fin cases.length),
      RegelSchranken E (Semantik.Befehl.baueVariante ziel name labels cases index))

/-- Bounded byte strings meet the checker row: `textLiteral`/`textConcat`/`substring`
    build values in temporaries (no booking change), so both legs are preserved once the
    depth interpretation is fixed. Slicing stays inside the checked capacities through
    the existing `teilfolge` guard row.
    Difficulty: mittel. Sketch: as for aggregates — temporaries only (`Rahmen.schreibe`);
    the `substring` capacity premise is the `waechterBedarf .teilfolge` guard, already
    part of `WaechterHalten`. -/
def textSchrankenAussage : Prop :=
  ∀ (E : Einheit PUnit PUnit Int PUnit Semantik.Rahmen PUnit PUnit PUnit Semantik.Befehl)
    (tiefe : ∀ r : Semantik.Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length),
    (∀ (ziel : Nat) (decoded : List Char),
      RegelSchranken E (Semantik.Befehl.textLiteral ziel decoded)) ∧
    (∀ (basis a b : Nat),
      RegelSchranken E (Semantik.Befehl.textConcat basis a b)) ∧
    (∀ (basis capacity : Nat),
      RegelSchranken E (Semantik.Befehl.substring basis capacity))

/-- Low-level space management meets the checker row once each allocating rule carries
    its ceiling premise: growers fit the post-state live set under a declared finite
    memory ceiling, non-growers keep the live set included and the depth nonincreasing;
    open (`none`) ceilings admit every step, exactly as today. `flushSpace` moves no
    allocation (execution proofs in `Mem/Execution` untouched). DMA accounts its
    descriptor and payload extents against the same ceiling.
    Difficulty: mittel-schwer. Sketch: per constructor — stack via `stapelErhaltenAussage`
    from the depth premise; memory via the fit disjunct directly or
    `speicherErhaltenAussage` via the inclusion disjunct; the wrapper only resolves the
    graph (`FuehrtSchrittAus`), never the booking. -/
def speicherverwaltungSchrankenAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl LowLevel.MemInstruction)
    (op : LowLevel.MemInstruction),
    (∀ (c : Kontext) (s u : Zustand L Ort Wert Raum Lok Grund) (w : Wahl)
      (plans : List (SchrittPlan L Ort Wert Bedingung)),
      (E.system.regel op).ideal c s w plans u →
      ∀ n, E.schranken.speicher = some n →
        ((LebendeZellen u).encard ≤ n ∨ LebendeZellen u ⊆ LebendeZellen s) ∧
        ∀ d, E.schranken.stapelTiefe (u.lokal d) ≤ E.schranken.stapelTiefe (s.lokal d)) →
    RegelSchranken E op

/-- Region binding meets the checker row: `bindeRegion` already refuses
    (`Rahmen.bindeRegion` returns the named halt `ungueltigerBereich`) when the slot is
    missing, ungranted, borrowed or the extent fails — never an unchecked bind. A bound
    region additionally checks the extent against its ceiling; open regions admit.
    Difficulty: mittel. Sketch: both refusal and success paths keep `fortsetzungen`
    (`halt` only sets `stopp`; success extends `lokale` only) and change no booking, so
    both legs follow by the preservation helpers through the `intern` wrapper. -/
def regionSchrankenAussage : Prop :=
  ∀ (E : Einheit PUnit PUnit Int PUnit Semantik.Rahmen PUnit PUnit PUnit Semantik.Befehl)
    (tiefe : ∀ r : Semantik.Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length)
    (receiver : Nat) (init : LowLevel.RegionInitializer),
    RegelSchranken E (Semantik.Befehl.bindeRegion receiver init)

/-- Non-growing control and scalar forms meet the checker row once their step-level
    footprint is fixed: depth nonincreasing and live set included across the full ideal
    step. M6 discharges the footprint per form by `rfl` on `Befehl.auswerten` (temporaries,
    program counter and bounded counters only).
    Difficulty: leicht-mittel. Sketch: `stapelErhaltenAussage` plus
    `speicherErhaltenAussage` with the two footprint facts. -/
def kontrollflussSkalarSchrankenAussage : Prop :=
  ∀ (E : Einheit PUnit PUnit Int PUnit Semantik.Rahmen PUnit PUnit PUnit Semantik.Befehl)
    (tiefe : ∀ r : Semantik.Rahmen, E.schranken.stapelTiefe r = r.fortsetzungen.length)
    (b : Semantik.Befehl),
    (∀ {η : I.Lauf E}, I.Laeufe E η → ∀ t c w spur vor nach,
      η.zeit.zustand t = vor → E.system.kopf vor c = some b →
      η.zeit.spur t = some (.kontext c w, spur) → η.zeit.zustand (t + 1) = nach →
      I.Schritt E.einrichtung E.system E.katalog η.hw t vor (.kontext c w, spur) nach →
      (∀ d, E.schranken.stapelTiefe (nach.lokal d) ≤ E.schranken.stapelTiefe (vor.lokal d)) ∧
      LebendeZellen nach ⊆ LebendeZellen vor) →
    RegelSchranken E b

end Gabbro.Core.Beobachtung
