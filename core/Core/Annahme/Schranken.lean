/-
  File:      core/Core/Annahme/Schranken.lean
  Subject:   The stack and memory checker row of acceptance (PERFECT-MODEL §3.2, §3.7, step M9 B9/B21).

  `SchrankenLokal E` is the decidable local bounds rule over the program's syntax interface,
  the bounds analogue of `RegelLokal`: every ideal step of every form preserves the declared
  stack and memory bounds (`StapelZustand`, `SpeicherZustand` over `E.schranken`), the loader
  establishes them at every ideal cut zero, and the protocol steps preserve them. Open bounds
  stay admitted exactly as today: with `schranken = .leer` every conjunct holds unconditionally,
  so refusal only bites where a finite bound is declared.

  Consequences for the forms (discharged per form, pinned in
  `Beobachtung.SchrankenB9B21Pflichten`): a form whose ideal step can grow the stack or the
  live set (`rufe`, aggregate and text construction, `newSpace` and friends, DMA, region
  binding) is accepted only with a bound premise that refuses — a named halt such as
  `Abschluss.abstieg`, `Abschluss.ueberlauf` or `Rahmen.bindeRegion`'s `ungueltigerBereich` —
  instead of exceeding. What the static analysis cannot bound is refused, never assumed.
  The static never-fires argument (S5 `rufTief`, the B21 `ZeitAb`-analogous computation) is
  progress-side follow-up work; the `ImSchranken` leg only needs that refusal preserves bounds.

  `TiefenBezug` carries the one simulation-side fact the transfer needs: the unit's local
  relation respects the declared depth measure, so `StapelZustand` moves across `Zustandsbezug`
  (memory moves by `ProtokollBezug` alone). For `lokalerBezug = Eq` it holds by `rfl`.
-/
module

public import Core.Maschine.Start
public import Core.Katalog.Start
public import Core.Beobachtung.SchrankenB9B21
public import Core.Verfeinerung.Maschine
public import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι}

/-- The loader obligation of the bounds row: the initial cut of every ideal run satisfies
    the declared stack and memory bounds. Loader data, so no clock facts are needed. -/
def SchrankenStart (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  ∀ {η : I.Lauf E}, I.Laeufe E η →
    StapelZustand E (η.zeit.zustand 0) ∧ SpeicherZustand E (η.zeit.zustand 0)

/-- The per-form obligation of the bounds row: a context step of form `i` preserves the
    stack and memory bounds. Formulated at full-step granularity like `KHRegelPflicht`, so
    the machine wrapper (`FuehrtSchrittAus`) is covered: a growing form discharges this only
    with a bound premise that refuses instead of exceeding. -/
def RegelSchranken (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (i : ι) : Prop :=
  ∀ {η : I.Lauf E}, I.Laeufe E η → ∀ t c w spur vor nach,
    η.zeit.zustand t = vor → E.system.kopf vor c = some i →
    η.zeit.spur t = some (.kontext c w, spur) → η.zeit.zustand (t + 1) = nach →
    I.Schritt E.einrichtung E.system E.katalog η.hw t vor (.kontext c w, spur) nach →
    StapelZustand E vor → SpeicherZustand E vor →
    StapelZustand E nach ∧ SpeicherZustand E nach

/-- The protocol obligation of the bounds row: an answer, interrupt or crash transition
    preserves the declared bounds. Crash installs the recovery entry's start data, whose
    bounds are that entry's own start obligation. -/
def SchrankenProtokoll (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  ∀ {η : I.Lauf E}, I.Laeufe E η → ∀ t w spur vor nach,
    η.zeit.zustand t = vor →
    η.zeit.spur t = some (w, spur) → ProtokollB8Wahl w →
    η.zeit.zustand (t + 1) = nach →
    I.Schritt E.einrichtung E.system E.katalog η.hw t vor (w, spur) nach →
    StapelZustand E vor → SpeicherZustand E vor →
    StapelZustand E nach ∧ SpeicherZustand E nach

/-- The unit's local relation respects the declared depth measure: related locals agree on
    `stapelTiefe` at every context. This is what moves `StapelZustand` across `Zustandsbezug`;
    memory moves by `ProtokollBezug` alone (`speicher_bezug`). -/
def TiefenBezug (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  ∀ l l' : Kontext → Lok, E.lokalerBezug l l' →
    ∀ c, E.schranken.stapelTiefe (l c) = E.schranken.stapelTiefe (l' c)

/-- The bounds row of `Lokal`: loader start, one obligation per form, the shared protocol
    part, and the depth-respecting local relation. Added as the last conjunct of `Lokal`, so
    units with open bounds are accepted exactly as before. -/
structure SchrankenLokal (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop where
  start : SchrankenStart E
  regel : ∀ i, RegelSchranken E i
  protokoll : SchrankenProtokoll E
  bezug : TiefenBezug E

/-- The stack and memory legs of `ImSchranken` at one ideal cut. -/
def SchrankenPrefix (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (η : I.Lauf E) (t : Nat) : Prop :=
  StapelZustand E (η.zeit.zustand t) ∧ SpeicherZustand E (η.zeit.zustand t)

/-- Every prefix of an admitted ideal run satisfies the declared stack and memory bounds, by
    induction over the cuts. Idle ticks are generic; form steps use the per-form obligation,
    protocol steps the shared one. The mirror image of `b9_b21_aus_pflichten` on the ideal
    side; the implementation side follows by simulation transfer (pinned). -/
theorem schranken_prefix_aus_lokal (pflicht : SchrankenLokal E) {η : I.Lauf E}
    (lauf : I.Laeufe E η) (t : Nat) : SchrankenPrefix E η t := by
  induction t with
  | zero => exact pflicht.start lauf
  | succ t ih =>
    have takt := η.zeit.takt t
    cases takt with
    | schritt label step =>
      cases step with
      | kontext normal bereit regel aus =>
        obtain ⟨f, kopf, regelSchritt⟩ := regel
        exact pflicht.regel f lauf t _ _ _ _ _ rfl kopf label rfl
          (.kontext normal bereit ⟨f, kopf, regelSchritt⟩ aus) ih.1 ih.2
      | antwort normal step =>
        exact pflicht.protokoll lauf t _ _ _ _ rfl label trivial rfl
          (.antwort normal step) ih.1 ih.2
      | interrupt normal step =>
        exact pflicht.protokoll lauf t _ _ _ _ rfl label trivial rfl
          (.interrupt normal step) ih.1 ih.2
      | absturz step =>
        exact pflicht.protokoll lauf t _ _ _ _ rfl label trivial rfl (.absturz step) ih.1 ih.2
    | wartet _ gleich _ => unfold SchrankenPrefix; rw [gleich]; exact ih

/-- An absent stack bound admits every local state. Units with open bounds are accepted
    exactly as before; refusal only bites where a finite bound is declared. -/
theorem stapelZustand_leer (h : E.schranken.stapel = none)
    (s : Zustand L Ort Wert Raum Lok Grund) : StapelZustand E s := by
  intro c n eq
  rw [h] at eq
  nomatch eq

/-- An absent memory bound admits every live set. Open regions stay admitted, never refused. -/
theorem speicherZustand_leer (h : E.schranken.speicher = none)
    (s : Zustand L Ort Wert Raum Lok Grund) : SpeicherZustand E s := by
  intro n eq
  rw [h] at eq
  nomatch eq

/-- The identity local relation respects every depth measure. -/
theorem tiefenBezug_eq (h : E.lokalerBezug = Eq) : TiefenBezug E := by
  intro l l' rel c
  rw [h] at rel
  cases rel
  rfl

/-- Related states agree on the live set: the protocol relation fixes everything but the
    form-local state, and liveness depends only on rights and booking extents. -/
theorem speicher_bezug {s i : Zustand L Ort Wert Raum Lok Grund}
    (h : I.Zustandsbezug E s i) : SpeicherZustand E s ↔ SpeicherZustand E i := by
  obtain ⟨proto, _⟩ := h
  have eq : { s with lokal := i.lokal } = i := proto
  have rechte : s.rechte = i.rechte := congrArg (fun z => z.rechte) eq
  have umfang : s.buchung.umfang = i.buchung.umfang :=
    congrArg (fun z => z.buchung.umfang) eq
  unfold SpeicherZustand LebendeZellen
  rw [rechte, umfang]

/-- Related states agree on the stack bound when the local relation respects the depth
    measure. Together with `speicher_bezug` this moves the whole bounds row across the
    simulation, cut by cut. -/
theorem stapel_bezug (bezug : TiefenBezug E) {s i : Zustand L Ort Wert Raum Lok Grund}
    (h : I.Zustandsbezug E s i) : StapelZustand E s ↔ StapelZustand E i := by
  have tief : ∀ c, E.schranken.stapelTiefe (s.lokal c) = E.schranken.stapelTiefe (i.lokal c) :=
    bezug s.lokal i.lokal h.2
  unfold StapelZustand UnterGrenze
  constructor
  · intro vor c n bound
    have := vor c n bound
    rw [tief c] at this
    exact this
  · intro nach c n bound
    have := nach c n bound
    rw [← tief c] at this
    exact this

open Gabbro.Core.Sicherheit.Laufkonstruktion

/-- Start data with unit local state. Rights are irrelevant here: booking starts empty. -/
private def grenzenDaten : Startdaten Unit Unit Unit Unit :=
  ⟨fun _ => (), fun _ => .ruht,
    fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => false, fun _ => 0⟩⟩

/-- Setup with the restart entry on the same start data. -/
private def grenzenEinrichtung : Einrichtung Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (),
    fun _ _ _ => False, fun _ _ => True, ⟨0, 0⟩,
    ⟨.faden 0, 0, fun _ => grenzenDaten, fun _ _ => ()⟩,
    fun _ => 0, fun _ _ _ => none⟩

/-- A rule that never steps, in either machine. -/
private def stillRegel
    : Regel (Zustand Unit Unit Unit Unit Unit Unit) (SchrittPlan Unit Unit Unit Unit) Unit :=
  ⟨fun _ _ _ _ _ => False, fun _ _ _ _ _ => False⟩

/-- A system with no head anywhere: only protocol transitions can fire. -/
private def stillSystem : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => stillRegel, fun _ _ => none, fun _ _ => False, fun _ _ _ => False⟩

/-- The finite-bound witness unit: depth one everywhere, ceiling one on both legs. -/
private def grenzenEinheit : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  katalog := katalog
  bild := bild
  einrichtung := grenzenEinrichtung
  system := stillSystem
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := .leer
  schranken := { Schrankendaten.leer with
    stapel := some 1, speicher := some 1, stapelTiefe := fun _ => 1 }
  startdaten := fun _ => grenzenDaten
  startmedium := fun _ _ => 0
  laden := fun _ _ => none

private theorem grenzen_stapel : grenzenEinheit.schranken.stapel = some 1 := rfl

private theorem grenzen_speicher : grenzenEinheit.schranken.speicher = some 1 := rfl

/-- The start and recovery states book nothing, so nothing is live. -/
private theorem zellen_leer_grenzen {s : Zustand Unit Unit Unit Unit Unit Unit}
    (h : ∀ i, s.buchung.umfang i = []) : LebendeZellen s = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z mem
  change s.rechte.lebt z.1 = true ∧ z.2 < (s.buchung.umfang z.1).length at mem
  rw [h z.1] at mem
  exact Nat.not_lt_zero _ mem.2

/-- The witness meets the checker row: the start cut has depth exactly one and an empty
    live set; the silent rule never steps; answers and interrupts touch only the protocol
    fields; crashes reinstall the start booking, which is empty. -/
private theorem grenzen_schranken : SchrankenLokal grenzenEinheit := by
  refine ⟨?_, ?_, ?_, tiefenBezug_eq rfl⟩
  · intro η lauf
    have hz : η.zeit.zustand 0 = (I.start grenzenEinheit η.start).2 := lauf.2.2.2.1
    rw [hz]
    constructor
    · intro c n eq
      rw [grenzen_stapel] at eq
      obtain rfl := Option.some.inj eq
      exact Nat.le_refl _
    · intro n eq
      rw [grenzen_speicher] at eq
      obtain rfl := Option.some.inj eq
      have nichtsLebt : LebendeZellen (I.start grenzenEinheit η.start).2 = ∅ :=
        zellen_leer_grenzen (fun _ => rfl)
      rw [nichtsLebt, Set.encard_empty]
      exact zero_le
  · intro i η lauf t c w spur vor nach vorEq kf spurEq nachEq step _ _
    exact nomatch kf
  · intro η lauf t w spur vor nach vorEq spurEq wahl nachEq step stapelVor speicherVor
    cases step with
    | kontext _ _ _ _ => exact False.elim wahl
    | antwort _ step =>
      obtain ⟨_, _, _, stateEq⟩ := step
      rw [stateEq]
      exact ⟨stapelVor, speicherVor⟩
    | interrupt _ step =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, stateEq⟩ := step
      rw [stateEq]
      exact ⟨stapelVor, speicherVor⟩
    | absturz step =>
      obtain ⟨_, _, p, _, stateEq⟩ := step
      rw [stateEq]
      constructor
      · intro c n eq
        rw [grenzen_stapel] at eq
        obtain rfl := Option.some.inj eq
        exact Nat.le_refl _
      · intro n eq
        rw [grenzen_speicher] at eq
        obtain rfl := Option.some.inj eq
        have nichtsLebt : LebendeZellen
            (vor.wiederanlauf grenzenEinheit.einrichtung.wiederanlauf t p) = ∅ :=
          zellen_leer_grenzen (fun _ => rfl)
        rw [nichtsLebt, Set.encard_empty]
        exact zero_le

/-- Joint satisfiability of the checker row with a real finite bound: depth exactly one
    against ceiling one, empty live set against ceiling one, on an admitted ideal run.
    The protocol cases above are non-vacuous: answers, interrupts and crashes are all
    possible on this unit. -/
theorem schrankenLokal_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (η : I.Lauf E)
      (s : Zustand Unit Unit Unit Unit Unit Unit),
      SchrankenLokal E ∧ I.Laeufe E η ∧ η.zeit.zustand 0 = s ∧
      SchrankenPrefix E η 0 ∧ E.schranken.stapel = some 1 ∧ E.schranken.speicher = some 1 ∧
      (∀ c, E.schranken.stapelTiefe (s.lokal c) = 1) ∧ (LebendeZellen s).encard = 0 := by
  obtain ⟨_, zul⟩ := zulStart_erfuellbar (erlaubt leer) bild_gueltig
  obtain ⟨η, lauf, _, _⟩ := I.lauf_mit_hw grenzenEinheit (erlaubt leer) zul (konform leer)
  have hz : η.zeit.zustand 0 = (I.start grenzenEinheit η.start).2 := lauf.2.2.2.1
  refine ⟨grenzenEinheit, η, (I.start grenzenEinheit η.start).2,
    grenzen_schranken, lauf, hz, grenzen_schranken.start lauf,
    rfl, rfl, fun _ => rfl, ?_⟩
  have nichtsLebt : LebendeZellen (I.start grenzenEinheit η.start).2 = ∅ :=
    zellen_leer_grenzen (fun _ => rfl)
  rw [nichtsLebt, Set.encard_empty]

end Gabbro.Core.Annahme
