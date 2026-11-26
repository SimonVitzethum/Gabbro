/-
  File:      core/Core/Annahme/Domaene.lean
  Subject:   ISOLATION DOMAINS (MK-17, design): domains as the authority boundary over the
              existing rights-and-loan model (`Rechte`, `Leihe`, `Zustand.befugt`).

  A unit declares domains; every context belongs to exactly one domain; memory, devices
  and questions of a domain are reachable from other domains only over declared channels.
  The core statement `IsolationAussage` says, over elaborated units (`einheitVon P t`,
  the `NIAkzeptiertAussage` pattern): in every run of an accepted elaborated unit, no
  context touches a cell, device or question of a foreign domain except over a declared
  channel; `DomaenenNIAussage` connects this to the existing flow noninterference (NI
  between domains up to channels). The static checker line `pruefeDomaenen` decides the
  finite declaration (domain count, channel table); domain membership itself is a total
  static function of the context identity, fixed by the declaration. The plan, the static
  line and the checker row (`DomaenenLokal`, `RegelIsolation`) live in
  `Core/Annahme/Lokal.lean`; this file keeps the run-level statements, the witnesses and
  the collection root.

  Strengthened checker (MK-17, designer decision 2026-11-26): the plan the unit carries is the
  finite `Maschine.DomaenenTabelle`; `pruefeDomaenenTab` decides every coherence condition of
  `tabKohaerent` on it, and `DomaenenTabelle.wohlgeformt` is an independent structural condition
  on the finite declaration. Correctness, completeness and equivalence of that line over finite
  tables are proved in `DomaeneBeweise/Pruefer.lean`; the function-based plan below survives only
  as the total-lookup embedding (`tabellePlan`), and a coherence condition that escapes the finite
  table is a proved user obligation in `DomaeneBeweise/Unentscheidbar.lean`.

  Design decisions (designer input, 2026-11-25, MK-17b: `RegelIsolation` is a checker row
  in `Lokal`, head-gated since the rule table covers every form but only heads step):
  * No new `Befehl` constructors (MK-04 owns `Befehl`): domains live beside the
    instruction set, over `Einrichtung.speicherObjekt`, `Zustand.befugt` and `Frage`.
  * Lock words and the event location ride on object `0` through the existing
    `Zelle.objekt` map, so a lock shared across domains is itself a declared channel.
    Device pushes and DMA arrivals are environment behaviour: their observability is
    covered by the NI leg, their authority by the existing `Vollmacht`/`Leihe`
    typestates; the access leg covers register and device authority through `Frage`.
  * All plan data is bundled in `DomaenenPlan` (no free `Prop` fields, no unbound
    function parameters, following the MK-10 family rule); every premise binds the
    plan to the unit or to the declaration.
  * Open prover obligations (not this file): the rule-to-run bridge
    (`RegelIsolation` per form implies `LaufIsolation`), the proof of
    `DomaenenNIAssage` from the flow-NI obligations, and checker soundness of
    `pruefeDomaenen` against `Akzeptiert`.
-/
module

public import Core.Maschine.Start
public import Core.Annahme.Annahme
public import Core.Beobachtung.Satz
public import Core.Ziel.Korrektheit.Pruefer

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Ziel.Korrektheit

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **Static coherence of plan and unit**: every assignment lands inside the declared
    domains. State-independent; the run statement below carries the dynamic part.
    The plan itself, the static line and the checker row (`DomaenenLokal`,
    `RegelIsolation`) live in `Core/Annahme/Lokal.lean`. -/
def DomaenenKohaerenz (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) : Prop :=
  (∀ c : Kontext, plan.kontextDomaene c < plan.domaenen) ∧
  (∀ x : Ort, plan.objektDomaene (E.einrichtung.speicherObjekt x) < plan.domaenen) ∧
  (∀ o : Objekt, plan.geraetDomaene o < plan.domaenen)

/-- A plan step touches foreign state with no channel: a foreign read, a foreign write in
    the declared footprint, or a foreign question. -/
def FremderSchritt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (c : Kontext) (p : SchrittPlan L Ort Wert Bedingung) : Prop :=
  (∃ l ∈ p.lesen, FremdeZelle E plan c l.ort) ∨
  (∃ x ∈ p.fuss, p.schreibt x = true ∧ FremdeZelle E plan c x) ∨
  (∃ q : Frage, p.aktion = .frage q ∧ FremdeFrage plan c q)

/-- **Run-level isolation**: in every admitted run, every context cut respects the domains. -/
def LaufIsolation [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) : Prop :=
  ∀ (h : Umgebung) (ρ : Lauf E), Laeufe E h ρ →
    ∀ (t : Nat) (w : SchrittWahl Wahl) (spur : SchrittSpur Ort Wert),
      ρ.zeit.spur t = some (w, spur) →
      ∀ (c : Kontext) (wahl : Wahl), w = .kontext c wahl → SpurRespektiert E plan c spur

/-- **The core statement (MK-17d) over elaborated units** (the `NIAkzeptiertAussage`
    pattern): in every run of an accepted elaborated unit, no context touches a cell,
    device or question of a foreign domain except over a channel the unit's own table
    declares. The per-form duty comes from the checker row in `Lokal`, through the
    rule-to-run bridge. -/
def IsolationAussage (P : Katalog.Plattform) : Prop :=
  ∀ (t : Gabbro.Core.Ast.Unit),
    Akzeptiert (einheitVon P t) →
    LaufIsolation (einheitVon P t) (tabellePlan (einheitVon P t).domaenen)

/-- Cross-domain traffic is low-labelled: every question about a foreign-domain object
    carries a public label. -/
def KanalTragenNiedrig (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) : Prop :=
  ∀ (c : Kontext) (q : Frage),
    plan.geraetDomaene q.objekt ≠ plan.kontextDomaene c →
    Beobachtung.oeffentlich (E.etiketten.frage q) = true

/-- **NI between domains up to the unit's own channels, over elaborated units** (the
    `NIAkzeptiertAussage` pattern): under low-labelled cross-domain traffic over the
    declared table, the accepted elaborated unit is noninterferent, by the pinned NI leg.
    The channel premise records the design intent; the leg supplies the conclusion. -/
def DomaenenNIAussage (P : Katalog.Plattform) : Prop :=
  ∀ (t : Gabbro.Core.Ast.Unit),
    Akzeptiert (einheitVon P t) →
    KanalTragenNiedrig (einheitVon P t) (tabellePlan (einheitVon P t).domaenen) →
    Beobachtung.Nichtinterferent (einheitVon P t)

/-- **Satisfiability**: a well-formed plan and an accepted unit meet the coherence
    premises and the run isolation jointly. -/
def IsolationErfuellbarAussage : Prop :=
  ∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (plan : DomaenenPlan),
    plan.wohlgeformt ∧ Akzeptiert E ∧ DomaenenKohaerenz E plan ∧ LaufIsolation E plan

/-- **Non-triviality**: the model represents the error — a well-formed plan with a
    foreign step in a unit the checker does not accept — and the static line refuses a
    malformed plan. -/
def IsolationNichtTrivialAussage : Prop :=
  (∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (plan : DomaenenPlan)
      (c : Kontext) (s u : Zustand Unit Unit Unit Unit Unit Unit) (w : Unit)
      (pl : SchrittPlan Unit Unit Unit Unit),
    plan.wohlgeformt ∧ (E.system.regel ()).impl c s w [pl] u ∧
      FremderSchritt E plan c pl ∧ ¬ Akzeptiert E) ∧
  (∃ plan : DomaenenPlan, pruefeDomaenen plan = false)

/-- **The collection root**: the core statement and its NI connection over every
    platform, with both companions. The single pin root for MK-17; the list may only grow. -/
def DomaenenAussage : Prop :=
  (∀ P : Katalog.Plattform, IsolationAussage P) ∧
  (∀ P : Katalog.Plattform, DomaenenNIAussage P) ∧
  IsolationErfuellbarAussage ∧ IsolationNichtTrivialAussage

/-- The single-domain plan: everything owned by domain `0`, no channels. -/
def eineDomaene : DomaenenPlan where
  domaenen := 1
  kontextDomaene := fun _ => 0
  objektDomaene := fun _ => 0
  geraetDomaene := fun _ => 0
  kanaele := []

/-- The single-domain plan passes the static line. -/
theorem eineDomaene_wohlgeformt : eineDomaene.wohlgeformt := rfl

/-- The single-domain plan is coherent with the trivial unit. -/
theorem eineDomaene_kohaerent : DomaenenKohaerenz trivialeEinheit eineDomaene := by
  refine ⟨fun _ => Nat.zero_lt_one, fun _ => Nat.zero_lt_one, fun _ => Nat.zero_lt_one⟩

/-- The trivial unit is accepted (the witness of `akzeptiert_erfuellbar`). -/
theorem akzeptiert_trivial : Akzeptiert trivialeEinheit := by
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_, ⟨Aussen.zulassung_m2 _, ?_⟩, ?_, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · intro i
    exact triviale_regel_lokal i
  · apply aussen_gueltig_aus_kontext
    intro _ _ _ _ _ _ _ step
    cases step with
    | kontext _ _ regel _ =>
      obtain ⟨i, hi, _⟩ := regel
      exact nomatch hi
  · refine ⟨fun _ _ _ => ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩, fun _ => ?_⟩
    constructor
    · intro _ _ _ _ _ h
      cases h.1
    · intro _ _ _ _ _ _ _ _ _ _ _ h
      cases h.1
  · exact schrankenLokal_leer rfl rfl rfl
  · exact Gabbro.Core.Annahme.abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · exact Gabbro.Core.Annahme.domaenenLokal_ohne_kopf _
      Gabbro.Core.Maschine.eineTabelle_akzeptiert fun _ _ => rfl
  · intro ρ _
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨fun ρ _ t op args need => False.elim need, fun ρ _ t => ?_,
      fun _ _ _ _ _ _ hne => (hne rfl).elim⟩
    intro h
    obtain ⟨C, hC⟩ := h
    obtain ⟨hex, hall⟩ := hC
    obtain ⟨c, hc⟩ := hex
    obtain ⟨b, hb, _⟩ := hall c hc
    exact False.elim hb

/-- The trivial system never takes a context step: every recorded context cut is
    impossible, so every run respects every domain. -/
theorem trivial_laufisolation : LaufIsolation trivialeEinheit eineDomaene := by
  intro _ ρ _ t w spur hspur c wahl hw
  subst hw
  have recorded := ρ.zeit.takt t
  rw [hspur] at recorded
  generalize vorEq : ρ.zeit.zustand t = vor at recorded
  generalize ρ.zeit.zustand (t + 1) = nach at recorded
  cases recorded with
  | wartet label _ _ => exact nomatch label
  | schritt label step =>
    cases step with
    | schritt h =>
      cases h with
      | kontext _ _ regel _ =>
        obtain ⟨i, hkopf, _⟩ := regel
        exact nomatch hkopf
      | antwort _ _ =>
        simp at label
      | interrupt _ _ =>
        simp at label
      | absturz _ =>
        simp at label

/-- Satisfiability of the access isolation: the single-domain plan over the trivial unit. -/
theorem isolation_erfuellbar : IsolationErfuellbarAussage :=
  ⟨trivialeEinheit, eineDomaene, eineDomaene_wohlgeformt, akzeptiert_trivial,
    eineDomaene_kohaerent, trivial_laufisolation⟩

/-- A well-formed two-domain plan: the context in domain `0`, the memory object in
    domain `1`, no channels. -/
def verletzungPlan : DomaenenPlan where
  domaenen := 2
  kontextDomaene := fun _ => 0
  objektDomaene := fun _ => 1
  geraetDomaene := fun _ => 0
  kanaele := []

/-- The violating plan passes the static line: the error is representable, not refused. -/
theorem verletzungPlan_wohlgeformt : verletzungPlan.wohlgeformt := rfl

/-- The violating setup: the authority of `gebenEinrichtung` with the single memory
    object moved to domain `1`. -/
def verletzungEinrichtung : Einrichtung Unit Unit Unit Unit Unit Unit Unit :=
  { gebenEinrichtung with speicherObjekt := fun _ => 1 }

/-- The violating rule: every step, ideal and implementation, is permitted. -/
def verletzungRegel : Regel (Zustand Unit Unit Unit Unit Unit Unit)
    (SchrittPlan Unit Unit Unit Unit) Unit :=
  ⟨fun _ _ _ _ _ => True, fun _ _ _ _ _ => True⟩

/-- The violating system: one permissive form at every head. -/
def verletzungSystem : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => verletzungRegel, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

/-- The violating unit on the approved x86-64 rows. -/
def verletzungEinheit : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  katalog := Plattform.x86_64.katalog
  bild := ⟨Bildformat.elf, fun _ => none, []⟩
  einrichtung := verletzungEinrichtung
  system := verletzungSystem
  startdaten := fun _ => ⟨fun _ => (), fun _ => .ruht,
    fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => false, fun _ => 0⟩⟩
  startmedium := fun _ _ => 0
  laden := fun _ _ => none
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := .leer

/-- The violating plan step: write the single cell. -/
def verletzungPlan_schritt : SchrittPlan Unit Unit Unit Unit :=
  ⟨.intern, [], [()], fun _ => true, fun _ => .na, fun _ => ()⟩

/-- The violating state: entirely dead authority. -/
def verletzungZustand : Zustand Unit Unit Unit Unit Unit Unit :=
  Zustand.start (fun _ => ()) (fun _ => .ruht)
    (fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩)
    ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))

/-- The write to the single cell is foreign: its object lives in domain `1`, the context
    in domain `0`, with no channel. -/
theorem verletzung_fremd (c : Kontext) :
    FremderSchritt verletzungEinheit verletzungPlan c verletzungPlan_schritt := by
  refine Or.inr (Or.inl ⟨(), (List.mem_singleton).mpr rfl, rfl, ?_⟩)
  show ¬ verletzungPlan.erlaubt (verletzungPlan.kontextDomaene c)
    (verletzungPlan.objektDomaene (verletzungEinrichtung.speicherObjekt ()))
  intro h
  unfold DomaenenPlan.erlaubt at h
  rcases h with h | h
  · have zero_eq_one : (0 : Nat) = 1 := h
    exact Nat.zero_ne_one zero_eq_one
  · exact List.not_mem_nil h

/-- The violating unit fails the authority obligation: its ideal rule permits a
    footprint step in a state with dead authority. -/
theorem verletzung_nicht_regel_lokal : ¬ RegelLokal verletzungEinheit () := by
  intro h
  have hI := h (.faden 0) verletzungZustand verletzungZustand () verletzungPlan_schritt trivial
  exact befugt_verweigert _ verletzungZustand (.faden 0) verletzungPlan_schritt
    (fun _ => rfl) (Or.inl (fun h => nomatch h)) hI

/-- The checker excludes the violating unit: without live authority it is not accepted. -/
theorem verletzung_nicht_akzeptiert : ¬ Akzeptiert verletzungEinheit := by
  intro h
  exact verletzung_nicht_regel_lokal (h.1.2.1 ())

/-- Non-triviality: the model represents the foreign access and the checker excludes its
    unit, while the static line refuses the empty-domain plan. -/
theorem isolation_nichtTrivial : IsolationNichtTrivialAussage :=
  ⟨⟨verletzungEinheit, verletzungPlan, .faden 0, verletzungZustand, verletzungZustand, (),
    verletzungPlan_schritt, verletzungPlan_wohlgeformt, trivial, verletzung_fremd _,
    verletzung_nicht_akzeptiert⟩,
   ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0, []⟩, rfl⟩⟩

end Gabbro.Core.Annahme
