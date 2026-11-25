/-
  File:      core/Core/Annahme/Domaene.lean
  Subject:   ISOLATION DOMAINS (MK-17, design): domains as the authority boundary over the
              existing rights-and-loan model (`Rechte`, `Leihe`, `Zustand.befugt`).

  A unit declares domains; every context belongs to exactly one domain; memory, devices
  and questions of a domain are reachable from other domains only over declared channels.
  The core statement `IsolationAussage` says: in every run of an accepted unit, no context
  touches a cell, device or question of a foreign domain except over a declared channel;
  `DomaenenNIAussage` connects this to the existing flow noninterference (NI between
  domains up to channels). The static checker line `pruefeDomaenen` decides the finite
  declaration (domain count, channel table); domain membership itself is a total static
  function of the context identity, fixed by the declaration.

  Design decisions (designer input, 2026-11-25):
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
public import Core.Maschine.Ergebnis
public import Core.Annahme.Annahme
public import Core.Beobachtung.Satz

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- An isolation domain identity. -/
abbrev Domaene := Nat

/-- **The static domain declaration of a unit**: the number of domains, the total static
    assignment of every context, memory object and outside object to its owning domain,
    and the declared channels between domains. Pure data; every premise below binds it
    to the unit or to the declaration. -/
structure DomaenenPlan where
  domaenen : Nat
  kontextDomaene : Kontext → Domaene
  objektDomaene : Nat → Domaene
  geraetDomaene : Objekt → Domaene
  kanaele : List (Domaene × Domaene)

/-- **The static checker line**: the declaration is finite and well-scoped — at least one
    domain, every channel between declared domains. Domain membership itself needs no
    enumeration: it is a total static function of the context identity. -/
def pruefeDomaenen (plan : DomaenenPlan) : Bool :=
  decide (0 < plan.domaenen) &&
    plan.kanaele.all (fun k => decide (k.1 < plan.domaenen) && decide (k.2 < plan.domaenen))

/-- A plan is well-formed exactly when the static line accepts it. -/
def DomaenenPlan.wohlgeformt (plan : DomaenenPlan) : Prop :=
  pruefeDomaenen plan = true

/-- The checker line decides well-formedness, by definition. -/
theorem pruefeDomaenen_korrekt (plan : DomaenenPlan) :
    pruefeDomaenen plan = true → plan.wohlgeformt :=
  fun h => h

/-- **Static coherence of plan and unit**: every assignment lands inside the declared
    domains. State-independent; the run statement below carries the dynamic part. -/
def DomaenenKohaerenz (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) : Prop :=
  (∀ c : Kontext, plan.kontextDomaene c < plan.domaenen) ∧
  (∀ x : Ort, plan.objektDomaene (E.einrichtung.speicherObjekt x) < plan.domaenen) ∧
  (∀ o : Objekt, plan.geraetDomaene o < plan.domaenen)

/-- Same domain, or a declared channel from the acting domain to the owning one. -/
def DomaenenPlan.erlaubt (plan : DomaenenPlan) (von nach : Domaene) : Prop :=
  von = nach ∨ (von, nach) ∈ plan.kanaele

/-- The cell lies in a foreign domain with no channel from the acting context. -/
def FremdeZelle (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (c : Kontext) (x : Ort) : Prop :=
  ¬ plan.erlaubt (plan.kontextDomaene c) (plan.objektDomaene (E.einrichtung.speicherObjekt x))

/-- The question targets a foreign-domain object with no channel from the acting context. -/
def FremdeFrage (plan : DomaenenPlan) (c : Kontext) (q : Frage) : Prop :=
  ¬ plan.erlaubt (plan.kontextDomaene c) (plan.geraetDomaene q.objekt)

/-- A plan step touches foreign state with no channel: a foreign read, a foreign write in
    the declared footprint, or a foreign question. -/
def FremderSchritt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (c : Kontext) (p : SchrittPlan L Ort Wert Bedingung) : Prop :=
  (∃ l ∈ p.lesen, FremdeZelle E plan c l.ort) ∨
  (∃ x ∈ p.fuss, p.schreibt x = true ∧ FremdeZelle E plan c x) ∨
  (∃ q : Frage, p.aktion = .frage q ∧ FremdeFrage plan c q)

/-- One recorded cut respects the domains: every memory access of the acting context
    stays in its domain or uses a channel, and every issued question is asked by the
    context the trace names, in its domain or over a channel. Lazy initial writes and
    environment arrivals are not program accesses. -/
def SpurRespektiert (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (c : Kontext) (spur : SchrittSpur Ort Wert) : Prop :=
  (∀ a l, (a, l) ∈ spur.speicher → a = .kontext c → ¬ FremdeZelle E plan c l.ort) ∧
  (∀ ev : FrageEreignis, Ereignis.frage ev ∈ spur.aussen →
    ∀ d : Kontext, d.nummer = ev.context → ¬ FremdeFrage plan d ev.question)

/-- **Run-level isolation**: in every admitted run, every context cut respects the domains. -/
def LaufIsolation [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) : Prop :=
  ∀ (h : Umgebung) (ρ : Lauf E), Laeufe E h ρ →
    ∀ (t : Nat) (w : SchrittWahl Wahl) (spur : SchrittSpur Ort Wert),
      ρ.zeit.spur t = some (w, spur) →
      ∀ (c : Kontext) (wahl : Wahl), w = .kontext c wahl → SpurRespektiert E plan c spur

/-- **The core statement (MK-17)**: in every run of an accepted unit, no context touches
    a cell, device or question of a foreign domain except over a declared channel. -/
def IsolationAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (plan : DomaenenPlan),
    plan.wohlgeformt → Akzeptiert E → DomaenenKohaerenz E plan → LaufIsolation E plan

/-- Cross-domain traffic is low-labelled: every question about a foreign-domain object
    carries a public label. -/
def KanalTragenNiedrig (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) : Prop :=
  ∀ (c : Kontext) (q : Frage),
    plan.geraetDomaene q.objekt ≠ plan.kontextDomaene c →
    Beobachtung.oeffentlich (E.etiketten.frage q) = true

/-- **NI between domains up to channels**: under low-labelled cross-domain traffic, the
    existing flow noninterference covers the domains. -/
def DomaenenNIAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (plan : DomaenenPlan),
    Akzeptiert E → KanalTragenNiedrig E plan → Beobachtung.Nichtinterferent E

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

/-- **The collection root**: the core statement, its NI connection, and both companions.
    The single pin root for MK-17; the list may only grow. -/
def DomaenenAussage : Prop :=
  IsolationAussage ∧ DomaenenNIAussage ∧ IsolationErfuellbarAussage ∧ IsolationNichtTrivialAussage

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
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_, ⟨Aussen.zulassung_m2 _, ?_⟩, ?_, ?_⟩,
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
