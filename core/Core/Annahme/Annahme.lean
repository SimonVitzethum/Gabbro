/-
  File:      core/Core/Annahme/Annahme.lean
  Subject:   Acceptance and its satisfiability (PERFECT-MODEL §3.2, step M5).

  `Akzeptiert E := Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E`: the perfect checker over the
  syntax, `I` and the catalogue only. Acceptance is a FUNCTION OF THE UNIT ALONE: the clause
  table and the guard uses are the canonical values determined by the unit
  (`kanonischeKlauseln`, `kanonischeVerwendung` — M6 computes them from the AST); `Akzeptiert`
  takes no type-class instance arguments, so no free choice of tables can make it hold
  trivially. `akzeptiert_erfuellbar` proves the three conjuncts hold jointly for a concrete
  trivial-syntax system, and `geschlossen_nicht_akzeptiert` with `geschlossen_erfuellbar`
  proves acceptance is not vacuous in the refusal direction. Non-vacuity of the two local
  obligations: `stale_nicht_aussen_gueltig` (a system emitting a stale-handle question fails
  `AussenGueltig`) and `unbefugt_nicht_regel_lokal` (a step touching an unowned location fails
  `RegelLokal`), beside their satisfiability (`aussen_gueltig_ohne_fragen`, `befugt_mit_griff`,
  `befugt_erfuellbar` in `Lokal.lean`).
-/
module

public import Core.Annahme.Lokal
public import Core.Annahme.Klauseln
public import Core.Annahme.Waechter

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **`Akzeptiert E := Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E`** (§3.2): the perfect
    checker. It may use only the syntax, `I` and the catalogue — never the implementation
    machine, images, runs or an error notion. `I` never mentions `Akzeptiert`. A function of
    the unit alone: no instance arguments, the tables are canonical. -/
def Akzeptiert [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    Prop :=
  Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E

/-- Acceptance implies a well-formed catalogue selection — the `Akzeptiert`-conjunct of
    `NichtLeer` (§2.1), from `Lokal`. -/
theorem akzeptiert_katalog [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (h : Akzeptiert E) : KatalogWohlgeformt E.katalog :=
  h.1.1

/-- The trivial rule: no implementation step, no `I` step. -/
def trivialesRegel
    : Regel (Zustand Unit Unit Unit Unit Unit Unit) (SchrittPlan Unit Unit Unit Unit) Unit :=
  ⟨fun _ _ _ _ => False, fun _ _ _ _ _ => False⟩

/-- The trivial system: one form with no steps, no head anywhere, nothing finished, never
    blocked. -/
def trivialesSystem : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => trivialesRegel, fun _ _ => none, fun _ _ => False, fun _ _ _ => False⟩

/-- The trivial unit on the approved x86-64 rows. -/
def trivialeEinheit : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  katalog := Plattform.x86_64.katalog
  bild := ⟨Bildformat.elf, fun _ => none, []⟩
  einrichtung := ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (),
    fun _ _ _ => False, fun _ _ => True, ⟨0, 0⟩,
    ⟨.faden 0, 0,
      fun _ => ⟨fun _ => (), fun _ => .ruht,
        fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
        ⟨fun _ => true, fun _ => 0⟩⟩,
      fun _ _ => ()⟩⟩
  system := trivialesSystem
  startdaten := fun _ => ⟨fun _ => (), fun _ => .ruht,
    fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 0⟩⟩
  startmedium := fun _ _ => 0
  laden := fun _ _ => none

/-- The trivial form meets the authority obligation: it never steps. -/
theorem triviale_regel_lokal (i : Unit) : RegelLokal trivialeEinheit i := by
  refine ⟨fun c s u plan h => False.elim h, fun c s u w plan h => False.elim h⟩

/-- The trivial implementation machine emits no outside question: the only rule never fires,
    and arrivals, deliveries and crashes carry no question event. -/
theorem triviale_impl_stumm (run : HwLauf) (t : Nat)
    (s : Zustand Unit Unit Unit Unit Unit Unit) (spur : SchrittSpur Unit Unit)
    (s' : Zustand Unit Unit Unit Unit Unit Unit)
    (step : ImplSchritt trivialeEinheit.einrichtung trivialeEinheit.system
      trivialeEinheit.katalog run t s spur s')
    (ev : FrageEreignis) : Ereignis.frage ev ∉ spur.aussen := by
  intro mem
  cases step with
  | kontext _ _ regel _ =>
    obtain ⟨i, hi, _⟩ := regel
    exact nomatch hi
  | antwort _ h =>
    exact frage_absurd_mem (by rw [h.2.1] at mem; exact mem) (by intro hcon; cases hcon)
  | interrupt _ h =>
    obtain ⟨_, _, _, _, _, _, _, _, hEq, _, _⟩ := h
    exact frage_absurd_mem (by rw [hEq] at mem; exact mem) (by intro hcon; cases hcon)
  | absturz h =>
    obtain ⟨_, hEq, _⟩ := h
    exact frage_absurd_mem (by rw [hEq] at mem; exact mem) (by intro hcon; cases hcon)

/-- The trivial ideal machine emits no outside question either. -/
theorem triviale_ideal_stumm (run : HwLauf) (t : Nat)
    (s : Zustand Unit Unit Unit Unit Unit Unit) (w : I.SchrittWahl Unit)
    (spur : SchrittSpur Unit Unit) (s' : Zustand Unit Unit Unit Unit Unit Unit)
    (step : I.Schritt trivialeEinheit.einrichtung trivialeEinheit.system
      trivialeEinheit.katalog run t s (w, spur) s')
    (ev : FrageEreignis) : Ereignis.frage ev ∉ spur.aussen := by
  intro mem
  cases step with
  | kontext _ _ regel _ =>
    obtain ⟨i, hi, _⟩ := regel
    exact nomatch hi
  | antwort _ h =>
    exact frage_absurd_mem (by rw [h.2.1] at mem; exact mem) (by intro hcon; cases hcon)
  | interrupt _ h =>
    obtain ⟨_, _, _, _, _, _, _, _, hEq, _, _⟩ := h
    exact frage_absurd_mem (by rw [hEq] at mem; exact mem) (by intro hcon; cases hcon)
  | absturz h =>
    obtain ⟨_, hEq, _⟩ := h
    exact frage_absurd_mem (by rw [hEq] at mem; exact mem) (by intro hcon; cases hcon)

/-- **Satisfiability of acceptance**: a concrete (trivial-syntax) system where all three
    conjuncts hold jointly: no uses to guard, nothing written to violate, never blocked. -/
theorem akzeptiert_erfuellbar : ∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit),
    Akzeptiert E := by
  refine ⟨trivialeEinheit, ⟨Plattform.katalog_wohlgeformt .x86_64, ?_, ⟨Aussen.zulassung_m2 _, ?_⟩⟩,
    ?_, ?_⟩
  · intro i
    exact triviale_regel_lokal i
  · exact aussen_gueltig_ohne_fragen _ triviale_impl_stumm triviale_ideal_stumm
  · intro ρ _
    exact ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩
  · refine ⟨fun ρ _ t op args need => False.elim need, fun ρ _ t => ?_⟩
    intro h
    obtain ⟨C, hC⟩ := h
    obtain ⟨hex, hall⟩ := hC
    obtain ⟨c, hc⟩ := hex
    obtain ⟨b, hb, _⟩ := hall c hc
    exact False.elim hb

/-- **A system with a closed waiting set at an `I` cut is not accepted.** -/
theorem geschlossen_nicht_akzeptiert [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (ρ : I.Lauf E) (hρ : I.Laeufe E ρ) (t : I.Schnitt E ρ)
    (C : Kontext → Prop) (h : GeschlossenWartend E (ρ.zeit.zustand t.val) C) :
    ¬ Akzeptiert E := by
  intro ha
  exact ha.2.2.2 ρ hρ t ⟨C, h⟩

/-- Two locks held cross-wise: each holder waits on the lock the other holds. -/
def kreuzSperren : Bool → SperrZustand
  | false => ⟨some (.faden 1), []⟩
  | true => ⟨some (.faden 0), []⟩

/-- Both contexts wait on the lock the other holds. -/
def kreuzBlockiert : Zustand Bool Unit Unit Unit Unit Unit → Kontext → Blockade Bool Unit → Prop
  | _, .faden 0, .sperre false => True
  | _, .faden 1, .sperre true => True
  | _, _, _ => False

/-- The cross-waiting rule: silent in both machines. -/
def kreuzRegel
    : Regel (Zustand Bool Unit Unit Unit Unit Unit) (SchrittPlan Bool Unit Unit Unit) Unit :=
  ⟨fun _ _ _ _ => False, fun _ _ _ _ _ => False⟩

/-- The cross-waiting system: one silent form, heads nowhere, nothing finished. -/
def kreuzSystem : MaschinenSystem Bool Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => kreuzRegel, fun _ _ => none, fun _ _ => False, kreuzBlockiert⟩

/-- The cross-waiting unit on the approved x86-64 rows. -/
def kreuzEinheit : Einheit Bool Unit Unit Unit Unit Unit Unit Unit Unit where
  katalog := Plattform.x86_64.katalog
  bild := ⟨Bildformat.elf, fun _ => none, []⟩
  einrichtung := ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (),
    fun _ _ _ => False, fun _ _ => True, ⟨0, 0⟩,
    ⟨.faden 0, 0,
      fun _ => ⟨fun _ => (), fun _ => .ruht,
        fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
        ⟨fun _ => true, fun _ => 0⟩⟩,
      fun _ _ => ()⟩⟩
  system := kreuzSystem
  startdaten := fun _ => ⟨fun _ => (), fun _ => .ruht,
    fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 0⟩⟩
  startmedium := fun _ _ => 0
  laden := fun _ _ => none

/-- The cross-waiting state: free memory, no traffic, locks held cross-wise. -/
def kreuzZustand : Zustand Bool Unit Unit Unit Unit Unit :=
  { (Zustand.start (L := Bool) (Ort := Unit) (Wert := Unit) (Raum := Unit) (Lok := Unit)
      (Grund := Unit) (fun _ => ()) (fun _ => .ruht)
      (fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩)
      ⟨fun _ => true, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))) with
    sperren := kreuzSperren }

/-- **The closed waiting set exists**: both contexts wait on the lock the other holds. -/
theorem geschlossen_erfuellbar :
    ∃ (E : Einheit Bool Unit Unit Unit Unit Unit Unit Unit Unit)
      (s : Zustand Bool Unit Unit Unit Unit Unit) (C : Kontext → Prop),
      GeschlossenWartend E s C := by
  refine ⟨kreuzEinheit, kreuzZustand, fun c => c = .faden 0 ∨ c = .faden 1, ?_, ?_⟩
  · exact ⟨.faden 0, Or.inl rfl⟩
  · intro c hc
    cases hc with
    | inl h =>
      subst h
      refine ⟨.sperre false, True.intro, True.intro, ?_, ?_⟩
      · intro l hl
        cases hl
        exact ⟨.faden 1, Or.inr rfl, rfl⟩
      · intro k hk
        cases hk
    | inr h =>
      subst h
      refine ⟨.sperre true, True.intro, True.intro, ?_, ?_⟩
      · intro l hl
        cases hl
        exact ⟨.faden 0, Or.inl rfl, rfl⟩
      · intro k hk
        cases hk

/-- A question whose handle records an earlier generation (gen 1) than the commit snapshot. -/
def staleFrage : Frage where
  endpoint := .hosted
  handle := ⟨0, ⟨⟨.hosted, 0⟩, 1⟩, [.read]⟩
  other := []
  operation := .read

/-- On the empty outside snapshot no question is valid at commit: every access fails the
    same-event check and no row stability covers the object. -/
theorem stale_nicht_gueltig (p : Plattform) :
    ¬ Aussen.GueltigBeiCommit p AussenSicht.leer staleFrage := by
  apply fruehere_provenienz_verweigert p _ _
    ⟨staleFrage.handle, staleFrage.operation.required⟩ List.mem_cons_self
    staleFrage.handle.origin rfl ?_ (Aussen.reihe_instabil _ _)
  show staleFrage.handle.origin ≠ _
  intro hcon
  exact nomatch hcon

/-- A rule that always fires: it emits the stale question in every state. -/
def staleRegel
    : Regel (Zustand Unit Unit Unit Unit Unit Unit) (SchrittPlan Unit Unit Unit Unit) Unit :=
  ⟨fun _ _ _ _ => True, fun _ _ _ _ _ => True⟩

/-- A system with one always-firing form at every head. -/
def staleSystem : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => staleRegel, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

/-- The stale-emitting unit on the approved x86-64 rows. -/
def staleEinheit : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  katalog := Plattform.x86_64.katalog
  bild := ⟨Bildformat.elf, fun _ => none, []⟩
  einrichtung := ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (),
    fun _ _ _ => False, fun _ _ => True, ⟨0, 0⟩,
    ⟨.faden 0, 0,
      fun _ => ⟨fun _ => (), fun _ => .ruht,
        fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
        ⟨fun _ => true, fun _ => 0⟩⟩,
      fun _ _ => ()⟩⟩
  system := staleSystem
  startdaten := fun _ => ⟨fun _ => (), fun _ => .ruht,
    fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 0⟩⟩
  startmedium := fun _ _ => 0
  laden := fun _ _ => none

/-- **A system that emits a question with a stale handle does NOT satisfy the outside rule**:
    the composed implementation step emits the stale question while the commit snapshot moved
    on, so validity at commit fails. -/
theorem stale_nicht_aussen_gueltig : ¬ AussenGueltig staleEinheit := by
  intro h
  let c : Kontext := .faden 0
  let s : Zustand Unit Unit Unit Unit Unit Unit :=
    Zustand.start (fun _ => ()) (fun _ => .laeuft)
      (fun _ => ⟨some (.faden 0), .nutzer, (), fun _ => true, 0, false, []⟩)
      ⟨fun _ => true, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))
  let run : HwLauf :=
    ⟨fun _ => ⟨some 0, fun _ => false, [], fun _ => false, false, false, 0⟩,
      ⟨fun _ _ => AussenSicht.leer, fun _ _ _ => .warten, fun _ _ _ _ => none⟩⟩
  let plan : SchrittPlan Unit Unit Unit Unit :=
    ⟨.frage staleFrage, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩
  let ev := s.stelleFrage 0 c staleFrage
  obtain ⟨g₁, hstep⟩ := Speicher.Zustand.schritt_ohne_lesen
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig (SpeicherAkteur.kontext c)
    (aussenEtikett staleEinheit.einrichtung (.frage ev)) (fun h => h)
  let spur : SchrittSpur Unit Unit :=
    ⟨[((SpeicherAkteur.kontext c), aussenEtikett staleEinheit.einrichtung (.frage ev))], [.frage ev]⟩
  let s' : Zustand Unit Unit Unit Unit Unit Unit := { s.frage ev with graph := g₁ }
  have hmem : Speicherfolge s.initial (SpeicherAkteur.kontext c) s.graph
      [aussenEtikett staleEinheit.einrichtung (.frage ev)] spur.speicher s'.graph :=
    .cons (.ohne (Or.inl rfl)) hstep (.nil _)
  have hrahmen : Zustandsrahmen s s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hlesen : ∀ l ∈ plan.lesen, l.art.liest := fun _ h => absurd h List.not_mem_nil
  have hfrage : FuehrtAus staleEinheit.einrichtung 0 c s s plan.aktion [] [.frage ev] (s.frage ev) :=
    FuehrtAus.frage staleFrage
  have haus : FuehrtSchrittAus staleEinheit.einrichtung 0 c s s plan spur s' :=
    ⟨hrahmen, hlesen, [], _, hfrage, hmem, rfl⟩
  have hregel : staleSystem.ImplSchritt c s [plan] s :=
    ⟨(), rfl, trivial⟩
  have hbereit : KannSchreiten run 0 c s := ⟨0, rfl, rfl, rfl⟩
  have hschritt : ImplSchritt staleEinheit.einrichtung staleSystem staleEinheit.katalog
      run 0 s spur s' :=
    .kontext rfl hbereit hregel haus
  have hfrage_mem : Ereignis.frage ev ∈ spur.aussen := List.mem_cons_self
  exact stale_nicht_gueltig _ (h.1 run 0 s spur s' hschritt ev hfrage_mem)

/-- A plan that writes a location. -/
def unbefugtPlan : SchrittPlan Unit Unit Unit Unit :=
  ⟨.intern, [], [()], fun _ => false, fun _ => .na, fun _ => ()⟩

/-- A state with entirely dead authority: nothing lives anywhere. -/
def toteRechte : Rechte := ⟨fun _ => false, fun _ => 0⟩

/-- **A step touching an unowned location is not `RegelLokal`**: the always-firing rule takes
    a footprint step in a state with dead authority, so no live handle covers it. -/
theorem unbefugt_nicht_regel_lokal : ¬ RegelLokal staleEinheit () := by
  intro h
  let s : Zustand Unit Unit Unit Unit Unit Unit :=
    Zustand.start (fun _ => ()) (fun _ => .laeuft)
      (fun _ => ⟨some (.faden 0), .nutzer, (), fun _ => true, 0, false, []⟩)
      toteRechte (fun _ => ()) (.leer (fun _ => 0))
  have hI := h.1 (.faden 0) s s unbefugtPlan trivial
  exact befugt_verweigert _ s (.faden 0) unbefugtPlan (fun _ => rfl) (Or.inl (by decide)) hI

end Gabbro.Core.Annahme
