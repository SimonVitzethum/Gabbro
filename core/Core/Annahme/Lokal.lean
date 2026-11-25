/-
  File:      core/Core/Annahme/Lokal.lean
  Subject:   The local part of acceptance (PERFECT-MODEL §3.2, §4, step M5).

  `Lokal E` is the decidable local rules over the program's syntax interface, generic over the
  program's units and forms: the per-form authority obligation (`RegelLokal`, discharged per
  form), the per-form stack and memory obligation (`SchrankenLokal`, discharged per form;
  open bounds stay admitted), the wait-free lock sections (`AbschnittWartefrei`: no waiting
  on a not-yet-enabled condition while holding a bound lock) and the outside rule of §4
  (`AussenLokal` with `AussenGueltig`:
  every outside effect valid at commit), over the catalogue selection (`KatalogWohlgeformt`).
  `stale_griff_ungueltig`
  and the refusal theorems connect M10's outside provenance to validity at commit: a handle
  that records only an earlier answer's generation never establishes validity once the commit
  snapshot moved on. The domain isolation row (`DomaenenLokal`, MK-17): every form that can
  stand at a head meets the per-form duty `RegelIsolation` under every domain plan.
-/
module

public import Core.Maschine.Start
public import Core.Maschine.Ergebnis
public import Core.Aussen.Bindung
public import Core.Aussen.Zulassung
public import Core.Annahme.Schranken
public import Core.Beobachtung.Fluss.Quellregel

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Sicherheit (Speicherrecht)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- The context's bound handle is valid, its allocation contains the location at an offset,
    and the context holds the requested right while the allocation is owned. -/
def BefugtOrt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (x : Ort) (recht : Speicherrecht) : Prop :=
  ∃ (g : Griff) (offset : Nat),
    E.einrichtung.speicherGriff s c x = some g ∧ g.objekt = E.einrichtung.speicherObjekt x ∧
    s.rechte.Gueltig g ∧ (s.leihen g.objekt).Zugriff ∧
    (s.buchung.umfang g.objekt)[offset]? = some x ∧ s.buchung.haelt c g recht

/-- **Authority footprint of one composed plan step**: the acting context needs read
    authority for each recorded read, write authority for each read-modify-write and
    write authority throughout the declared write footprint. -/
def Befugt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (plan : SchrittPlan L Ort Wert Bedingung) : Prop :=
  (∀ x ∈ plan.fuss, BefugtOrt E s c x .schreiben) ∧
  (∀ l ∈ plan.lesen, BefugtOrt E s c l.ort .lesen ∧
    (l.art.schreibt → BefugtOrt E s c l.ort .schreiben))

/-- **Obligation of a form: its decidable local rules hold.** Every ideal step of the form
    covers its memory footprint by live authority at the pre-state. Form-specific typing
    is M6's additional field. -/
def RegelLokal (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (i : ι) : Prop :=
  ∀ (c : Kontext) (s u : Zustand L Ort Wert Raum Lok Grund) (w : Wahl)
    (plan : SchrittPlan L Ort Wert Bedingung),
    (E.system.regel i).ideal c s w [plan] u → Befugt E s c plan

/-- Ownership and the requested rights in the program's own authority state. -/
def AussengriffeEigen (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (q : Frage) : Prop :=
  ∀ z ∈ q.zugriffe, s.buchung.aussengriff c z.handle z.right

/-- Outside rules checked on the ideal context step. A question needs program-side rights
    at issue. An unmediated commit has no catalogue reply that can revalidate it or fail,
    so it needs pinned stability and its operation must succeed under the admitted rely. -/
def AussenKontextLokal [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (c : Kontext)
    (run : HwLauf) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  (∀ ev : FrageEreignis, Ereignis.frage ev ∈ spur.aussen →
    E.katalog.enthaelt (.endpoint ev.question.endpoint) ∧ AussengriffeEigen s c ev.question) ∧
  ∃ neu, s'.buchung.wirkungen = s.buchung.wirkungen ++ neu ∧
    ∀ effect, Sicherheit.Wirkung.aussen effect ∈ neu →
      effect.kontext = c ∧ AussengriffeEigen s c effect.frage ∧
      E.katalog.enthaelt (.endpoint effect.frage.endpoint) ∧
      (∀ z ∈ effect.frage.zugriffe, Aussen.ReihenStabil E.katalog.plattform z.handle.origin.object) ∧
      ∀ H, Hardware E.katalog H → run.konform E.katalog H →
        ∃ reply, E.katalog.zulaessig (run.politik.sicht t s.verlauf) effect.frage reply ∧
          reply.result.isOk = true

/-- The outside rule at the ideal boundaries. An asynchronous effect is checked in the
    catalogue view of the successful reply, over the history before that reply. The receiving
    context owns the handles at that same cut. Data from an earlier answer may inform the
    choice, while the catalogue establishes current validity. -/
def AussenGueltig [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  (∀ (run : HwLauf) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
    (w : SchrittWahl Wahl) (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund),
    I.Schritt E.einrichtung E.system E.katalog run t s (w, spur) s' →
    match w with
    | .kontext c _ => AussenKontextLokal E c run t s spur s'
    | .antwort a =>
      ∀ H, Hardware E.katalog H → run.konform E.katalog H → a.reply.result.isOk = true →
        Aussen.GueltigBeiCommit E.katalog.plattform (run.politik.sicht t s.verlauf) a.question
    | .interrupt _ | .absturz => True) ∧
  ∀ (η : I.Lauf E), I.Laeufe E η → ∀ t a spur,
    η.zeit.spur t = some (.antwort a, spur) → a.reply.result.isOk = true →
    ∃ c, c.nummer = a.context ∧ AussengriffeEigen (η.zeit.zustand t) c a.question

/-- The reply boundary establishes validity in the commit view for any conformant policy. -/
theorem antwort_gueltig [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι} {run t a s spur s' H}
    (step : AntwortSchritt E.einrichtung E.katalog run t a s spur s')
    (hardware : Hardware E.katalog H) (konform : run.konform E.katalog H)
    (ok : a.reply.result.isOk = true) :
    Aussen.GueltigBeiCommit E.katalog.plattform (run.politik.sicht t s.verlauf) a.question :=
  Aussen.atomar_gueltig (step.1.zulaessig hardware konform).2 ok

/-- **The outside rule of §4 inside `Lokal`**: the selected platform admits only interfaces
    where every query goes through an owned handle with a failure channel (`ZulassungsRegel`),
    and every outside effect of the unit is valid at commit. -/
def AussenLokal [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    Prop :=
  Aussen.ZulassungsRegel E.katalog.plattform ∧ AussenGueltig E

/-- **Wait-free lock sections** (PERFECT-MODEL §3.2, step M5; MK-05 Option A): a context
    that holds a lock under a declared hold bound waits — if its system reports it blocked
    at all — only on an already-enabled lock take: the awaited lock is free and the holder
    stands at the head of its queue. A wait on an `await`, a join, an outside question or a
    hardware delay while holding is refused, as is a wait on a lock that is held or queued
    ahead: the holder keeps no blockade the progress duties cannot discharge
    (`FortschrittsPflichten.eindeutig`: a ready context is never blocked), so a live
    dispatched holder whose rule offers the release step stays eligible until it hands the
    lock off (`SperrHalterBereit`). This is a checker row like `RegelLokal`: no user proof
    is owed — only the reported blockade is discriminated, over decidable state facts. -/
def AbschnittWartefrei [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  ∀ (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (l : L),
    E.schranken.halten l ≠ none → (s.sperren l).besitzer = some c →
    ∀ (b : Blockade L Bedingung), E.system.blockiert s c b →
      match b with
      | .sperre l' => (s.sperren l').besitzer = none ∧ (s.sperren l').schlange[0]? = some c
      | _ => False

/-- A unit that never reports a context blocked meets the section row. -/
theorem abschnittWartefrei_ohne_blockade [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (nie : ∀ (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (b : Blockade L Bedingung),
      ¬ E.system.blockiert s c b) :
    AbschnittWartefrei E := by
  intro s c l _ _ b hb
  exact False.elim (nie s c b hb)

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

/-- One recorded cut respects the domains: every memory access of the acting context
    stays in its domain or uses a channel, and every issued question is asked by the
    context the trace names, in its domain or over a channel. Lazy initial writes and
    environment arrivals are not program accesses. -/
def SpurRespektiert (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (c : Kontext) (spur : SchrittSpur Ort Wert) : Prop :=
  (∀ a l, (a, l) ∈ spur.speicher → a = .kontext c → ¬ FremdeZelle E plan c l.ort) ∧
  (∀ ev : FrageEreignis, Ereignis.frage ev ∈ spur.aussen →
    ∀ d : Kontext, d.nummer = ev.context → ¬ FremdeFrage plan d ev.question)

/-- **The checker-side isolation duty of one form** (the `RegelLokal` pattern, lifted to the
    recorded step as for `Beobachtung.RegelNIPflicht`): every implementation step of the form
    that the machine carries out through `FuehrtSchrittAus` produces a spur the acting context's
    domain respects. The duty is per form, generic over units, and carries no per-program data. -/
def RegelIsolation [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (i : ι) : Prop :=
  ∀ (t : Nat) (c : Kontext) (s u s' : Zustand L Ort Wert Raum Lok Grund)
    (w : Wahl) (p : SchrittPlan L Ort Wert Bedingung) (spur : SchrittSpur Ort Wert),
    (E.system.regel i).impl c s w [p] u →
    FuehrtSchrittAus E.einrichtung t c s u p spur s' →
    SpurRespektiert E plan c spur

/-- **Isolation duty of a unit** (MK-17 checker row): every form that can stand at the head
    of a context meets the per-form duty under every domain plan. The head gate is the
    honest scope: the rule table covers every form of the type, but only heads ever step,
    so only heads owe the duty. -/
def DomaenenLokal [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    Prop :=
  ∀ (plan : DomaenenPlan) (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (i : ι),
    E.system.kopf s c = some i → RegelIsolation E plan i

/-- The empty recorded cut respects every domain plan: no memory access, no question. -/
theorem spurRespektiert_leer [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (c : Kontext) :
    SpurRespektiert E plan c ⟨[], []⟩ := by
  refine ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

/-- A unit that never reports a head meets the isolation row (the
    `abschnittWartefrei_ohne_blockade` pattern). -/
theorem domaenenLokal_ohne_kopf [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (nie : ∀ (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext),
      E.system.kopf s c = none) :
    DomaenenLokal E := by
  intro plan s c i hkopf
  rw [nie s c] at hkopf
  exact nomatch hkopf

/-- **`Lokal E`: the local rules** — catalogue, authority, outside validity, labelled
    flow, stack/memory bounds, wait-free lock sections and domain isolation at source
    initialisation and at each form. The bounds row is third from last, the section row
    second from last and the isolation row last, so units with open bounds are accepted
    exactly as before. The isolation row (MK-17, meaning change) constrains the recorded
    implementation steps: every form that can stand at a head respects every domain plan. -/
def Lokal [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  KatalogWohlgeformt E.katalog ∧ (∀ i, RegelLokal E i) ∧ AussenLokal E ∧
    Beobachtung.FlussLokal E ∧ SchrankenLokal E ∧ AbschnittWartefrei E ∧ DomaenenLokal E

/-- Satisfiability with both rights: a read and a write can use the same owned location. -/
theorem befugt_erfuellbar (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (x : Ort) :
    let o := E.einrichtung.speicherObjekt x
    let g := s.rechte.ausgeben o
    let gebunden := { E with einrichtung := { E.einrichtung with speicherGriff := fun _ _ _ => some g } }
    let lebend := { s with
      rechte := s.rechte.beleben o
      leihen := fun _ => .eigen
      buchung := { s.buchung with umfang := fun _ => [x], haelt := fun d h _ => d = c ∧ h = g } }
    let plan : SchrittPlan L Ort Wert Bedingung :=
      ⟨.intern, [⟨.lesen, x, .na, s.initial x, s.initial x⟩], [x],
        fun _ => true, fun _ => .na, s.initial⟩
    Befugt gebunden lebend c plan := by
  dsimp only
  constructor
  · intro y hy
    cases List.mem_singleton.mp hy
    exact ⟨_, 0, rfl, rfl, s.rechte.ausgeben_gueltig _, trivial, rfl, rfl, rfl⟩
  · intro l hl
    cases List.mem_singleton.mp hl
    exact ⟨⟨_, 0, rfl, rfl, s.rechte.ausgeben_gueltig _, trivial, rfl, rfl, rfl⟩, False.elim⟩

/-- **A step touching memory without live authority is refused**: where every object is dead,
    no handle is valid, so a plan with a nonempty footprint is not covered. -/
theorem befugt_verweigert (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (plan : SchrittPlan L Ort Wert Bedingung)
    (tot : ∀ o, s.rechte.lebt o = false)
    (beruehrt : plan.fuss ≠ [] ∨ plan.lesen ≠ []) :
    ¬ Befugt E s c plan := by
  intro h
  have tot_verweigert (x : Ort) (r : Speicherrecht) : ¬ BefugtOrt E s c x r := by
    rintro ⟨g, _, _, _, hg, _, _, _⟩
    exact Bool.false_ne_true ((tot g.objekt).symm.trans hg.1)
  rcases beruehrt with hf | hl
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil plan.fuss hf
    exact tot_verweigert x _ (h.1 x hx)
  · obtain ⟨l, hm⟩ := List.exists_mem_of_ne_nil plan.lesen hl
    exact tot_verweigert l.ort _ (h.2 l hm).1

/-- Even when the binding returns the same handle, only the acting context's right counts. -/
theorem anderer_kontext_nicht_befugt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c d : Kontext) (x : Ort) (r : Speicherrecht)
    (bindung : E.einrichtung.speicherGriff s c x = E.einrichtung.speicherGriff s d x)
    (fremd : ∀ g, s.buchung.haelt d g r → ¬ s.buchung.haelt c g r)
    (befugt : BefugtOrt E s d x r) :
    ¬ BefugtOrt E s c x r := by
  obtain ⟨g, _, hd, _, _, _, _, rechtD⟩ := befugt
  rintro ⟨g', _, hc, _, _, _, _, rechtC⟩
  have gleich : g' = g := Option.some.inj (hc.symm.trans (bindung.trans hd))
  subst g'
  exact fremd g rechtD rechtC

/-- Even when both locations bind the same live handle, its allocation must contain the
    accessed location. -/
theorem anderer_ort_nicht_befugt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (x y : Ort) (r : Speicherrecht)
    (bindung : E.einrichtung.speicherGriff s c x = E.einrichtung.speicherGriff s c y)
    (ausserhalb : ∀ g, E.einrichtung.speicherGriff s c y = some g → x ∉ s.buchung.umfang g.objekt)
    (befugt : BefugtOrt E s c y r) :
    ¬ BefugtOrt E s c x r := by
  obtain ⟨g, _, hy, _, _, _, _, _⟩ := befugt
  rintro ⟨g', _, hx, _, _, _, ort, _⟩
  have gleich : g' = g := Option.some.inj (hx.symm.trans (bindung.trans hy))
  subst g'
  exact ausserhalb g hy (List.mem_of_getElem? ort)

/-- A handle whose recorded generation is stale at the commit snapshot authorises nothing:
    the same-event validity check fails. -/
theorem stale_griff_ungueltig (s : AussenSicht) (e : Endpunkt) (t : Zugriff)
    (stale : t.handle.origin ≠ s.herkunft t.handle.origin.object) :
    s.gueltig e t = false := by
  have hbeq : (t.handle.origin == s.herkunft t.handle.origin.object) = false :=
    decide_eq_false stale
  simp only [AussenSicht.gueltig, hbeq, Bool.and_false, Bool.false_and]

/-- **An effect whose authorisation rests only on an earlier answer is refused** (§4): the
    handle records the earlier answer's generation, the commit snapshot moved on, and no row
    stability covers the object — so validity at commit fails on both disjuncts. -/
theorem fruehere_provenienz_verweigert (p : Plattform) (s : AussenSicht) (q : Frage)
    (t : Zugriff) (mem : t ∈ q.zugriffe) (frueher : Herkunft)
    (spur : t.handle.origin = frueher)
    (alt : frueher ≠ s.herkunft t.handle.origin.object)
    (ninstabil : ¬ Aussen.ReihenStabil p t.handle.origin.object) :
    ¬ Aussen.GueltigBeiCommit p s q := by
  subst spur
  intro hval
  cases hval with
  | frisch alle =>
    have htrue := (List.all_eq_true.mp alle) t mem
    have hfalse := stale_griff_ungueltig s q.endpoint t alt
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  | stabil fest => exact ninstabil (fest t mem)

/-- **Only earlier-answer provenance never establishes validity at commit**: the value `u`
    derives from the earlier answer `a₀` (M10 `Abgeleitet`, so its label carries that answer's
    origin), the handle the effect uses records that earlier generation, the commit snapshot
    moved on, and no row stability covers the object. -/
theorem fruehere_ableitung_verweigert (p : Plattform) (s : AussenSicht) (q : Frage)
    (t : Zugriff) (mem : t ∈ q.zugriffe) (u : Gabbro.Core.Aussen.Wert Handle)
    (eq : u.inhalt = t.handle) (a₀ : Antwort) (abgel : Aussen.Abgeleitet u a₀)
    (issued : a₀.origin = t.handle.origin)
    (alt : a₀.origin ≠ s.herkunft t.handle.origin.object)
    (ninstabil : ¬ Aussen.ReihenStabil p t.handle.origin.object) :
    ¬ Aussen.GueltigBeiCommit p s q := by
  have _traegt := Aussen.abgeleitet_traegt u a₀ abgel
  have _gleich := eq
  exact fruehere_provenienz_verweigert p s q t mem a₀.origin issued.symm alt ninstabil

end Gabbro.Core.Annahme
