/-
  File:      core/Core/Fortschritt/AntwortBeiGelegenheit.lean
  Subject:   A COUNTEREXAMPLE to the general "a ready core context must step at its
             opportunity" claim, and the precise status of scheduler fairness.

  Under the unchanged rules `AngebotGueltig` reserves an interrupt-delivery tick but
  does not couple a core opportunity to the absence of a delivery: a conformant
  history may offer both at one and the same cut. The elaborated answer-elimination
  step of `einheitVon_schreitet_bei_gelegenheit` uses `einheitVon_keine_fragen`, a
  fact of raw elaborated units only; a raw unit with a genuine open hosted question
  admits a maximal run that consumes the answer at the very cut at which a live,
  dispatched and rule-enabled core context is ready. This module exhibits that cut
  using the hosted arrival proof. It then states exactly what remains for scheduler
  fairness: a finite number of competing answers still yields infinitely many core
  steps, while an unbounded number is the counter-run obligation.
-/
module

public import Core.Annahme.HostedLauf
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core
open Gabbro.Core.Katalog
open Gabbro.Core.Maschine
open Gabbro.Core.Annahme
open Gabbro.Core.Annahme.Hosted

/-- The hosted state at the answer cut with the issuing context kept running. -/
def fragendLebendig (s : AussenStart) (g : SpeicherGraph Unit Unit) : Zustand :=
  { (binde (startZustand s)).frage (gestellt s) with graph := g }

/-- The raw competing unit: hosted rules plus an always-enabled internal spin at a
    state that has not consumed an answer yet. No source binding is claimed. -/
def wettbewerbRegel (c : Kontext) (s : Zustand) (_ : Unit)
    (plans : List Plan) (u : Zustand) : Prop :=
  c = kontext ∧
    ((plans = [bindePlan] ∧ s.lokal c = some griff ∧ u = binde s) ∨
     (plans = [fragePlan] ∧ AussengriffeEigen s c frage ∧ u = s) ∨
     (plans = [bindePlan] ∧ u = s))

def wettbewerbKopf (s : Zustand) (_c : Kontext) : Option Unit :=
  if s.antworten.length = 0 then some () else none

def wettbewerbEinheit : Modell where
  katalog := einheit.katalog
  bild := einheit.bild
  einrichtung := einrichtung
  system := ⟨fun _ => ⟨wettbewerbRegel, wettbewerbRegel⟩, wettbewerbKopf,
    fun s _ => s.antworten.length ≠ 0, fun _ _ _ => False⟩
  startdaten := startDaten
  startmedium := fun _ _ => 0
  laden := fun s _ => some (startZustand s)
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := .leer
  domaenen := hostedTabelle
  etiketten := einheit.etiketten
  fluss := einheit.fluss

/-- The competing unit uses the same start contract as the hosted unit. -/
theorem wettbewerb_zul {s : AussenStart} (zul : einheit.ZulStart (umgebung []) s) :
    wettbewerbEinheit.ZulStart (umgebung []) s := by
  exact zul

/-- The issuing context keeps running at the answer cut, so the core is ready. -/
theorem wettbewerb_bereit (s : AussenStart) (g : SpeicherGraph Unit Unit) (bytes : List UInt8) :
    KannSchreiten (hardware bytes) 2 kontext (fragendLebendig s g) := by
  refine ⟨0, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

/-- A complete rule step and its machine execution exist at the answer cut. -/
theorem wettbewerb_kernschritt (s : AussenStart) (g : SpeicherGraph Unit Unit) :
    wettbewerbEinheit.system.ImplSchritt kontext (fragendLebendig s g) () [bindePlan]
      (fragendLebendig s g) ∧
    FuehrtSchrittAus einrichtung 2 kontext (fragendLebendig s g) (fragendLebendig s g)
      bindePlan ⟨[], []⟩ (fragendLebendig s g) := by
  constructor
  · refine ⟨(), ?_, ?_⟩
    · change wettbewerbKopf (fragendLebendig s g) kontext = some ()
      have hant : (fragendLebendig s g).antworten = [] := by rfl
      unfold wettbewerbKopf
      rw [hant]
      simp only [List.length_nil, if_pos rfl]
    · change wettbewerbRegel kontext (fragendLebendig s g) () [bindePlan] (fragendLebendig s g)
      exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · have rahmen : Zustandsrahmen (fragendLebendig s g) (fragendLebendig s g) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨rahmen, ?_, [], fragendLebendig s g, ?_, ?_, ?_⟩
    · intro l mem
      exact (List.not_mem_nil mem).elim
    · exact FuehrtAus.intern
    · exact .nil _
    · rfl

/-- The state after the competing answer has been consumed. -/
def fertigLebendig (s : AussenStart) (bytes : List UInt8)
    (g g' : SpeicherGraph Unit Unit) : Zustand :=
  { (fragendLebendig s g).antwort (angekommen s bytes) with graph := g' }

/-- The open answer is admissible at the live cut: the hardware offers its endpoint, the
    policy commits, and the issued question is still unanswered. -/
theorem wettbewerb_antwort_angeboten (s : AussenStart) (bytes : List UInt8)
    (g : SpeicherGraph Unit Unit) :
    (fragendLebendig s g).AntwortAngeboten wettbewerbEinheit.katalog (hardware bytes) 2
      (angekommen s bytes) := by
  refine ⟨rfl, ⟨decide_eq_true ausgewaehlt, ?_⟩, ausgewaehlt,
    ⟨gestellt s, List.mem_cons_self, Nat.zero_le _, Nat.le_succ _, rfl, rfl, rfl⟩,
    fun _ mem => (List.not_mem_nil mem).elim⟩
  exact antwort_atomar (fragendLebendig s g).verlauf bytes

/-- Issuing the question keeps the context running: no `warte` on the way. -/
private theorem frage_aus_live (s : AussenStart) :
    ∃ g, FuehrtSchrittAus einrichtung 1 kontext (binde (startZustand s)) (binde (startZustand s))
      fragePlan (frageSpur s) (fragendLebendig s g) := by
  obtain ⟨g, step⟩ := Speicher.Zustand.schritt_ohne_lesen
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
    (SpeicherAkteur.kontext kontext)
    (aussenEtikett einrichtung (.frage (gestellt s))) id
  refine ⟨g, ?_⟩
  refine ⟨?_, ?_, [], (binde (startZustand s)).frage (gestellt s), ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l mem
    exact (List.not_mem_nil mem).elim
  · exact FuehrtAus.frage frage
  · exact .cons (.ohne (Or.inl rfl)) step (.nil _)

private theorem antwort_aus_live (s : AussenStart) (bytes : List UInt8)
    (g : SpeicherGraph Unit Unit) (gut : g.graph.Konsistent ∧ g.graph.Vollstaendig) :
    ∃ g', AntwortSchritt einrichtung wettbewerbEinheit.katalog (hardware bytes) 2
      (angekommen s bytes) (fragendLebendig s g) (antwortSpur s bytes)
      (fertigLebendig s bytes g g') := by
  obtain ⟨g', step⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2
    (SpeicherAkteur.aussen : SpeicherAkteur Unit)
    (aussenEtikett einrichtung (.antwort (angekommen s bytes))) id
  exact ⟨g', wettbewerb_antwort_angeboten s bytes g, rfl,
    .cons (.ohne (Or.inl rfl)) step (.nil _), rfl⟩

private theorem kein_kontext_fertig (s : AussenStart) (bytes : List UInt8)
    (g g' : SpeicherGraph Unit Unit)
    {c w plans u} (step : wettbewerbEinheit.system.ImplSchritt c
      (fertigLebendig s bytes g g') w plans u) : False := by
  obtain ⟨_, head, _⟩ := step
  change wettbewerbKopf (fertigLebendig s bytes g g') c = some _ at head
  unfold wettbewerbKopf at head
  split at head
  · rename_i eq
    have hlen : (fertigLebendig s bytes g g').antworten.length = 1 := by rfl
    rw [hlen] at eq
    cases eq
  · cases head

private theorem kein_antwort_fertig (s : AussenStart) (bytes : List UInt8)
    (g g' : SpeicherGraph Unit Unit) {t a spur nach}
    (step : AntwortSchritt einrichtung wettbewerbEinheit.katalog (hardware bytes) t a
      (fertigLebendig s bytes g g') spur nach) : False := by
  obtain ⟨ev, mem, _, _, _, instanz, _⟩ := step.1.2.2.2.1
  cases List.mem_singleton.mp mem
  exact step.1.2.2.2.2 (angekommen s bytes) List.mem_cons_self instanz

private theorem kein_interrupt_fertig {s : AussenStart} {bytes : List UInt8}
    {g g' : SpeicherGraph Unit Unit} {t id spur nach}
    (step : UnterbrechungsSchritt einrichtung (hardware bytes) t id
      (fertigLebendig s bytes g g') spur nach) : False := by
  obtain ⟨_, _, _, _, _, angeboten, _⟩ := step
  have eq := angeboten.2.2.1
  change ([] : List InterruptSignal)[id.2]? = some _ at eq
  rw [List.getElem?_nil] at eq
  cases eq

private theorem kein_absturz_fertig {s : AussenStart} {bytes : List UInt8}
    {g g' : SpeicherGraph Unit Unit} {t spur nach}
    (step : AbsturzSchritt einrichtung.persistenzRegion einrichtung.wiederanlauf
      wettbewerbEinheit.katalog (hardware bytes) t
      (fertigLebendig s bytes g g') spur nach) : False := by
  have eq := step.1.2
  cases eq

/-- After the answer the head is gone and no other transition remains. -/
private theorem fertigLebendig_still (s : AussenStart) (bytes : List UInt8)
    (g g' : SpeicherGraph Unit Unit) (t : Nat) :
    KeinSchritt (Lauffolge wettbewerbEinheit (hardware bytes)) t
      (fertigLebendig s bytes g g') := by
  intro _ _ step
  cases step with
  | schritt trans =>
    cases trans with
    | kontext _ _ regel _ => exact kein_kontext_fertig s bytes g g' regel
    | antwort _ reply => exact kein_antwort_fertig s bytes g g' reply
    | interrupt _ enters => exact kein_interrupt_fertig enters
    | absturz crash => exact kein_absturz_fertig crash

/-- THE WITNESS. Under the unchanged rules an admitted maximal run of a raw unit
    consumes a valid open answer at the very cut at which a dispatched, live and
    rule-enabled core context is ready. The conformant history offers both a core
    and the delivery at that cut, selects no interrupt and offers no crash. -/
theorem antwort_bei_bereitem_kern
    (s : AussenStart) (zul : einheit.ZulStart (umgebung []) s) (bytes : List UInt8) :
    ∃ (ρ : Lauf wettbewerbEinheit) (g : SpeicherGraph Unit Unit),
      Laeufe wettbewerbEinheit (umgebung bytes) ρ ∧
      ρ.start = s ∧ ρ.hw = hardware bytes ∧
      ρ.zeit.zustand 0 = some (startZustand s) ∧
      ρ.zeit.zustand 1 = some (binde (startZustand s)) ∧
      ρ.zeit.zustand 2 = some (fragendLebendig s g) ∧
      ρ.zeit.spur 0 = some (.kontext kontext (), ⟨[], []⟩) ∧
      ρ.zeit.spur 1 = some (.kontext kontext (), frageSpur s) ∧
      ρ.zeit.spur 2 = some (.antwort (angekommen s bytes), antwortSpur s bytes) ∧
      KannSchreiten ρ.hw 2 kontext (fragendLebendig s g) ∧
      (ρ.hw.angebot 2).core = some 0 ∧
      (ρ.hw.angebot 2).delivery frage.endpoint = true ∧
      (ρ.hw.angebot 2).crash = false ∧
      ((hardware bytes).angebot 2).interruptAuswahl = none := by
  obtain ⟨g, frageAus⟩ := frage_aus_live s
  have gut := (frageAus.viele einrichtung).gut
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
  obtain ⟨g', reply⟩ := antwort_aus_live s bytes g gut
  have bindeRahmen : Zustandsrahmen (startZustand s) (binde (startZustand s)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have bindeAus : FuehrtSchrittAus einrichtung 0 kontext (startZustand s)
      (binde (startZustand s)) bindePlan ⟨[], []⟩ (binde (startZustand s)) :=
    ⟨bindeRahmen, fun _ mem => (List.not_mem_nil mem).elim, [], _, FuehrtAus.intern, .nil _, rfl⟩
  have bindeRegel : wettbewerbEinheit.system.ImplSchritt kontext (startZustand s) ()
      [bindePlan] (binde (startZustand s)) := by
    refine ⟨(), ?_, ?_⟩
    · change wettbewerbKopf (startZustand s) kontext = some ()
      unfold wettbewerbKopf
      have h : (startZustand s).antworten.length = 0 := by rfl
      rw [h]
      simp only [List.length_nil, if_pos rfl]
    · change wettbewerbRegel kontext (startZustand s) () [bindePlan] (binde (startZustand s))
      refine ⟨rfl, Or.inl ?_⟩
      refine ⟨rfl, ?_, rfl⟩
      change s.outside.channels .hosted 0 = some griff
      rw [zul.2.2.2.2.2.2.2]
      rfl
  have frageRegel : wettbewerbEinheit.system.ImplSchritt kontext (binde (startZustand s)) ()
      [fragePlan] (binde (startZustand s)) := by
    refine ⟨(), ?_, ?_⟩
    · change wettbewerbKopf (binde (startZustand s)) kontext = some ()
      unfold wettbewerbKopf
      have h : (binde (startZustand s)).antworten.length = 0 := by rfl
      rw [h]
      simp only [List.length_nil, if_pos rfl]
    · change wettbewerbRegel kontext (binde (startZustand s)) () [fragePlan] (binde (startZustand s))
      exact ⟨rfl, Or.inr (Or.inl ⟨rfl, eigene_frage (startZustand s), rfl⟩)⟩
  have frageAus' : FuehrtSchrittAus wettbewerbEinheit.einrichtung 1 kontext
      (binde (startZustand s)) (binde (startZustand s)) fragePlan (frageSpur s)
      (fragendLebendig s g) := frageAus
  let h₀ : Lauffolge wettbewerbEinheit (hardware bytes) 0 (some (startZustand s))
      (.kontext kontext (), ⟨[], []⟩) (some (binde (startZustand s))) :=
    .schritt (.kontext rfl ⟨0, rfl, rfl, rfl⟩ bindeRegel bindeAus)
  let h₁ : Lauffolge wettbewerbEinheit (hardware bytes) 1 (some (binde (startZustand s)))
      (.kontext kontext (), frageSpur s) (some (fragendLebendig s g)) :=
    .schritt (.kontext rfl ⟨0, rfl, rfl, rfl⟩ frageRegel frageAus')
  let h₂ : Lauffolge wettbewerbEinheit (hardware bytes) 2 (some (fragendLebendig s g))
      (.antwort (angekommen s bytes), antwortSpur s bytes) (some (fertigLebendig s bytes g g')) :=
    .schritt (.antwort rfl reply)
  let ρ : Lauf wettbewerbEinheit :=
    ⟨s, hardware bytes, dreiTakte h₀ h₁ h₂ (fun t => fertigLebendig_still s bytes g g' (t + 3))⟩
  refine ⟨ρ, g, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨erlaubt bytes, konform bytes, wettbewerb_zul zul, rfl⟩
  · exact wettbewerb_bereit s g bytes
  · rfl
  · exact decide_eq_true ausgewaehlt
  · rfl
  · rfl

/- Scheduler fairness in the general case. The answer elimination of
   `einheitVon_schreitet_bei_gelegenheit` is a fact of raw elaborated units only;
   for a unit that can answer an open question, the same opportunity can be taken
   by an answer. The conclusion nevertheless holds as soon as the competing
   answers are finite: pick an opportunity past the last answer, and at that cut
   no crash, no interrupt and no answer can consume the single core, so the ready
   context must step. What remains when answers are unbounded is precisely a
   counter-run whose ready context is preempted by an answer at every opportunity. -/

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}
variable [DecidableEq L]
variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)

theorem schedulerFair_bei_endlichen_antworten {H : Umgebung} {ρ : Lauf E}
    (lauf : Laeufe E H ρ) (a : Nat) (c : Kontext)
    (ready : ∀ t, a ≤ t → ∃ s, ρ.zeit.zustand t = some s ∧
      (∃ k, (s.kerne k).laeuft = some c) ∧ s.status c = .laeuft ∧
      (ρ.hw.angebot t).crash = false ∧
      ∃ w plan u spur s', E.system.ImplSchritt c s w [plan] u ∧
        FuehrtSchrittAus E.einrichtung t c s u plan spur s')
    (opps : ∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ.hw.gelegenheit t k ∧
      ∃ s, ρ.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some c)
    (endlich : ∃ N, ∀ t a_ev spur, N ≤ t →
      ρ.zeit.spur t ≠ some (.antwort a_ev, spur)) :
    ∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ w spur, ρ.zeit.spur t = some (.kontext c w, spur) := by
  obtain ⟨N, hN⟩ := endlich
  intro n hn
  let m := max n N
  have hma : a ≤ m := le_trans hn (le_max_left n N)
  obtain ⟨t, htm, k, geleg, s, hs, disp⟩ := opps m hma
  have htn : n ≤ t := le_trans (le_max_left n N) htm
  have htN : N ≤ t := le_trans (le_max_right n N) htm
  obtain ⟨s', hs', _, live, noCrash, w, plan, u, spur, snext, regel, aus⟩ :=
    ready t (le_trans hma htm)
  have ss' : s = s' := Option.some.inj (hs.symm.trans hs')
  subst s'
  have stepExists : ∃ ev next, Lauffolge E ρ.hw t (ρ.zeit.zustand t) ev next := by
    rw [hs]
    refine ⟨(.kontext c w, spur), some snext, ?_⟩
    exact .schritt (.kontext noCrash ⟨k, geleg, disp, live⟩ regel aus)
  have tick := ρ.zeit.takt t
  cases tick with
  | wartet label eq pause =>
    obtain ⟨ev, next, hstep⟩ := stepExists
    exact (pause ev next hstep).elim
  | schritt label step =>
    rw [hs] at step
    generalize hnext : ρ.zeit.zustand (t + 1) = nextAt at step
    cases nextAt with
    | none => cases step
    | some next =>
      have hex : ∃ (wahl : SchrittWahl Wahl) (spur : SchrittSpur Ort Wert),
          ρ.zeit.spur t = some (wahl, spur) := by
        obtain ⟨ev, evEq'⟩ : ∃ ev, ρ.zeit.spur t = some ev := ⟨_, label⟩
        rcases ev with ⟨w, sp⟩
        exact ⟨w, sp, evEq'⟩
      obtain ⟨wahl, spurEv, evEq⟩ := hex
      have hstep' : ImplSchritt E.einrichtung E.system E.katalog ρ.hw t s
          (wahl, spurEv) next := by
        cases step with
        | schritt h =>
          have conj := label.symm.trans evEq
          cases conj
          exact h
      cases wahl with
      | kontext c' w' =>
        cases hstep' with
        | kontext _ bereit' _ _ =>
          obtain ⟨k', geleg', disp', _⟩ := bereit'
          have kk' : k = k' := Option.some.inj (geleg.symm.trans geleg')
          have disp'' : (s.kerne k).laeuft = some c' := kk'.symm ▸ disp'
          have cc' : c = c' := Option.some.inj (disp.symm.trans disp'')
          subst c'
          exact ⟨t, htn, w', spurEv, evEq⟩
      | antwort a_ev =>
        exact (hN t a_ev spurEv htN evEq).elim
      | interrupt id =>
        cases hstep' with
        | interrupt _ enters =>
          obtain ⟨_, _, _, _, _, pending, _⟩ := enters
          have reserved := (lauf.2.1.2 t).interrupt_reserviert pending.2.2.2.2
          have impossible : none = some k := reserved.2.1.symm.trans geleg
          cases impossible
      | absturz =>
        cases hstep' with
        | absturz crash =>
          have hc := crash.1.2
          rw [noCrash] at hc
          cases hc

/-- The general form of the elaborated opportunity lemma: at a crash-free core
    opportunity a dispatched, live and rule-enabled context must step. -/
def SchreitetBeiGelegenheit (ρ : Lauf E) : Prop :=
  ∀ {H : Umgebung}, Laeufe E H ρ →
    ∀ {tick : Nat} {s : Zustand L Ort Wert Raum Lok Grund} {c : Kontext},
      ρ.zeit.zustand tick = some s → (ρ.hw.angebot tick).crash = false →
      KannSchreiten ρ.hw tick c s →
      ∀ {w : Wahl} {plan : SchrittPlan L Ort Wert Bedingung}
        {u : Zustand L Ort Wert Raum Lok Grund} {spur : SchrittSpur Ort Wert}
        {s' : Zustand L Ort Wert Raum Lok Grund},
        E.system.ImplSchritt c s w [plan] u →
        FuehrtSchrittAus E.einrichtung tick c s u plan spur s' →
        ∃ w spur, ρ.zeit.spur tick = some (.kontext c w, spur)

/-- The general form is false: the admitted witness consumes the answer at the very
    cut where the core context is ready. What the elaborated proof excludes through
    `einheitVon_keine_fragen` is therefore not a general machine fact. -/
theorem nicht_schreitet_bei_gelegenheit
    (s : AussenStart) (zul : einheit.ZulStart (umgebung []) s) (bytes : List UInt8) :
    ∃ ρ : Lauf wettbewerbEinheit, Laeufe wettbewerbEinheit (umgebung bytes) ρ ∧
      ¬ SchreitetBeiGelegenheit wettbewerbEinheit ρ := by
  obtain ⟨ρ, g, run, _, _, _, _, cut, _, _, answer, bereit, _, _, crash, _⟩ :=
    antwort_bei_bereitem_kern s zul bytes
  refine ⟨ρ, run, ?_⟩
  intro allg
  obtain ⟨regel, aus⟩ := wettbewerb_kernschritt s g
  obtain ⟨w, spur, step⟩ := allg run cut crash bereit regel aus
  have eq := answer.symm.trans step
  have wahlEq : (.antwort (angekommen s bytes) : SchrittWahl Unit) = .kontext kontext w :=
    congrArg Prod.fst (Option.some.inj eq)
  cases wahlEq

/-- The remaining counter-run obligation when the competing answers are unbounded:
    a context that is continuously dispatched, live and rule-enabled on a suffix,
    with a crash-free core opportunity at infinitely many cuts, while every one of
    those cuts is consumed by an open answer and the context never steps. The
    witness above supplies the one-tick pump; what remains is to iterate it along
    an unbounded question stream. -/
def GegenlaufPflicht (ρ : Lauf E) (a : Nat) (c : Kontext) : Prop :=
  (∀ t, a ≤ t → ∃ s, ρ.zeit.zustand t = some s ∧
    (∃ k, (s.kerne k).laeuft = some c) ∧ s.status c = .laeuft ∧
    (ρ.hw.angebot t).crash = false ∧
    ∃ w plan u spur s', E.system.ImplSchritt c s w [plan] u ∧
      FuehrtSchrittAus E.einrichtung t c s u plan spur s') ∧
  (∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ.hw.gelegenheit t k ∧
    ∃ s, ρ.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some c ∧
      ∃ a_ev spur, ρ.zeit.spur t = some (.antwort a_ev, spur)) ∧
  (∀ t (w : Wahl) spur, a ≤ t →
    ρ.zeit.spur t ≠ some (.kontext c w, spur))

end Gabbro.Core.Fortschritt
