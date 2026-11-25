module

public import Core.Maschine.Zeitlauf
public import Core.Maschine.Quelltabellen
public import Core.Maschine.Messdaten

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- The unit supplies its rules, image declaration, canonical source initialisation,
    implementation loader and refinement data. M6 unit constructors derive the
    local relation from the source forms and supply their checked length bounds.
    Loader failure is represented by an empty implementation state. -/
structure Einheit (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type) where
  katalog : Katalog.Katalog
  bild : Bild
  einrichtung : Einrichtung L Ort Wert Raum Lok Grund Bedingung
  system : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι
  startdaten : AussenStart → Startdaten Wert Raum Lok Grund
  startmedium : AussenStart → Nat → UInt8
  laden : AussenStart → Ladung → Option (Zustand L Ort Wert Raum Lok Grund)
  lokalerBezug : (Kontext → Lok) → (Kontext → Lok) → Prop
  stotterLaenge : ι → Nat
  quelltabellen : Quelltabellen (Zustand L Ort Wert Raum Lok Grund)
  schranken : Beobachtung.Schrankendaten L Lok := .leer
  etiketten : Beobachtung.Etiketten Ort := .leer
  fluss : Beobachtung.Flussdaten ι Lok Ort Wert := .leer

variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)

/-- The catalogue judges starts before either machine initialises, independently of loader success. -/
def Einheit.ZulStart (h : Umgebung) (s : AussenStart) : Prop :=
  Katalog.ZulStart E.katalog h E.bild s

namespace I

/-- Canonical ideal initialisation keeps the entire catalogue start at the initial cut. -/
def start (s : AussenStart) : AussenStart × Zustand L Ort Wert Raum Lok Grund :=
  let d := E.startdaten s
  (s, Zustand.start d.lokal d.status d.kerne d.rechte E.einrichtung.initial
    (.leer (E.startmedium s)))

theorem start_grenze (s : AussenStart) :
    (start E s).1.inputBytes = s.inputBytes ∧ (start E s).1.assignment = s.assignment ∧
      (start E s).1.outside = s.outside :=
  ⟨rfl, rfl, rfl⟩

end I

variable [DecidableEq L]

/-- Implementation failure is terminal. A working state follows the concrete step relation. -/
inductive Lauffolge (hw : HwLauf) (t : Nat) :
    Option (Zustand L Ort Wert Raum Lok Grund) → (SchrittWahl Wahl × SchrittSpur Ort Wert) →
      Option (Zustand L Ort Wert Raum Lok Grund) → Prop where
  | schritt {s s' spur} (h : ImplSchritt E.einrichtung E.system E.katalog hw t s spur s') :
      Lauffolge hw t (some s) spur (some s')

structure Lauf where
  start : AussenStart
  hw : HwLauf
  zeit : Zeitlauf (Lauffolge E hw)

def Schnitt (ρ : Lauf E) : Type := ρ.zeit.Schnitt

/-- Scheduler fairness of an implementation run (PERFECT-MODEL §3.7, step M11): a context that is
    dispatched, live and rule-enabled on a whole suffix — with a crash-free tick and a complete
    protocol step available — and that has opportunities on its dispatch core infinitely often,
    is stepped infinitely often. This is a property of the execution model, not a catalogue row:
    hardware rows speak about cores, deliveries and cycles only and never arbitrate which ready
    context takes a step, while the runtime dispatches its contexts with a generic dispatch proof
    (PERFECT-MODEL §3.4: executing the dispatch is a language obligation). A program therefore
    proves nothing; every admissible platform satisfies it by construction of `Laeufe`. -/
def SchedulerFair (ρ : Lauf E) : Prop :=
  ∀ (a : Nat) (c : Kontext),
    (∀ t, a ≤ t → ∃ s, ρ.zeit.zustand t = some s ∧
      (∃ k, (s.kerne k).laeuft = some c) ∧ s.status c = .laeuft ∧
      (ρ.hw.angebot t).crash = false ∧
      ∃ w plan u spur s', E.system.ImplSchritt c s w [plan] u ∧
        FuehrtSchrittAus E.einrichtung t c s u plan spur s') →
    (∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ.hw.gelegenheit t k ∧
      ∃ s, ρ.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some c) →
    ∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ w spur, ρ.zeit.spur t = some (.kontext c w, spur)

/-- Maximal implementation runs, with the recorded hardware schedule and its total policy.
    Admissibility includes scheduler fairness: every admissible run serves every
    continuously dispatched, live and rule-enabled context infinitely often whenever its
    dispatch core offers opportunities infinitely often. -/
def Laeufe (h : Umgebung) (ρ : Lauf E) : Prop :=
  Hardware E.katalog h ∧ ρ.hw.konform E.katalog h ∧ E.ZulStart h ρ.start ∧
    ρ.zeit.zustand 0 = E.laden ρ.start (h.lade E.bild) ∧ SchedulerFair E ρ

/-- A preferred step serves the context the opportunity core dispatches. -/
def BevorzugtSchritt (hw : HwLauf) (t : Nat) (s : Option (Zustand L Ort Wert Raum Lok Grund))
    (ev : SchrittWahl Wahl × SchrittSpur Ort Wert) : Prop :=
  ∃ c w spur k, ev = (.kontext c w, spur) ∧ hw.gelegenheit t k ∧
    ∃ z, s = some z ∧ (z.kerne k).laeuft = some c

/-- One fair tick: a preferred dispatched-context step if one exists, another possible step
    otherwise, and a pause only when no step exists at all. -/
noncomputable def fairerSchritt (hw : HwLauf) (t : Nat)
    (s : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Option (Zustand L Ort Wert Raum Lok Grund) ×
      Option (SchrittWahl Wahl × SchrittSpur Ort Wert) := by
  classical
  exact if h1 : ∃ ev next, Lauffolge E hw t s ev next ∧ BevorzugtSchritt hw t s ev then
    (Classical.choose (Classical.choose_spec h1), some (Classical.choose h1))
  else if h2 : ∃ ev next, Lauffolge E hw t s ev next then
    (Classical.choose (Classical.choose_spec h2), some (Classical.choose h2))
  else (s, none)

theorem fairerSchritt_takt (hw : HwLauf) (t : Nat)
    (s : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Takt (Lauffolge E hw) (KeinSchritt (Lauffolge E hw)) t s
      (fairerSchritt E hw t s).2 (fairerSchritt E hw t s).1 := by
  unfold fairerSchritt
  classical
  split
  · next h1 =>
    exact .schritt rfl (Classical.choose_spec (Classical.choose_spec h1)).1
  · next h1 =>
    split
    · next h2 =>
      exact .schritt rfl (Classical.choose_spec (Classical.choose_spec h2))
    · next h2 =>
      refine .wartet rfl rfl (fun ev next step => h2 ⟨ev, next, step⟩)

/-- The fair schedule from an initial state: preferred dispatched-context steps everywhere. -/
noncomputable def fairerFolge (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Nat → Option (Zustand L Ort Wert Raum Lok Grund) ×
      Option (SchrittWahl Wahl × SchrittSpur Ort Wert)
  | 0 => (init, none)
  | t + 1 => fairerSchritt E hw t (fairerFolge hw init t).1

noncomputable def fairerZeit (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Zeitlauf (Lauffolge E hw) where
  zustand := fun t => (fairerFolge E hw init t).1
  spur := fun t => (fairerFolge E hw init (t + 1)).2
  takt := fun t => fairerSchritt_takt E hw t (fairerFolge E hw init t).1

theorem fairerZeit_start (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund)) :
    (fairerZeit E hw init).zustand 0 = init := rfl

/-- The fair schedule serves every continuously dispatched, live and rule-enabled context
    infinitely often whenever its dispatch core offers opportunities infinitely often: at such
    a joint tick the preferred branch fires, and the opportunity core dispatches exactly the
    waiting context. -/
theorem fairer_zeit_fair (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund))
    (s : AussenStart) : SchedulerFair E ⟨s, hw, fairerZeit E hw init⟩ := by
  intro a c bereit opp n hn
  obtain ⟨t, ht, k, gelegenheit, z, eq, dispatch⟩ := opp (max n a) (Nat.le_max_right _ _)
  have hz : (fairerZeit E hw init).zustand t = some z := eq
  obtain ⟨z', eq', _, live, normal, w, plan, u, spur, s', regel, aus⟩ :=
    bereit t ((Nat.le_max_right n a).trans ht)
  have same : z' = z := Option.some.inj (eq'.symm.trans hz)
  subst z'
  have schritt : Lauffolge E hw t (some z) (.kontext c w, spur) s' :=
    .schritt (.kontext normal ⟨k, gelegenheit, dispatch, live⟩ regel aus)
  have bevorzugt : BevorzugtSchritt hw t (some z) (.kontext c w, spur) :=
    ⟨c, w, spur, k, rfl, gelegenheit, z, rfl, dispatch⟩
  have wahl : ∃ ev next, Lauffolge E hw t (some z) ev next ∧ BevorzugtSchritt hw t (some z) ev :=
    ⟨_, _, schritt, bevorzugt⟩
  have hstate : (fairerFolge E hw init t).1 = some z := hz
  have spurEq : (fairerZeit E hw init).spur t = some (Classical.choose wahl) := by
    show (fairerSchritt E hw t (fairerFolge E hw init t).1).2 = _
    rw [hstate]
    unfold fairerSchritt
    classical
    rw [dif_pos wahl]
  have spec := Classical.choose_spec (Classical.choose_spec wahl)
  obtain ⟨c', w', spur', k', hev, geleg', z0, hseq, dispatch'⟩ := spec.2
  have kk : k' = k := Option.some.inj (geleg'.symm.trans gelegenheit)
  subst kk
  have z0eq : z0 = z := Option.some.inj hseq.symm
  subst z0
  have gleich : c' = c := Option.some.inj (dispatch'.symm.trans dispatch)
  subst gleich
  exact ⟨t, (Nat.le_max_left n a).trans ht, w', spur', hev ▸ spurEq⟩

theorem lauf_mit_hw {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) (konform : hw.konform E.katalog h) :
    ∃ ρ, Laeufe E h ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  refine ⟨⟨s, hw, fairerZeit E hw (E.laden s (h.lade E.bild))⟩,
    ⟨hardware, konform, start, fairerZeit_start E hw _, fairer_zeit_fair E hw _ s⟩, rfl, rfl⟩

/-- Scheduler fairness for a run that is stuck from some cut on: a context
    whose rule stays available on a suffix with infinitely many opportunities
    on its dispatch core would take a step there, against the stuck cut. -/
theorem SchedulerFair_aus_stillstand_ab (ρ : Lauf E) (N : Nat)
    (still : ∀ t, N ≤ t → ∀ s, ρ.zeit.zustand t = some s →
      KeinSchritt (Lauffolge E ρ.hw) t (some s)) :
    SchedulerFair E ρ := by
  intro a c ready opp n hn
  obtain ⟨t, ht, k, geleg, z, eq, disp⟩ := opp (max n N) (hn.trans (Nat.le_max_left n N))
  have htN : N ≤ t := (Nat.le_max_right n N).trans ht
  have hat : a ≤ t := (hn.trans (Nat.le_max_left n N)).trans ht
  obtain ⟨s, hs, _, _, live, normal, w, plan, u, spur, s', regel, aus⟩ := ready t hat
  have same : s = z := Option.some.inj (hs.symm.trans eq)
  have dispS : (s.kerne k).laeuft = some c := by rw [same]; exact disp
  have kann : KannSchreiten ρ.hw t c s := ⟨k, geleg, dispS, live⟩
  have step : Lauffolge E ρ.hw t (some s) (.kontext c w, spur) (some s') :=
    .schritt (.kontext normal kann regel aus)
  exact (still t htN s hs _ _ step).elim

/-- Shifted scheduler fairness for a fair tail: the same duties as `SchedulerFair`,
    read at shifted hardware ticks. Spliced runs inherit it through `voran`. -/
def ShiftFair (hw : HwLauf) (ab : Nat) (s : AussenStart)
    (tail : Zeitlauf (fun t => Lauffolge E hw (t + ab))) : Prop :=
  ∀ (a : Nat) (c : Kontext),
    (∀ t, a ≤ t → ∃ z, tail.zustand t = some z ∧
      (∃ k, (z.kerne k).laeuft = some c) ∧ z.status c = .laeuft ∧
      (hw.angebot (t + ab)).crash = false ∧
      ∃ w plan u spur s', E.system.ImplSchritt c z w [plan] u ∧
        FuehrtSchrittAus E.einrichtung (t + ab) c z u plan spur s') →
    (∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ k, hw.gelegenheit (t + ab) k ∧
      ∃ z, tail.zustand t = some z ∧ (z.kerne k).laeuft = some c) →
    ∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ w spur, tail.spur t = some (.kontext c w, spur)

theorem fairerSchritt_taktAb (hw : HwLauf) (ab t : Nat)
    (s : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Takt (fun t => Lauffolge E hw (t + ab)) (KeinSchritt (fun t => Lauffolge E hw (t + ab))) t s
      (fairerSchritt E hw (t + ab) s).2 (fairerSchritt E hw (t + ab) s).1 := by
  unfold fairerSchritt
  classical
  split
  · next h1 =>
    exact .schritt rfl (Classical.choose_spec (Classical.choose_spec h1)).1
  · next h1 =>
    split
    · next h2 =>
      exact .schritt rfl (Classical.choose_spec (Classical.choose_spec h2))
    · next h2 =>
      refine .wartet rfl rfl (fun ev next step => h2 ⟨ev, next, step⟩)

noncomputable def fairerFolgeAb (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund))
    (ab : Nat) :
    Nat → Option (Zustand L Ort Wert Raum Lok Grund) ×
      Option (SchrittWahl Wahl × SchrittSpur Ort Wert)
  | 0 => (init, none)
  | t + 1 => fairerSchritt E hw (t + ab) (fairerFolgeAb hw init ab t).1

noncomputable def fairerZeitAb (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund))
    (ab : Nat) : Zeitlauf (fun t => Lauffolge E hw (t + ab)) where
  zustand := fun t => (fairerFolgeAb E hw init ab t).1
  spur := fun t => (fairerFolgeAb E hw init ab (t + 1)).2
  takt := fun t => fairerSchritt_taktAb E hw ab t (fairerFolgeAb E hw init ab t).1

theorem fairerZeitAb_start (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund))
    (ab : Nat) : (fairerZeitAb E hw init ab).zustand 0 = init := rfl

/-- The shifted fair schedule serves every continuously ready context infinitely often. -/
theorem fairerZeitAb_fair (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund))
    (ab : Nat) (s : AussenStart) : ShiftFair E hw ab s (fairerZeitAb E hw init ab) := by
  intro a c bereit oppd n hn
  obtain ⟨t, ht, k, gelegenheit, z, eq, dispatch⟩ := oppd (max n a) (Nat.le_max_right _ _)
  have hstate : (fairerFolgeAb E hw init ab t).1 = some z := eq
  obtain ⟨z', eq', _, live, normal, w, plan, u, spur, s', regel, aus⟩ :=
    bereit t ((Nat.le_max_right n a).trans ht)
  have same : z' = z := Option.some.inj (eq'.symm.trans hstate)
  subst z'
  have schritt : Lauffolge E hw (t + ab) (some z) (.kontext c w, spur) s' :=
    .schritt (.kontext normal ⟨k, gelegenheit, dispatch, live⟩ regel aus)
  have bevorzugt : BevorzugtSchritt hw (t + ab) (some z) (.kontext c w, spur) :=
    ⟨c, w, spur, k, rfl, gelegenheit, z, rfl, dispatch⟩
  have wahl : ∃ ev next, Lauffolge E hw (t + ab) (some z) ev next ∧
      BevorzugtSchritt hw (t + ab) (some z) ev :=
    ⟨_, _, schritt, bevorzugt⟩
  have spurEq : (fairerZeitAb E hw init ab).spur t = some (Classical.choose wahl) := by
    show (fairerSchritt E hw (t + ab) (fairerFolgeAb E hw init ab t).1).2 = _
    rw [hstate]
    unfold fairerSchritt
    classical
    rw [dif_pos wahl]
  have spec := Classical.choose_spec (Classical.choose_spec wahl)
  obtain ⟨c', w', spur', k', hev, geleg', z0, hseq, dispatch'⟩ := spec.2
  have kk : k' = k := Option.some.inj (geleg'.symm.trans gelegenheit)
  subst kk
  have z0eq : z0 = z := Option.some.inj hseq.symm
  subst z0
  have gleich : c' = c := Option.some.inj (dispatch'.symm.trans dispatch)
  subst gleich
  exact ⟨t, (Nat.le_max_left n a).trans ht, w', spur', hev ▸ spurEq⟩

/-- The fair-history lift with the exact start and hardware projection of the seventh conjunct. -/
theorem fairer_lauf {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (start : E.ZulStart h s) (fair : FairLaeufe E.katalog h hw) :
    ∃ ρ, Laeufe E h ρ ∧ ρ.start = s ∧ ρ.hw = hw :=
  lauf_mit_hw E fair.hardware start fair.konform

theorem lauf_ab_start {h : Umgebung} {s : AussenStart}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) :
    ∃ ρ, Laeufe E h ρ ∧ ρ.start = s := by
  let hw : HwLauf := ⟨fun _ => ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩, h.politik⟩
  have konform : hw.konform E.katalog h := by
    refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact fun _ h => nomatch h
    · exact fun _ h => nomatch h
    · exact fun _ h => (List.not_mem_nil h).elim
    · exact fun _ h => nomatch h
    · exact fun h => h.elim (fun h => nomatch h) (fun h => nomatch h)
  obtain ⟨ρ, run, sameStart, hwEq⟩ := lauf_mit_hw E hardware start konform
  refine ⟨ρ, ⟨run.1, run.2.1, run.2.2.1, run.2.2.2.1, ?_⟩, sameStart⟩
  have keine : ∀ t k, ¬ hw.gelegenheit t k := fun t k h => nomatch h
  intro a c _ oppd n hn
  obtain ⟨t, _, k, opp, _⟩ := oppd n hn
  rw [hwEq] at opp
  exact (keine t k opp).elim

theorem lauf_erfuellbar (katalog : KatalogWohlgeformt E.katalog) (bild : E.bild.gueltig E.katalog.plattform.ziel) :
    ∃ h s hw ρ, E.ZulStart h s ∧ FairLaeufe E.katalog h hw ∧
      Laeufe E h ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  obtain ⟨h, hw, hardware, fair⟩ := katalog_nichtLeer E.katalog katalog
  obtain ⟨s, start⟩ := zulStart_erfuellbar hardware bild
  obtain ⟨ρ, run, sameStart, sameHw⟩ := fairer_lauf E start fair
  exact ⟨h, s, hw, ρ, start, fair, run, sameStart, sameHw⟩

/-- Every offered crash is taken at a cut with a loaded implementation state. -/
theorem absturz_am_schnitt {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι}
    {ρ : Lauf E} {t : Nat} {s : Zustand L Ort Wert Raum Lok Grund}
    (atCut : ρ.zeit.zustand t = some s) (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    ∃ next, ρ.zeit.spur t = some (.absturz, absturzSpur) ∧ ρ.zeit.zustand (t + 1) = some next ∧
      AbsturzSchritt E.einrichtung.persistenzRegion E.einrichtung.wiederanlauf E.katalog ρ.hw t s absturzSpur next := by
  have tick := ρ.zeit.takt t
  rw [atCut] at tick
  cases tick with
  | schritt label step =>
    cases transition : ρ.zeit.zustand (t + 1) with
    | none =>
      rw [transition] at step
      cases step
    | some next =>
      rw [transition] at step
      cases step with
      | schritt h =>
        obtain ⟨wahl, crash⟩ := h.absturzfall _ _ offer
        exact ⟨next, label.trans (congrArg some (Prod.ext wahl crash.genau.1)), rfl, crash.genau.1 ▸ crash⟩
  | wartet _ _ pause =>
    exact (pause _ _ (.schritt (.absturz (absturz_schritt_erfuellbar _ _ offer s)))).elim

/-- A crash can be placed at any chosen cut of a fair hardware history selecting the row. -/
theorem fairer_absturz_erfuellbar {k h hw} (fair : FairLaeufe k h hw)
    (selected : k.enthaelt .persistence) (crashCut : Nat) :
    ∃ next, FairLaeufe k h next ∧ AbsturzAngeboten k next crashCut := by
  let next : HwLauf := { hw with
    angebot := fun t => { hw.angebot t with crash := if t = crashCut then true else (hw.angebot t).crash } }
  refine ⟨next, ⟨fair.hardware, fair.politik, ?_, fair.kerne, fair.interrupts,
    fair.auslieferung, fair.medium, fair.cycles, fair.zeit⟩, selected, ?_⟩
  · intro t
    have valid := fair.gueltig t
    exact ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, fun _ => selected⟩
  · simp only [next, ↓reduceIte]

theorem ladefehler_endlich (ρ : Lauf E) (failure : ρ.zeit.zustand 0 = none) :
    ρ.zeit.Endlich := by
  have idle (t : Nat) (absent : ρ.zeit.zustand t = none) :
      ρ.zeit.spur t = none ∧ ρ.zeit.zustand (t + 1) = none := by
    cases ρ.zeit.takt t with
    | schritt _label step =>
      rw [absent] at step
      cases step
    | wartet label eq _pause => exact ⟨label, eq.trans absent⟩
  have absent (t : Nat) : ρ.zeit.zustand t = none := by
    induction t with
    | zero => exact failure
    | succ t ih => exact (idle t ih).2
  exact ⟨⟨0, Or.inl rfl⟩, fun t _ => (idle t (absent t)).1⟩

namespace I

structure Lauf where
  start : AussenStart
  umgebung : Umgebung
  hw : HwLauf
  zeit : Zeitlauf (Schritt E.einrichtung E.system E.katalog hw) (fun t _ => ¬ AbsturzAngeboten E.katalog hw t)
  /-- The context using a core opportunity for a private implementation step. -/
  belegt : Nat → Option Kontext

abbrev Schnitt (ρ : Lauf E) : Type := ρ.zeit.Schnitt

def ZustandAm (ρ : Lauf E) (t : Schnitt E ρ) : AussenStart × Zustand L Ort Wert Raum Lok Grund :=
  (ρ.start, ρ.zeit.zustand t.val)

/-- Maximal ideal runs use the same hardware opportunities. A private core step
    occupies its tick without adding an ideal transition. Unoccupied ticks must
    still take a step whenever one is possible. -/
def Laeufe (ρ : Lauf E) : Prop :=
  Hardware E.katalog ρ.umgebung ∧ ρ.hw.konform E.katalog ρ.umgebung ∧
    E.ZulStart ρ.umgebung ρ.start ∧ ρ.zeit.zustand 0 = (start E ρ.start).2 ∧
    ρ.zeit.Maximal (fun t => ρ.belegt t = none) ∧
    (∀ t c, ρ.belegt t = some c → ρ.zeit.spur t = none ∧ KannSchreiten ρ.hw t c (ρ.zeit.zustand t))

/-- A crash offer is mandatory even at an ideal cut where a private step could normally pause. -/
theorem absturz_am_schnitt (ρ : Lauf E) {t : Nat} (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    ρ.zeit.spur t = some (.absturz, absturzSpur) ∧
      AbsturzSchritt E.einrichtung.persistenzRegion E.einrichtung.wiederanlauf E.katalog ρ.hw t
        (ρ.zeit.zustand t) absturzSpur (ρ.zeit.zustand (t + 1)) := by
  cases ρ.zeit.takt t with
  | schritt label step =>
    obtain ⟨wahl, crash⟩ := step.absturzfall _ _ offer
    exact ⟨label.trans (congrArg some (Prod.ext wahl crash.genau.1)), crash.genau.1 ▸ crash⟩
  | wartet _ _ pause => exact (pause offer).elim

theorem anfang (ρ : Lauf E) (h : Laeufe E ρ) :
    ZustandAm E ρ ⟨0, Or.inl rfl⟩ = start E ρ.start :=
  Prod.ext rfl h.2.2.2.1

theorem lauf_mit_hw {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) (konform : hw.konform E.katalog h) :
    ∃ ρ, Laeufe E ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert (Schritt E.einrichtung E.system E.katalog hw) (I.start E s).2
  have pause t z (stuck : KeinSchritt (Schritt E.einrichtung E.system E.katalog hw) t z) :
      ¬ AbsturzAngeboten E.katalog hw t :=
    fun offer => stuck _ _ (.absturz (absturz_schritt_erfuellbar _ _ offer z))
  exact ⟨⟨s, h, hw, zeit.erlaubePausen pause, fun _ => none⟩,
    ⟨hardware, konform, start, init, zeit.erlaubePausen_maximal pause _ (fun _ => rfl),
      fun _ _ h => nomatch h⟩, rfl, rfl⟩

end I

/-- An admissible fair history can exercise the crash boundary in both machines. The
    implementation premise records an actual successful load, as for the generic cut lemma. -/
theorem absturz_laeufe_erfuellbar {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    {z : Zustand L Ort Wert Raum Lok Grund}
    (start : E.ZulStart h s) (fair : FairLaeufe E.katalog h hw)
    (selected : E.katalog.enthaelt .persistence) (loaded : E.laden s (h.lade E.bild) = some z) :
    ∃ ρ : Lauf E, ∃ η : I.Lauf E, Laeufe E h ρ ∧ I.Laeufe E η ∧
      ρ.start = s ∧ η.start = s ∧ ρ.hw = η.hw ∧ FairLaeufe E.katalog h ρ.hw ∧
      ρ.zeit.spur 0 = some (.absturz, absturzSpur) ∧ η.zeit.spur 0 = some (.absturz, absturzSpur) := by
  obtain ⟨crashHw, fairCrash, offer⟩ := fairer_absturz_erfuellbar fair selected 0
  obtain ⟨ρ, run, startEq, hwEq⟩ := fairer_lauf E start fairCrash
  obtain ⟨η, ideal, startEq', hwEq'⟩ := I.lauf_mit_hw E fairCrash.hardware start fairCrash.konform
  have load : ρ.zeit.zustand 0 = some z := by
    rw [run.2.2.2.1, startEq, loaded]
  obtain ⟨_, label, _, _⟩ := absturz_am_schnitt load (hwEq.symm ▸ offer)
  obtain ⟨label', _⟩ := I.absturz_am_schnitt E η (hwEq'.symm ▸ offer)
  exact ⟨ρ, η, run, ideal, startEq, startEq', hwEq.trans hwEq'.symm, hwEq.symm ▸ fairCrash,
    label, label'⟩

end Gabbro.Core.Maschine
