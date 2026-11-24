module

public import Core.Verfeinerung.ZielFX

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- Only an actual step, a crash reset, or an exit discharges an instance. -/
def Erledigt (η : Lauf E) (c : Kontext) (t : Nat) : Prop :=
  (∃ w spur, η.zeit.spur t = some (.kontext c w, spur)) ∨
    η.zeit.spur t = some (.absturz, absturzSpur) ∨
    (∃ e, (η.zeit.zustand (t + 1)).status c = .beendet e)

/-- A dispatched unit whose step instance remains open on the entire suffix. -/
def BleibtOffen (η : Lauf E) (c : Kontext) (f : F) (a : Nat) : Prop :=
  (∃ k, ((η.zeit.zustand a).kerne k).laeuft = some c) ∧
    ∀ t, a ≤ t → E.system.kopf (η.zeit.zustand t) c = some f ∧
      (η.zeit.zustand t).status c = .laeuft ∧ ¬ Erledigt η c t

def Bereit (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) : Prop :=
  ¬ E.system.fertig s c ∧ (∀ b, ¬ E.system.blockiert s c b) ∧ ∃ w plans u, E.system.ISchritt c s w plans u

/-- Repeated eligibility is sufficient for lock acquisition. Other forms are
    subject to continuously enabled progress. -/
def Aktiviert (η : Lauf E) (c : Kontext) (a : Nat) : Prop :=
  (∀ t, a ≤ t → Bereit (E := E) (η.zeit.zustand t) c) ∨
    (∀ n, a ≤ n → ∃ t, n ≤ t ∧ Bereit (E := E) (η.zeit.zustand t) c ∧
      ∃ w plan u l,
        E.system.ISchritt c (η.zeit.zustand t) w [plan] u ∧ plan.aktion = .sperre l .nehmen)

def Haengt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (ρ : Maschine.Lauf E) (η : Lauf E) (c : Kontext) : Prop :=
  FairLaeufe E.katalog η.umgebung ρ.hw ∧ ∃ a f, BleibtOffen η c f a ∧ Aktiviert η c a

inductive FortschrittsKlasse (F : Type) where
  | blockierend
  | lockFree (einheiten : F → Prop)

def SystemAktiv (forms : F → Prop) (η : Lauf E) (a : Nat) : Prop :=
  ∀ n, a ≤ n → ∃ t c f, n ≤ t ∧ forms f ∧ E.system.kopf (η.zeit.zustand t) c = some f ∧
    Bereit (E := E) (η.zeit.zustand t) c

def SystemSchritt (forms : F → Prop) (η : Lauf E) (a : Nat) : Prop :=
  ∃ t, a ≤ t ∧ (η.zeit.spur t = some (.absturz, absturzSpur) ∨
    ∃ c f w spur, forms f ∧ E.system.kopf (η.zeit.zustand t) c = some f ∧
      η.zeit.spur t = some (.kontext c w, spur))

/-- Progress of the composed rules, with an additional system-wide completion
    condition for the forms checked as lock-free. -/
def FortschrittDerKlasse (klasse : FortschrittsKlasse F) (η : Lauf E) : Prop :=
  (∀ t c, (η.zeit.zustand t).status c = .laeuft →
    (∃ k, ((η.zeit.zustand t).kerne k).laeuft = some c) →
    FortschrittAm E.einrichtung E.system E.katalog η.hw t (η.zeit.zustand t) c) ∧
  match klasse with
  | .blockierend => True
  | .lockFree forms => ∀ a, SystemAktiv forms η a → SystemSchritt forms η a

/-- The scheduler and checked forms establish which offered ticks service a
    context. Core fairness alone does not arbitrate a simultaneous interrupt
    or answer. The selection rule therefore concerns actual recorded ticks. -/
structure FortschrittsPflichten (klasse : FortschrittsKlasse F)
    (ρ : Maschine.Lauf E) (η : Lauf E) (nutzbar : Nat → Kontext → Prop) : Prop where
  fertig : ∀ s c, E.system.kopf s c = none → E.system.fertig s c
  regeln : ∀ f, Gabbro.Core.Ideal.RegelFortschritt E.system f
  komponierbar : ∀ f, RegelKomponierbar E.einrichtung E.system f
  angebot : ∀ t c, nutzbar t c →
    ∃ k, ((η.zeit.zustand t).kerne k).laeuft = some c ∧ η.hw.gelegenheit t k
  wahl : ∀ t c, nutzbar t c →
    (∃ w spur s', Schritt E.einrichtung E.system E.katalog η.hw t (η.zeit.zustand t) (.kontext c w, spur) s') →
    ∃ w spur, ρ.zeit.spur t = some (.kontext c w, spur)
  individuell : FairLaeufe E.katalog η.umgebung ρ.hw →
    ∀ a c f, BleibtOffen η c f a → Aktiviert η c a →
    ∀ n, a ≤ n → ∃ t, n ≤ t ∧ nutzbar t c ∧ Bereit (E := E) (η.zeit.zustand t) c
  systemweit : FairLaeufe E.katalog η.umgebung ρ.hw →
    match klasse with
    | .blockierend => True
    | .lockFree forms =>
      ∀ a, SystemAktiv forms η a → ¬ SystemSchritt forms η a →
        ∃ t c f, a ≤ t ∧ forms f ∧ BleibtOffen η c f t ∧ Aktiviert η c t

variable {ρ : Maschine.Lauf E} {η : Lauf E} {lokal : LokalerBezug Lok} {laenge : F → Nat}
variable {klasse : FortschrittsKlasse F} {nutzbar : Nat → Kontext → Prop}

theorem FortschrittsPflichten.vollzug (pf : FortschrittsPflichten klasse ρ η nutzbar)
    (valid : Laeufe E η) {t c} (slot : nutzbar t c) (live : (η.zeit.zustand t).status c = .laeuft)
    (bereit : Bereit (E := E) (η.zeit.zustand t) c) :
    η.zeit.spur t = some (.absturz, absturzSpur) ∨
      ∃ w spur, ρ.zeit.spur t = some (.kontext c w, spur) := by
  obtain ⟨k, dispatch, offer⟩ := pf.angebot t c slot
  rcases
    fortschritt_im_lauf valid pf.fertig pf.regeln pf.komponierbar t c live ⟨k, dispatch⟩
    with crash | done | ⟨b, blocked⟩ | step | withheld
  · obtain ⟨_, _, crash⟩ := crash
    cases crash with
    | absturz fault => exact Or.inl (absturz_am_schnitt E η fault.1).1
  · exact (bereit.1 done).elim
  · exact (bereit.2.1 b blocked).elim
  · exact Or.inr (pf.wahl t c slot step)
  · exact (withheld.2 k dispatch offer).elim

omit [DecidableEq L] in
theorem SpurAbgleich.ideales_etikett {event : SchrittWahl Wahl × SchrittSpur Ort Wert} {ideal}
    (aligned : SpurAbgleich (some event) ideal) : ideal = none ∨ ideal = some event := by
  cases aligned with
  | privat _ _ => exact Or.inl rfl
  | schritt _ => exact Or.inr rfl

theorem Laufabgleich.entladet (matchRun : Laufabgleich ρ η lokal) (valid : Laeufe E η)
    (bound : StotterSchranke laenge η) (pf : FortschrittsPflichten klasse ρ η nutzbar)
    (fair : FairLaeufe E.katalog η.umgebung ρ.hw) {a c f}
    (openStep : BleibtOffen η c f a) (enabled : Aktiviert η c a) : False := by
  classical
  have marks (n : Nat) (after : a ≤ n) : ∃ t, n ≤ t ∧ η.belegt t = some c := by
    obtain ⟨t, later, slot, ready⟩ := pf.individuell fair a c f openStep enabled n after
    obtain ⟨_, live, openTick⟩ := openStep.2 t (after.trans later)
    rcases pf.vollzug valid slot live ready with crash | ⟨w, spur, chosen⟩
    · exact (openTick (Or.inr (Or.inl crash))).elim
    · have tick := matchRun.spur t
      rw [chosen] at tick
      rcases tick.ideales_etikett with idle | step
      ·
        have marked : η.belegt t ≠ none := by
          intro h
          rcases (matchRun.frei t).mp h with no | yes
          · rw [chosen] at no
            cases no
          · exact yes idle
        cases captured : η.belegt t with
        | none => exact (marked captured).elim
        | some d' =>
          obtain ⟨v', _, event, _⟩ := matchRun.belegt t d' captured
          have context := (SchrittWahl.kontext.inj (congrArg Prod.fst (Option.some.inj (event.symm.trans chosen)))).1
          exact ⟨t, later, context ▸ captured⟩
      · exact (openTick (Or.inl ⟨w, spur, step⟩)).elim
  have limited n : zaehle (fun t => decide (η.belegt t = some c)) a n ≤ laenge f :=
    bound c f a n (fun t after _ => by
      obtain ⟨head, _, uncompleted⟩ := openStep.2 t after
      exact ⟨head, fun w spur h => uncompleted (Or.inl ⟨w, spur, h⟩), fun h => uncompleted (Or.inr (Or.inl h))⟩)
  obtain ⟨q, quiet⟩ := markierungen_endlich (fun t => decide (η.belegt t = some c)) a (laenge f) limited
  obtain ⟨t, later, mark⟩ := marks (max a q) (Nat.le_max_left _ _)
  have never := quiet t ((Nat.le_max_right _ _).trans later)
  simp only [mark, decide_true] at never
  cases never

theorem Laufabgleich.fortschritt (matched : Laufabgleich ρ η lokal) (valid : Laeufe E η)
    (bound : StotterSchranke laenge η) (pf : FortschrittsPflichten klasse ρ η nutzbar)
    (fair : FairLaeufe E.katalog η.umgebung ρ.hw) :
    (∀ c, ¬ Haengt E ρ η c) ∧ FortschrittDerKlasse klasse η := by
  refine ⟨?_, fortschritt_im_lauf valid pf.fertig pf.regeln pf.komponierbar, ?_⟩
  · rintro c ⟨_, a, f, opened, enabled⟩
    exact matched.entladet valid bound pf fair opened enabled
  · cases klasse with
    | blockierend => trivial
    | lockFree forms =>
      intro a active
      by_contra absent
      obtain ⟨_, _, _, _, _, opened, enabled⟩ := pf.systemweit fair a active absent
      exact matched.entladet valid bound pf fair opened enabled

theorem sim_ziel_fortschritt_im_lauf {h : Umgebung} (pflicht : SimPflichten E lokal laenge)
    (run : Maschine.Laeufe E h ρ)
    (fortschritt : ∀ η, Laeufe E η → Laufabgleich ρ η lokal → η.umgebung = h →
      ∃ nutzbar, FortschrittsPflichten klasse ρ η nutzbar) :
    ∃ η, Laeufe E η ∧ Sim E ρ η ∧ (∀ k, ZielFX E h ρ k) ∧
      (FairLaeufe E.katalog h ρ.hw → (∀ c, ¬ Haengt E ρ η c) ∧ FortschrittDerKlasse klasse η) := by
  obtain ⟨η, valid, matched, environment⟩ := laufabgleich pflicht.abgleich run
  have bound := pflicht.abgleich.schranke h ρ η run matched
  have sim := matched.sim valid bound (pflicht.autoritaet h ρ run) pflicht.fortsetzung
  obtain ⟨_, pf⟩ := fortschritt η valid matched environment
  exact ⟨η, valid, sim, pflicht.zielFX run, fun fair => matched.fortschritt valid bound pf (environment.symm ▸ fair)⟩

end Gabbro.Core.Maschine.I
