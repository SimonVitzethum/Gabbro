module

public import Core.Ideal.Eigenschaften
public import Core.Maschine.Protokoll
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Ideal (IBestimmt IFortschritt RegelBestimmt RegelFortschritt)
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
variable (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
variable (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι)

/-- The composed step is determined by the source choice and the RC11 order resolution. -/
def Bestimmt : Prop :=
  ∀ k hw t s w es es' s' s'',
    Schritt e Sy k hw t s (w, es) s' → Schritt e Sy k hw t s (w, es') s'' →
    SpeicherWahlGleich s'.graph s''.graph → es = es' ∧ s' = s''

/-- The composed step is determined when the forms are: `I.Bestimmt` of the system, the protocol lemmas and the
    memory resolution. -/
theorem bestimmt_aus_formen (forms : IBestimmt Sy) : Bestimmt e Sy := by
  intro k hw t s w es es' s' s'' left right memory
  cases left with
  | kontext _ _ rule run =>
    cases right with
    | kontext _ _ rule' run' =>
      obtain ⟨plan, states⟩ := forms _ _ _ _ _ _ _ rule rule'
      cases List.cons.inj plan |>.1
      cases states
      exact run.bestimmt run' memory
  | antwort _ arrives =>
    cases right with
    | antwort _ arrives' => exact arrives.bestimmt arrives' memory
  | interrupt _ enters =>
    cases right with
    | interrupt _ enters' => exact enters.bestimmt enters' memory
  | absturz crash =>
    cases right with
    | absturz crash' => exact ⟨crash.genau.1.trans crash'.genau.1.symm, crash.genau.2.trans crash'.genau.2.symm⟩

theorem bestimmt_aus_regeln (regeln : ∀ i, RegelBestimmt (Sy.regel i)) : Bestimmt e Sy :=
  bestimmt_aus_formen e Sy (Gabbro.Core.Ideal.bestimmt_aus_regeln Sy regeln)

/-- **The composed step is determined when every form that stands at a head is determinate.** A form that no state
    ever presents at a head of a context (an access instruction in a system whose code has none) owes nothing. -/
theorem bestimmt_aus_kopfregeln
    (regeln : ∀ i s c, Sy.kopf s c = some i → RegelBestimmt (Sy.regel i)) : Bestimmt e Sy := by
  refine bestimmt_aus_formen e Sy ?_
  intro c s w es es' s1 s2 ⟨i, hi, h1⟩ ⟨j, hj, h2⟩
  rw [hi] at hj
  cases hj
  exact regeln i s c hi c s w es es' s1 s2 h1 h2

/-- A form with an ideal rule must supply one plan that can execute through the shared
    machine protocol from a consistent graph. This is checked when the form enters. -/
def RegelKomponierbar (i : ι) : Prop :=
  ∀ t s c w plans u, Sy.kopf s c = some i → s.SpeicherGut → (Sy.regel i).ideal c s w plans u →
    ∃ plan spur s', plans = [plan] ∧ FuehrtSchrittAus e t c s u plan spur s'

/-- At a cut with a live dispatched context, the hardware may crash, the context may have
    finished or blocked, or an enabled form may step or wait for a core opportunity. -/
def FortschrittAm (k : Katalog.Katalog) (hw : HwLauf) (t : Nat)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) : Prop :=
  (∃ spur s', Schritt e Sy k hw t s (.absturz, spur) s') ∨
    Sy.fertig s c ∨ (∃ b, Sy.blockiert s c b) ∨
    (∃ w spur s', Schritt e Sy k hw t s (.kontext c w, spur) s') ∨
    ((∃ w plans u, Sy.ISchritt c s w plans u) ∧
      ∀ kern, (s.kerne kern).laeuft = some c → ¬ hw.gelegenheit t kern)

def Fortschritt : Prop :=
  ∀ k h hw t s c, hw.konform k h → s.SpeicherGut → s.status c = .laeuft →
    (∃ kern, (s.kerne kern).laeuft = some c) → FortschrittAm e Sy k hw t s c

theorem fortschritt_aus_regeln (fertig : ∀ s c, Sy.kopf s c = none → Sy.fertig s c)
    (regeln : ∀ i, RegelFortschritt Sy i) (komponierbar : ∀ i, RegelKomponierbar e Sy i) :
    Fortschritt e Sy := by
  have forms : IFortschritt Sy := Gabbro.Core.Ideal.fortschritt_aus_regeln Sy fertig regeln
  intro k h hw t s c konform memory running _
  cases offer : (hw.angebot t).crash with
  | true =>
    have selected := (konform.2 t).2.2.2.2 (Or.inr offer)
    exact Or.inl ⟨_, _, .absturz (absturz_schritt_erfuellbar _ _ ⟨selected, offer⟩ s)⟩
  | false =>
    rcases forms s c with done | ⟨w, plans, u, rule⟩ | blocked
    · exact Or.inr (Or.inl done)
    · by_cases ready : KannSchreiten hw t c s
      · obtain ⟨i, head, form⟩ := rule
        obtain ⟨plan, spur, s', rfl, run⟩ := komponierbar i t s c w plans u head memory form
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, spur, s', .kontext offer ready ⟨i, head, form⟩ run⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨⟨w, plans, u, rule⟩, fun kern dispatch slot => ready ⟨kern, slot, dispatch, running⟩⟩)))
    · exact Or.inr (Or.inr (Or.inl blocked))

variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι}

theorem speicher_gut_im_lauf {ρ : Lauf E} (valid : Laeufe E ρ) (t : Nat) :
    (ρ.zeit.zustand t).SpeicherGut := by
  induction t with
  | zero =>
    rw [valid.2.2.2.1]
    exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  | succ t ih =>
    cases ρ.zeit.takt t with
    | schritt _ step => exact ideal_speicher_gut _ _ step ih
    | wartet _ state _ => exact state.symm ▸ ih

/-- Any alternative step to the run's recorded choice and memory resolution has the same
    observation and next state. -/
theorem bestimmt_im_lauf {ρ : Lauf E}
    (regeln : ∀ i, RegelBestimmt (E.system.regel i)) {t w spur spur' s'}
    (recorded : ρ.zeit.spur t = some (w, spur))
    (alternate : Schritt E.einrichtung E.system E.katalog ρ.hw t (ρ.zeit.zustand t) (w, spur') s')
    (memory : SpeicherWahlGleich (ρ.zeit.zustand (t + 1)).graph s'.graph) :
    spur = spur' ∧ ρ.zeit.zustand (t + 1) = s' := by
  cases ρ.zeit.takt t with
  | schritt label step =>
    cases Option.some.inj (label.symm.trans recorded)
    exact bestimmt_aus_regeln _ _ regeln _ _ _ _ _ _ _ _ _ step alternate memory
  | wartet label _ _ => cases label.symm.trans recorded

/-- The composed progress alternatives hold at every hardware cut of an admissible ideal run. -/
theorem fortschritt_im_lauf {ρ : Lauf E} (valid : Laeufe E ρ)
    (fertig : ∀ s c, E.system.kopf s c = none → E.system.fertig s c)
    (regeln : ∀ i, RegelFortschritt E.system i)
    (komponierbar : ∀ i, RegelKomponierbar E.einrichtung E.system i)
    (t : Nat) (c : Kontext) (running : (ρ.zeit.zustand t).status c = .laeuft)
    (dispatch : ∃ kern, ((ρ.zeit.zustand t).kerne kern).laeuft = some c) :
    FortschrittAm E.einrichtung E.system E.katalog ρ.hw t (ρ.zeit.zustand t) c :=
  fortschritt_aus_regeln _ _ fertig regeln komponierbar _ _ _ _ _ _ valid.2.1 (speicher_gut_im_lauf valid t)
    running dispatch

/-- The recovery entry has the same progress alternatives as any other dispatched context. -/
theorem fortschritt_nach_absturz {ρ : Lauf E} (valid : Laeufe E ρ)
    (fertig : ∀ s c, E.system.kopf s c = none → E.system.fertig s c)
    (regeln : ∀ i, RegelFortschritt E.system i)
    (komponierbar : ∀ i, RegelKomponierbar E.einrichtung E.system i)
    {t : Nat} (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    FortschrittAm E.einrichtung E.system E.katalog ρ.hw (t + 1) (ρ.zeit.zustand (t + 1))
      E.einrichtung.wiederanlauf.eintritt := by
  obtain ⟨_, step⟩ := absturz_am_schnitt E ρ offer
  exact fortschritt_im_lauf valid fertig regeln komponierbar (t + 1) _ step.neustart.2.2.2.2.1
    ⟨E.einrichtung.wiederanlauf.kern, step.neustart.2.2.2.2.2.1⟩

/-- A one-form unit with an internal action jointly discharges the obligations and takes
    a composed step at a dispatched core opportunity. -/
theorem komposition_erfuellbar (k : Katalog.Katalog) (hw : HwLauf) (t : Nat) (c : Kontext)
    (s : Zustand L Ort Wert Raum Lok Grund) (normal : (hw.angebot t).crash = false)
    (bereit : KannSchreiten hw t c s) :
    ∃ system : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Unit Unit,
      (∀ i, RegelBestimmt (system.regel i)) ∧
      (∀ s c, system.kopf s c = none → system.fertig s c) ∧
      (∀ i, RegelFortschritt system i ∧ RegelKomponierbar e system i) ∧
      Schritt e system k hw t s (.kontext c (), ⟨[], []⟩) s := by
  let plan : SchrittPlan L Ort Wert Bedingung := ⟨.intern, [], [], fun _ => false, fun _ => .na, e.initial⟩
  let form : Regel (Zustand L Ort Wert Raum Lok Grund) (SchrittPlan L Ort Wert Bedingung) Unit :=
    ⟨fun _ s _ es u => es = [plan] ∧ u = s, fun _ s _ es u => es = [plan] ∧ u = s⟩
  let system : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Unit Unit :=
    ⟨fun _ => form, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩
  have execute (t : Nat) (c : Kontext) (s : Zustand L Ort Wert Raum Lok Grund) :
      FuehrtSchrittAus e t c s s plan ⟨[], []⟩ s :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ h => (List.not_mem_nil h).elim,
      [], s, .intern, .nil _, rfl⟩
  refine ⟨system, ?_, ?_, ?_, .kontext normal bereit ⟨(), rfl, rfl, rfl⟩ (execute t c s)⟩
  · intro _ _ _ _ _ _ _ _ a b
    exact ⟨a.1.trans b.1.symm, a.2.trans b.2.symm⟩
  · exact fun _ _ noHead => nomatch noHead
  · intro i
    cases i
    refine ⟨fun s _ _ => Or.inl ⟨(), [plan], s, rfl, rfl⟩, ?_⟩
    intro t s c _ plans u _ _ rule
    obtain ⟨samePlan, sameState⟩ := rule
    subst u
    exact ⟨plan, ⟨[], []⟩, s, samePlan, execute t c s⟩

end Gabbro.Core.Maschine.I
