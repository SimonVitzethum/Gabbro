module

public import Core.Verfeinerung.Protokoll

@[expose] public section

namespace Gabbro.Core.Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
variable {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
variable {Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι}
variable {s u s' : Zustand L Ort Wert Raum Lok Grund}

omit [DecidableEq L] in
theorem Zustandsrahmen.verbrauch (rahmen : Zustandsrahmen s u) (vorher : s.Verbrauch) :
    u.Verbrauch := by
  intro c
  simpa only [Zustand.angekommen, rahmen.antworten, rahmen.verbraucht, rahmen.verworfen] using vorher c

theorem FuehrtAus.verbrauch {t c aktion lock outside v}
    (action : FuehrtAus e t c s u aktion lock outside v)
    (frame : Zustandsrahmen s u) (vorher : s.Verbrauch) : v.Verbrauch := by
  have inner := frame.verbrauch vorher
  cases action with
  | intern => exact inner
  | warte _ => exact inner
  | sperre _ _ => exact inner
  | frage _ => exact inner
  | verbrauche ready =>
    have same : u.naechsteAntwort c = s.naechsteAntwort c := by
      simp only [Zustand.naechsteAntwort, Zustand.angekommen, frame.antworten, frame.verbraucht, frame.verworfen]
    exact Zustand.verbrauche_verbrauch inner (same.trans ready)
  | rueckkehr _ _ => exact inner

theorem FuehrtSchrittAus.verbrauch {t c plan spur}
    (step : FuehrtSchrittAus e t c s u plan spur s') (vorher : s.Verbrauch) : s'.Verbrauch := by
  obtain ⟨frame, _, lock, v, action, _, state⟩ := step
  rw [state]
  exact action.verbrauch frame vorher

theorem ImplSchritt.verbrauch {k hw t spur} (step : ImplSchritt e Sy k hw t s spur s')
    (vorher : s.Verbrauch) : s'.Verbrauch := by
  cases step with
  | kontext _ _ _ execute => exact execute.verbrauch vorher
  | antwort _ arrives =>
    rw [arrives.2.2.2]
    exact Zustand.antwort_verbrauch vorher _
  | interrupt _ enters =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, state⟩ := enters
    rw [state]
    exact vorher
  | absturz crash => exact (crash.verbrauch vorher).1

variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι}

/-- The M4 graph and answer-consumption invariants hold on every hardware cut
    from a load with the canonical protocol state, including at crashes. -/
theorem speicher_verbrauch_im_lauf {ρ : Lauf E}
    (init : ∃ z, ρ.zeit.zustand 0 = some z ∧ I.ProtokollBezug z (I.start E ρ.start).2) (t : Nat) :
    ∃ z, ρ.zeit.zustand t = some z ∧ z.SpeicherGut ∧ z.Verbrauch := by
  induction t with
  | zero =>
    obtain ⟨z, load, related⟩ := init
    have canonical : (I.start E ρ.start).2.SpeicherGut ∧ (I.start E ρ.start).2.Verbrauch :=
      ⟨⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩, fun _ => Nat.zero_le _⟩
    change { z with lokal := (I.start E ρ.start).2.lokal } = (I.start E ρ.start).2 at related
    rw [← related] at canonical
    exact ⟨z, load, canonical⟩
  | succ t ih =>
    obtain ⟨z, loaded, memory, answers⟩ := ih
    have tick := ρ.zeit.takt t
    rw [loaded] at tick
    cases tick with
    | schritt _ event =>
      cases after : ρ.zeit.zustand (t + 1) with
      | none =>
        rw [after] at event
        cases event
      | some next =>
        rw [after] at event
        cases event with
        | schritt step => exact ⟨_, rfl, impl_speicher_gut _ _ step memory, step.verbrauch answers⟩
    | wartet _ same _ => exact ⟨z, same, memory, answers⟩

/-- Authority for every concrete context transition compatible with the recorded
    tick. This uses the unprojected execution plan and the pre-state handles. -/
def BerechtigungAmTakt (ρ : Lauf E) (t : Nat) : Prop :=
  ∀ s s' c w spur u plan,
    ρ.zeit.zustand t = some s → ρ.zeit.zustand (t + 1) = some s' →
    ρ.zeit.spur t = some (I.SchrittWahl.kontext c w, spur) →
    (ρ.hw.angebot t).crash = false → KannSchreiten ρ.hw t c s →
    E.system.ImplSchritt c s w [plan] u → FuehrtSchrittAus E.einrichtung t c s u plan spur s' →
    plan.Autorisiert E.einrichtung s c

end Gabbro.Core.Maschine
