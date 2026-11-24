module

public import Core.Ideal.Absturz

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}
variable {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
variable {s i s' : Zustand L Ort Wert Raum Lok Grund}

/-- Agreement on the state owned by the M4 machine protocol. Form-local state can
    differ, for example when the implementation has executed part of a source unit. -/
def ProtokollBezug (s i : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  { s with lokal := i.lokal } = i

theorem ProtokollBezug.refl (s : Zustand L Ort Wert Raum Lok Grund) : ProtokollBezug s s := rfl

theorem ProtokollBezug.aussen (h : ProtokollBezug s i) : AussenBezug s i := by
  change { s with lokal := i.lokal } = i at h
  rw [← h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Arrival transports the actual question instance and its reply even if the
    form-local state is mid-unit. The same RC11 extension is used. -/
theorem ProtokollBezug.antwort (h : ProtokollBezug s i) {k hw t a spur}
    (konkret : AntwortSchritt e k hw t a s spur s') :
    ∃ i', AntwortSchritt e k hw t a i spur i' ∧ ProtokollBezug s' i' ∧ i'.lokal = i.lokal := by
  change { s with lokal := i.lokal } = i at h
  obtain ⟨offer, obs, memory, state⟩ := konkret
  refine ⟨{ s' with lokal := i.lokal }, ⟨?_, obs, ?_, ?_⟩, rfl, rfl⟩
  · rw [← h]
    exact offer
  · rw [← h]
    exact memory
  · rw [← h, state]
    rfl

/-- The pending offer, handler instance and observed delivery are shared. Each
    machine keeps its own form-local state when the handler is dispatched. -/
theorem ProtokollBezug.interrupt (h : ProtokollBezug s i) {hw t id spur}
    (konkret : UnterbrechungsSchritt e hw t id s spur s') :
    ∃ i', UnterbrechungsSchritt e hw t id i spur i' ∧ ProtokollBezug s' i' ∧ i'.lokal = i.lokal := by
  change { s with lokal := i.lokal } = i at h
  obtain ⟨k, irq, c, nmi, offer, pending, enter, dormant, obs, memory, state⟩ := konkret
  refine ⟨{ s' with lokal := i.lokal }, ⟨k, irq, c, nmi, offer, ?_, ?_, ?_, obs, ?_, ?_⟩, rfl, rfl⟩
  · rw [← h]
    exact pending
  · rw [← h]
    exact enter
  · rw [← h]
    exact dormant
  · rw [← h]
    exact memory
  · rw [← h, state]
    rfl

/-- Recovery starts both machines in the same full state, even when their
    form-local state differed before the crash. -/
theorem ProtokollBezug.absturz (h : ProtokollBezug s i) {region w k hw t spur}
    (konkret : AbsturzSchritt region w k hw t s spur s') :
    AbsturzSchritt region w k hw t i spur s' := by
  have medium : nachAbsturz s.persistenz = nachAbsturz i.persistenz :=
    congrArg (fun z => nachAbsturz z.persistenz) h
  have ideal := absturz_schritt_erfuellbar region w konkret.1 i
  obtain ⟨label, state⟩ := absturz_rahmen h.aussen medium konkret ideal
  exact label.symm ▸ state.symm ▸ ideal

variable [DecidableEq L] {Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι}

/-- Only a context transition needs a form-specific match. The common protocol
    matches each arrival, interrupt and crash at the same tick and in the same
    RC11 order as the concrete step. -/
theorem protokoll_schritt {k hw t spur}
    (bezug : ProtokollBezug s i) (konkret : ImplSchritt e Sy k hw t s spur s')
    (form : ∀ c w u plan, spur.1 = .kontext c w → (hw.angebot t).crash = false → KannSchreiten hw t c s →
      Sy.ImplSchritt c s w [plan] u → FuehrtSchrittAus e t c s u plan spur.2 s' →
      ∃ i', Schritt e Sy k hw t i spur i' ∧ ProtokollBezug s' i') :
    ∃ i', Schritt e Sy k hw t i spur i' ∧ ProtokollBezug s' i' := by
  cases konkret with
  | kontext normal ready rule execute =>
    exact form _ _ _ _ rfl normal ready rule execute
  | antwort normal arrives =>
    obtain ⟨i', step, next, _⟩ := bezug.antwort arrives
    exact ⟨i', .antwort normal step, next⟩
  | interrupt normal enters =>
    obtain ⟨i', step, next, _⟩ := bezug.interrupt enters
    exact ⟨i', .interrupt normal step, next⟩
  | absturz crash =>
    exact ⟨s', .absturz (bezug.absturz crash), ProtokollBezug.refl s'⟩

end Gabbro.Core.Maschine.I
