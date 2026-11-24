module

public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)

/-- Expose payload at public objects and capabilities in public namespaces. -/
def niedereAussensicht (label : Etiketten Ort) (s : AussenSicht) :
    (Objekt → Option ObjektSicht) × (Endpunkt → Nat → Option Handle) ×
      (Objekt → List UInt8 → Option Handle) :=
  (fun o => sichtbar (label.objekt o ∪ label.endpunkt o.endpoint) (s.objects o),
    fun e i => (s.channels e i).bind fun h => sichtbar (label.endpunkt e ∪ label.objekt h.origin.object) h,
    fun o bytes => (s.names o bytes).bind fun h =>
      sichtbar (label.objekt o ∪ label.endpunkt o.endpoint ∪ label.objekt h.origin.object) h)

/-- Boot assignment and granted extents are public. Contents of private boot locations are free. -/
def startProjektion (s : AussenStart) :=
  (s.bootCore, s.assignment, s.regions,
    (fun a => (sichtbar (E.etiketten.bootByte a) (s.inputBytes a)).join),
    niedereAussensicht E.etiketten s.outside)

def NiedrigGleich (s₁ s₂ : AussenStart) : Prop :=
  startProjektion E s₁ = startProjektion E s₂

/-- The public history is a sequence of low requests and low answers, in order. Outside policy
    inputs are total, including public histories no admitted run ever visits. -/
def niedrigerVerlauf (label : Etiketten Ort) (history : AussenVerlauf) : AussenVerlauf :=
  history.filter fun entry =>
    match entry.2 with
    | .frage q | .antwort q _ => oeffentlich (label.frage q)

/-- A public non-answer is represented by some warten. -/
def politikProjektion (label : Etiketten Ort) (p : AussenPolitik) :=
  (fun t history => niedereAussensicht label (p.sicht t (niedrigerVerlauf label history)),
    fun t history q => sichtbar (label.frage q) (p.antwort t (niedrigerVerlauf label history) q),
    fun t history e phase => sichtbar (label.endpunkt e) (p.dma t (niedrigerVerlauf label history) e phase))

/-- Selected rows are unit data. Target, ABI, physical core count, loader-visible image bytes and
    start addresses, and the total public outside interface are the environment projection. -/
def umgebungsProjektion (h : Umgebung) :=
  (E.katalog, h.ziel, h.systemAbi, h.kernzahl,
    (fun b : Bild => b.beobachtung (h.lade b)), politikProjektion E.etiketten h.politik)

def GleicheNiedrigeUmgebung (h₁ h₂ : Umgebung) : Prop :=
  umgebungsProjektion E h₁ = umgebungsProjektion E h₂

/-- The physical choices include offered cores, interrupts and deliveries at public endpoints. -/
def angebotProjektion (label : Etiketten Ort) (a : Gelegenheit) :=
  (a.core, a.interrupt, a.raised, (fun e => sichtbar (label.endpunkt e) (a.delivery e)),
    a.medium, a.crash, a.cycles)

variable [DecidableEq L]

/-- The hardware schedule is a total open-loop policy. The reactive part compares its total
    public history interface. Program dispatch and high replies do not occur in the projection. -/
def hwPolitikProjektion (h : HwLauf) :=
  ((fun t => angebotProjektion E.etiketten (h.angebot t)), politikProjektion E.etiketten h.politik)

def GleichePolitik (ρ₁ ρ₂ : Lauf E) : Prop :=
  hwPolitikProjektion E ρ₁.hw = hwPolitikProjektion E ρ₂.hw

/-- The current machine has a maximal run under each conformant schedule. Reusing physical
    opportunities and selecting the second environment's own policy constructs the comparison
    run without a premise about how a program form resolves its choices. -/
theorem vergleichslauf {h₁ h₂ : Umgebung} {ρ₁ : Lauf E} {s₂ : AussenStart}
    (run : Laeufe E h₁ ρ₁) (hardware : Hardware E.katalog h₂)
    (umgebung : GleicheNiedrigeUmgebung E h₁ h₂) (zul : E.ZulStart h₂ s₂) :
    ∃ ρ₂, Laeufe E h₂ ρ₂ ∧ ρ₂.start = s₂ ∧ GleichePolitik E ρ₁ ρ₂ := by
  let hw₂ : HwLauf := { ρ₁.hw with politik := h₂.politik }
  have kerne : h₁.kernzahl = h₂.kernzahl := congrArg (fun p => p.2.2.2.1) umgebung
  have konform : hw₂.konform E.katalog h₂ := by
    refine ⟨rfl, fun t => ?_⟩
    obtain ⟨core, interrupt, raised, delivery, medium⟩ := run.2.1.2 t
    refine ⟨fun c offer => kerne ▸ core c offer, fun c offer => kerne ▸ interrupt c offer,
      fun irq offer => ?_, delivery, medium⟩
    obtain ⟨within, supported⟩ := raised irq offer
    exact ⟨kerne ▸ within, (hardware.ziel.trans run.1.ziel.symm).symm ▸ supported⟩
  obtain ⟨ρ₂, admitted, start, schedule⟩ := lauf_mit_hw E hardware zul konform
  refine ⟨ρ₂, admitted, start, ?_⟩
  unfold GleichePolitik hwPolitikProjektion
  rw [schedule, run.2.1.1]
  exact Prod.ext rfl (congrArg (fun p => p.2.2.2.2.2) umgebung)

end Gabbro.Core.Beobachtung
