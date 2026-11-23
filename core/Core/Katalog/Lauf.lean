module
public import Core.Katalog.Auswahl

@[expose] public section

namespace Gabbro.Core.Katalog

/-- The public projection supplied to the outside policy. Context and request-instance identities
    belong to the composed machine's events. -/
inductive AussenEreignis where
  | frage (q : Frage)
  | antwort (q : Frage) (a : Antwort)

abbrev AussenVerlauf := List (Nat × AussenEreignis)

/-- A total policy even on histories with no corresponding program run. The same policy can be used
    for runs with different requests. The snapshot at a cut may reflect prior outside interactions. -/
structure AussenPolitik where
  sicht : Nat → AussenVerlauf → AussenSicht
  antwort : Nat → AussenVerlauf → Frage → Entscheidung
  dma : Nat → AussenVerlauf → Endpunkt → GeraetePhase → Option DmaZugriff

structure Umgebung where
  ziel : ZielDaten
  systemAbi : SystemAbi
  kernzahl : Nat
  float : GleitHardware
  lade : Bild → Ladung
  translate : MmuSicht → Nat → Nat → Nat → Speicherdienst → Except MmuFehler (Nat × Nat)
  pages : Seitenbestand → SeitenEreignis → Seitenbestand → Prop
  interrupt : Maske → Unterbrechung → Eintritt
  medium : Strecke → PersistZustand → PersistEreignis → PersistZustand → Prop
  politik : AussenPolitik

/-- The entire outside policy is governed by the selected rows. A permitted DMA operation uses only
    the currently supplied loan. For replies, the row fixes both the mandatory answers and when silence
    is allowed, for each history, opportunity, and question. -/
structure Hardware (k : Katalog) (h : Umgebung) : Prop where
  katalog : KatalogWohlgeformt k
  ziel : h.ziel = k.plattform.ziel
  abi : h.systemAbi = k.plattform.systemAbi
  kerne : 0 < h.kernzahl
  float : nativeFloat h.float
  lader : ∀ b : Bild, b.gueltig h.ziel → lader h.ziel (b.beobachtung (h.lade b))
  mmu : h.translate = uebersetze h.ziel
  pages : h.pages = SeitenSchritt h.ziel
  interrupts : h.interrupt = unterbrechungen
  persistence : ∀ r s e t, h.medium r s e t ↔ k.enthaelt .persistence ∧ persistenz r s e t
  antwort : ∀ time history q, k.enthaelt (.endpoint q.endpoint) →
    h.politik.antwort time history q = atomar k.plattform (h.politik.sicht time history) q
  dma : ∀ time history e phase access, h.politik.dma time history e phase = some access →
    k.enthaelt (.endpoint e) ∧
      ∃ d l, k.plattform.geraet e = some d ∧ dma d phase l access

/-- The exogenous opportunities at a hardware cut. Offers are recorded even if the implementation
    is unable to receive or use one. A service offer does not already name a particular question. -/
structure Gelegenheit where
  core : Option Nat
  interrupt : Nat → Bool
  raised : List (Nat × Unterbrechung)
  delivery : Endpunkt → Bool
  medium : Bool
  crash : Bool
  cycles : Nat

/-- Infinite hardware input even where the composed implementation run stops at a finite cut. -/
structure HwLauf where
  angebot : Nat → Gelegenheit
  politik : AussenPolitik

def AngebotGueltig (k : Katalog) (h : Umgebung) (g : Gelegenheit) : Prop :=
  (∀ core, g.core = some core → core < h.kernzahl) ∧
  (∀ core, g.interrupt core = true → core < h.kernzahl) ∧
  (∀ irq ∈ g.raised, irq.1 < h.kernzahl ∧ h.ziel.unterstuetzt irq.2) ∧
  (∀ e, g.delivery e = true → k.enthaelt (.endpoint e)) ∧
  ((g.medium = true ∨ g.crash = true) → k.enthaelt .persistence)

/-- Row-conformant input for arbitrary implementation runs, including unfair ones. -/
def HwLauf.konform (k : Katalog) (h : Umgebung) (run : HwLauf) : Prop :=
  run.politik = h.politik ∧ ∀ i, AngebotGueltig k h (run.angebot i)

/-- Fairness quantifies over physical cores and offered service, independently of dispatch, masking,
    query traffic, arrival consumption, or the existence of a successful implementation step. -/
structure FairLaeufe (k : Katalog) (h : Umgebung) (run : HwLauf) : Prop where
  hardware : Hardware k h
  politik : run.politik = h.politik
  gueltig : ∀ i, AngebotGueltig k h (run.angebot i)
  kerne : kerneSchreiten h.kernzahl (fun i => (run.angebot i).core)
  interrupts : ∀ c, c < h.kernzahl → ∀ cut, ∃ i, cut ≤ i ∧ (run.angebot i).interrupt c = true
  auslieferung : ∀ e, k.enthaelt (.endpoint e) → ∀ cut, ∃ i, cut ≤ i ∧ (run.angebot i).delivery e = true
  medium : k.enthaelt .persistence → ∀ cut, ∃ i, cut ≤ i ∧ (run.angebot i).medium = true
  cycles : ∀ i j, i ≤ j → (run.angebot i).cycles ≤ (run.angebot j).cycles
  zeit : ∀ cut cycles, ∃ i, cut ≤ i ∧ cycles ≤ (run.angebot i).cycles

theorem FairLaeufe.konform (fair : FairLaeufe k h run) : run.konform k h :=
  ⟨fair.politik, fair.gueltig⟩

/-- Runtime identity for an issued question. It is independent of the external handle and scope. -/
structure FrageEreignis where
  cut : Nat
  context : Nat
  questionInstance : Nat
  question : Frage
  deriving DecidableEq, Repr

/-- An arrived reply is a distinct run event with its own cut, context instance and question instance.
    Whether the context later consumes it is recorded by the composition. -/
structure AntwortEreignis where
  cut : Nat
  context : Nat
  questionInstance : Nat
  question : Frage
  reply : Antwort
  deriving Repr

/-- Whether a supported pending interrupt can be presented at a cut is independent of whether the
    implementation consumes the offer. The architectural result is computed from the current mask. -/
def HwLauf.interruptAngeboten (run : HwLauf) (h : Umgebung) (cut core : Nat)
    (irq : Unterbrechung) : Prop :=
  (run.angebot cut).interrupt core = true ∧ h.ziel.unterstuetzt irq

theorem unterbrechung_angeboten {k h run} (fair : FairLaeufe k h run) (core cut : Nat)
    (existsCore : core < h.kernzahl) (irq : Unterbrechung) (supported : h.ziel.unterstuetzt irq) :
    ∃ i, cut ≤ i ∧ run.interruptAngeboten h i core irq := by
  obtain ⟨i, after, offer⟩ := fair.interrupts core existsCore cut
  exact ⟨i, after, offer, supported⟩

def AntwortEreignis.zu (a : AntwortEreignis) (q : FrageEreignis) : Prop :=
  q.cut ≤ a.cut ∧ q.context = a.context ∧ q.questionInstance = a.questionInstance ∧ q.question = a.question

def AntwortEreignis.erlaubt (e : AntwortEreignis) (run : HwLauf) (history : AussenVerlauf) : Prop :=
  (run.angebot e.cut).delivery e.question.endpoint = true ∧
    run.politik.antwort e.cut history e.question = .antwort e.reply

/-- On a fair hardware history, a row that keeps requiring an answer offers it on a later cut.
    This conclusion is solely about the policy and the schedule. -/
theorem antwort_angeboten {k h run} (fair : FairLaeufe k h run)
    (q : Frage) (history : Nat → AussenVerlauf) (cut : Nat)
    (selected : k.enthaelt (.endpoint q.endpoint))
    (ready : ∀ i, cut ≤ i → ∃ a,
      atomar k.plattform (h.politik.sicht i (history i)) q = .antwort a) :
    ∃ i a, cut ≤ i ∧ (run.angebot i).delivery q.endpoint = true ∧
      run.politik.antwort i (history i) q = .antwort a := by
  obtain ⟨i, later, offer⟩ := fair.auslieferung q.endpoint selected cut
  obtain ⟨a, answer⟩ := ready i later
  refine ⟨i, a, later, offer, ?_⟩
  rw [fair.politik, fair.hardware.antwort i (history i) q selected, answer]

end Gabbro.Core.Katalog
