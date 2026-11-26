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

/-- A delivery attempt identifies an interrupt by the cut and position of its raise. -/
inductive InterruptSignal where
  | erhoben (kern : Nat) (irq : Unterbrechung)
  | zustellen (kern : Nat) (id : Nat × Nat) (irq : Unterbrechung)

/-- The exogenous opportunities at a hardware cut, including raised interrupts and delivery attempts. -/
structure Gelegenheit where
  core : Option Nat
  interrupt : Nat → Bool
  interrupts : List InterruptSignal
  delivery : Endpunkt → Bool
  medium : Bool
  crash : Bool
  cycles : Nat

def Gelegenheit.interruptAuswahl (g : Gelegenheit) : Option (Nat × (Nat × Nat) × Unterbrechung) :=
  g.interrupts.findSome? fun
    | .erhoben _kern _irq => none
    | .zustellen kern id irq => some (kern, id, irq)

/-- A delivery consumes the cut's single transition opportunity. Multiple raises can
    still be recorded at that cut, and a crash takes precedence over delivery. -/
def Gelegenheit.interruptGueltig (g : Gelegenheit) (h : Umgebung)
    (ursprung : (Nat × Nat) → Nat → Unterbrechung → Prop) : InterruptSignal → Prop
  | .erhoben kern irq => kern < h.kernzahl ∧ h.ziel.unterstuetzt irq
  | .zustellen kern id irq =>
    kern < h.kernzahl ∧ h.ziel.unterstuetzt irq ∧ g.interrupt kern = true ∧
      g.interruptAuswahl = some (kern, id, irq) ∧ ursprung id kern irq ∧
      g.core = none ∧ ∀ e, g.delivery e = false

/-- Infinite hardware input even where the composed implementation run stops at a finite cut. -/
structure HwLauf where
  angebot : Nat → Gelegenheit
  politik : AussenPolitik

/-- The origin is an actual raise at or before the delivery attempt. The first cut
    can be audited on its own, without consulting any future offer. -/
def InterruptSignal.ursprung (signale : Nat → List InterruptSignal) :
    Nat → (Nat × Nat) → Nat → Unterbrechung → Prop
  | 0, id, kern, irq => id.1 = 0 ∧ (signale 0)[id.2]? = some (.erhoben kern irq)
  | t + 1, id, kern, irq =>
    id.1 ≤ t + 1 ∧ (signale id.1)[id.2]? = some (.erhoben kern irq)

def HwLauf.interruptUrsprung (run : HwLauf) := InterruptSignal.ursprung (fun t => (run.angebot t).interrupts)

/-- Validate one offer against the hardware rows. Run conformance also supplies its
    history to validate references in interrupt delivery attempts. -/
def AngebotGueltig (k : Katalog) (h : Umgebung) (g : Gelegenheit)
    (ursprung : (Nat × Nat) → Nat → Unterbrechung → Prop := fun _ _ _ => True) : Prop :=
  (∀ core, g.core = some core → core < h.kernzahl) ∧
  (∀ core, g.interrupt core = true → core < h.kernzahl) ∧
  (∀ signal ∈ g.interrupts, g.interruptGueltig h ursprung signal) ∧
  (∀ e, g.delivery e = true → k.enthaelt (.endpoint e)) ∧
  ((g.medium = true ∨ g.crash = true) → k.enthaelt .persistence)

theorem AngebotGueltig.interrupt_reserviert {k h g ursprung kern id irq}
    (gueltig : AngebotGueltig k h g ursprung) (wahl : g.interruptAuswahl = some (kern, id, irq)) :
    ursprung id kern irq ∧ g.core = none ∧ ∀ e, g.delivery e = false := by
  obtain ⟨signal, mem, gleich⟩ := List.exists_of_findSome?_eq_some wahl
  cases signal with
  | erhoben _ _ => cases gleich
  | zustellen k' id' irq' =>
    change some (k', id', irq') = some (kern, id, irq) at gleich
    cases gleich
    exact (gueltig.2.2.1 _ mem).2.2.2.2

/-- Row-conformant input for arbitrary implementation runs, including unfair ones. -/
def HwLauf.konform (k : Katalog) (h : Umgebung) (run : HwLauf) : Prop :=
  run.politik = h.politik ∧ ∀ i, AngebotGueltig k h (run.angebot i) (run.interruptUrsprung i)

/-- Fairness quantifies over physical cores and offered service, independently of dispatch, masking,
    query traffic, arrival consumption, or the existence of a successful implementation step. -/
structure FairLaeufe (k : Katalog) (h : Umgebung) (run : HwLauf) : Prop where
  hardware : Hardware k h
  politik : run.politik = h.politik
  gueltig : ∀ i, AngebotGueltig k h (run.angebot i) (run.interruptUrsprung i)
  kerne : kerneSchreiten h.kernzahl (fun i => (run.angebot i).core)
  interrupts : ∀ c, c < h.kernzahl → ∀ cut, ∃ i, cut ≤ i ∧ (run.angebot i).interrupt c = true
  auslieferung : ∀ e, k.enthaelt (.endpoint e) → ∀ cut, ∃ i, cut ≤ i ∧ (run.angebot i).delivery e = true
  medium : k.enthaelt .persistence → ∀ cut, ∃ i, cut ≤ i ∧ (run.angebot i).medium = true
  cycles : ∀ i j, i ≤ j → (run.angebot i).cycles ≤ (run.angebot j).cycles
  zeit : ∀ cut cycles, ∃ i, cut ≤ i ∧ cycles ≤ (run.angebot i).cycles

theorem FairLaeufe.konform (fair : FairLaeufe k h run) : run.konform k h :=
  ⟨fair.politik, fair.gueltig⟩

/-- **Selection fairness: the named hardware row for raised interrupts.** Every raised
    interrupt on a supported line of a live core is eventually selected with its origin
    (the raise cut and position it comes from). This row is bound to the catalogue
    environment `h`, never a free parameter, and it lives only in the progress leg:
    `FairLaeufe` and `Laeufe` never assume it. -/
def AuswahlFair (h : Umgebung) (run : HwLauf) : Prop :=
  ∀ (t i kern : Nat) (irq : Unterbrechung),
    (run.angebot t).interrupts[i]? = some (.erhoben kern irq) →
    kern < h.kernzahl →
    h.ziel.unterstuetzt irq →
    ∃ (t' : Nat) (id : Nat × Nat),
      t ≤ t' ∧ (run.angebot t').interruptAuswahl = some (kern, id, irq) ∧
        run.interruptUrsprung t' id kern irq

/-- **Counter liveness: the row behind the counter bound.** When the cycle counter of an
    offer reaches the bound register of the platform row, the hardware raises the row's
    trap line on that core at a later cut. -/
def ZaehlerLebendigAussage (p : Plattform) (h : Umgebung) (run : HwLauf) : Prop :=
  ∀ (hziel : h.ziel = p.ziel) (t kern : Nat),
    kern < h.kernzahl →
    (run.angebot t).cycles = p.zaehlerZeile.schranke →
    ∃ (t' i : Nat),
      t ≤ t' ∧ (run.angebot t').interrupts[i]? = some (.erhoben kern p.zaehlerZeile.trap)

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
