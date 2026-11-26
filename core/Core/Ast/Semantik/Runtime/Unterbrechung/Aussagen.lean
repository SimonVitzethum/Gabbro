/-
  File:      core/Core/Ast/Semantik/Runtime/Unterbrechung/Aussagen.lean
  Subject:   INTERRUPT CLASSES AND DEBUG (MK-20): the pinned statements. A Gabbro program controls
             interrupts with four frame-only instructions of four new effect classes (MK-20):
             `maskiere` masks or unmasks a vector, `prioritaet` sets the priority threshold,
             `sendeUnterbrechung` raises a vector on a core, `leiteLeitung` routes a line to a
             core with a priority. Their steps advance the acting frame only; the per-core state
             (`KernZustand.maske/untergrenze`), the pending send and the routing are applied by the
             machine duties below, never mid-step. Debug registers and performance counters are
             hardware rows whose hits are offered interrupts; `backtrace` reads `Rahmen.fortsetzungen`.
             The machine side exists: `NimmtUnterbrechung`, `KehrtZurueck`, `Katalog.Unterbrechung`,
             `InterruptSignal`, `unterbrechungErhalten` (proved in `SchrankenBeweise/Leicht`).
             All new statements sit under the single pinned root `UnterbrechungAussagen`; each carries
             `_erfuellbar` (the model represents the scenario) and `_nichtTrivial` (the model
             represents the error too — only the checker excludes it), proved in `Beweise` and
             `BeweiseFair`. The two fairness duties (`SendeLiefertAussage` over the named row
             `AuswahlFair`, `ZaehlerUmlaufAussage` over the counter row `ZaehlerZeile` with
             `ZaehlerLebendigAussage`) are proved in `BeweiseFair`; their decomposition into
             independent proof units is in the designer's report.
-/
module

public import Core.Maschine.Unterbrechung
public import Core.Katalog.Lauf
public import Core.Katalog.Erfuellbar
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Beobachtung.Fluss.Beschriftung.Einheit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung

/-- **Masking acts at the boundary, never mid-step** (kernel statement `MaskeSim`, proved as
    `maskeSim`). An interrupt-control step of `maskiere` or `prioritaet` leaves the delivery
    decision at its cut unchanged: a pending offer that is enabled stays enabled, with the same
    handler, because the step touches only the acting frame. The per-core mask therefore takes
    effect at the earliest at the next delivery decision. -/
def MaskeSimAussage : Prop :=
  ∀ (b : Befehl) (c : Kontext) (s u : Zustand) (w : PUnit.{1}) (plans : List Plan),
    (b.klasse = .maskiere ∨ b.klasse = .prioritaet) →
    b.ideal c s w plans u →
    ∀ (run : HwLauf) (t : Nat) (k : Kern) (id : Nat × Nat) (irq : Unterbrechung)
      (d : Kontext) (nmi : Bool),
      UnterbrechungAusstehend s run t k id irq →
      NimmtUnterbrechung (s.kerne k) k (Nat.pair id.1 id.2) irq d nmi →
      s.status d = .ruht →
      UnterbrechungAusstehend u run t k id irq ∧
        NimmtUnterbrechung (u.kerne k) k (Nat.pair id.1 id.2) irq d nmi ∧ u.status d = .ruht

/-- **The priority threshold filters delivery** (proved as `prioritaetFilter`). A delivery names a
    vector whose priority reaches the core threshold, on an unmasked line, while no NMI runs:
    this is the row `unterbrechungen` read at the core's architectural mask state. -/
def PrioritaetFilterAussage : Prop :=
  ∀ (m : Maske) (vektor p : Nat), p < m.minimum →
    unterbrechungen m (.maskierbar vektor p) = .ausstehend

/-- **A sent interrupt is selected for delivery** (proved as `sendeLiefert`, packet of
    `Befehl.sendeUnterbrechung`). A raised vector on a selection-fair hardware history is
    eventually selected with its origin: the conclusion is the named platform row `AuswahlFair`
    at the raise cut. Without the row the statement is false: a conformant run may starve a
    raised interrupt forever (`sendeLiefert_nichtTrivial`). -/
def SendeLiefertAussage : Prop :=
  ∀ (h : Katalog.Umgebung) (run : HwLauf) (t vektor kern : Nat) (i : Nat),
    AuswahlFair h run →
    (run.angebot t).interrupts[i]? = some (.erhoben kern (.maskierbar vektor 0)) →
    kern < h.kernzahl →
    h.ziel.unterstuetzt (.maskierbar vektor 0) →
    ∃ (t' : Nat) (id : Nat × Nat),
      t ≤ t' ∧ (run.angebot t').interruptAuswahl = some (kern, id, (.maskierbar vektor 0)) ∧
        run.interruptUrsprung t' id kern (.maskierbar vektor 0)

/-- **A routed line enters its handler when enabled** (proved as `leiteWirkt`). A selection that
    names a line, a core and a priority, with a pending offer on an enabled core state whose
    handler rests, enters exactly that handler: the successor runs it and records the offer. -/
def LeiteWirktAussage : Prop :=
  ∀ (s : Zustand) (run : HwLauf) (t : Nat) (k : Kern) (id : Nat × Nat)
    (leitung prioritaet : Nat) (d : Kontext) (nmi : Bool),
    (run.angebot t).interruptAuswahl = some (k, id, (.maskierbar leitung prioritaet)) →
    UnterbrechungAusstehend s run t k id (.maskierbar leitung prioritaet) →
    NimmtUnterbrechung (s.kerne k) k (Nat.pair id.1 id.2) (.maskierbar leitung prioritaet) d nmi →
    s.status d = .ruht →
    ∃ s' : Zustand, s' = Zustandseintritt s k id d nmi ∧ s'.status d = .laeuft ∧
      (s'.kerne k).laeuft = some d

/-- **A debug or counter hit is an offered interrupt** (proved as `debugTreffer`). Debug registers
    and performance counters are hardware rows: their hits are raised interrupts, and every
    supported line can be raised and selected on a conformant history. -/
def DebugTrefferAussage : Prop :=
  ∀ (k : Katalog) (h : Katalog.Umgebung) (irq : Unterbrechung) (kern : Nat),
    kern < h.kernzahl → h.ziel.unterstuetzt irq →
    ∃ hw : HwLauf, hw.konform k h ∧
      (hw.angebot 0).interrupts[0]? = some (.erhoben kern irq) ∧
      (hw.angebot 1).interruptAuswahl = some (kern, (0, 0), irq)

/-- **A counter that reaches its bound raises its trap line** (proved as `zaehlerUmlauf`,
    no packet: debug-side duty). When the cycle counter of an offer reaches the bound register
    of the platform's counter row, the row's trap line — a supported line on every platform —
    is raised on that core at a later cut, under the row's liveness (`ZaehlerLebendigAussage`).
    A history may let the counter pass without any raise (`zaehlerUmlauf_nichtTrivial`). -/
def ZaehlerUmlaufAussage : Prop :=
  ∀ (p : Plattform) (h : Katalog.Umgebung) (run : HwLauf) (t kern : Nat),
    ZaehlerLebendigAussage p h run →
    h.ziel = p.ziel →
    kern < h.kernzahl →
    (run.angebot t).cycles = p.zaehlerZeile.schranke →
    ∃ (t' : Nat) (irq : Unterbrechung), t ≤ t' ∧ h.ziel.unterstuetzt irq ∧
      ∃ (i : Nat), (run.angebot t').interrupts[i]? = some (.erhoben kern irq)

/-- A backtrace is the continuation stack of the frame. -/
def Rahmen.rueckblick (r : Rahmen) : List Fortsetzung := r.fortsetzungen

/-- **`backtrace` reads the continuation stack** (proved as `rueckblickWaechst`). A call pushes
    exactly one continuation onto the backtrace, or halts: the saved frames are the generated
    frame descriptors the backtrace walks. -/
def RueckblickAussage : Prop :=
  ∀ (r : Rahmen) (name : Identifier) (args : List (Ty .value)) (bind : Option (Ty .value)),
    (r.ruf name args bind).rueckblick.length = r.rueckblick.length + 1 ∨
      (r.ruf name args bind).stopp.isSome = true

/-- The label rule of `maskiere`: only the program counter moves, so the fall-through labels
    keep the frame at least as secret (proved as `maskeFluss`). -/
def MaskeFlussAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (vektor : Nat) (aus : Bool),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.maskiere vektor aus).SichtErhaltendBei β pc

/-- The label rule of `prioritaet` (proved as `prioritaetFluss`). -/
def PrioritaetFlussAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (grenze : Nat),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.prioritaet grenze).SichtErhaltendBei β pc

/-- The label rule of `sendeUnterbrechung` (proved as `sendeFluss`). -/
def SendeFlussAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (vektor kern : Nat),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.sendeUnterbrechung vektor kern).SichtErhaltendBei β pc

/-- The label rule of `leiteLeitung` (proved as `leiteFluss`). -/
def LeiteFlussAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (leitung kern prioritaet : Nat),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.leiteLeitung leitung kern prioritaet).SichtErhaltendBei β pc

/-- **All MK-20 statements under one pinned root.** The four packet statements of the registry
    entries of the new instructions come first; the two open duties have no proof yet. -/
def UnterbrechungAussagen : Prop :=
  MaskeSimAussage ∧ PrioritaetFilterAussage ∧ SendeLiefertAussage ∧ LeiteWirktAussage ∧
    DebugTrefferAussage ∧ ZaehlerUmlaufAussage ∧ RueckblickAussage ∧ MaskeFlussAussage ∧
    PrioritaetFlussAussage ∧ SendeFlussAussage ∧ LeiteFlussAussage

end Gabbro.Core.Ast.Semantik
