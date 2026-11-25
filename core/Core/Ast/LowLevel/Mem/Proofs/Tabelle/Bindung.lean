module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Erfuellbar
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # The MMU view is bound to the memory state

Entschiedene Verschärfung der Zielaussage (owner, 2026-11-24): jede Übersetzung der
zusammengesetzten Maschine ist an die MMU-Sicht des Speicherzustands gebunden,
`sicht = MemFrame.mmuSicht` des jeweiligen Kontexts. `Katalog.Lauf` fixiert nur, WIE eine
Sicht übersetzt (`Hardware.mmu`: `h.translate = uebersetze h.ziel`); die Bindung sagt, WOHER
die Sicht kommt: jede `translate`-Anfrage der Maschine läuft über die Sicht des handelnden
`MemFrame` (installierte Tabellen via `MemFrame.tabellenSicht` plus gecachte Übersetzungen
via `TranslationCache.sicht`). Die kleinste Änderung, die das erzwingt, ist die benannte
Kompositionsregel unten: `MmuGebunden` (`sicht = frame.mmuSicht`) als neue Prämisse an jedem
Speicherzugriff, getragen von `GebundeneUebersetzung`, die den handelnden Frame einfädelt.
Auf einer hardware-konformen Umgebung dekodiert das exakt wie die Katalogzeile verlangt
(`translate_mmuSicht`, `gebundeneUebersetzung_eq`).

Darunter ist der alte Befund als unzulässig bewiesen (`hauptbefund_gebunden_unmoeglich`):
ein leeres Frame koexistiert NICHT gebunden mit einer Sicht, die einen Eintrag bedient —
nichts in `Katalog.Lauf` erzwang bisher `sicht.tables = frame.tabellenSicht`. Die gebundene
Hardware hat weiterhin zulässige Läufe (`gebundene_plattform_erfuellbar`, via
`tabelle_nichtvakant` mit echter erreichbarer `mmuSicht`-Übersetzung). -/

/-- On a hardware-conformant environment, translating over a frame's view is the catalogue decode
    of that view. This is the binding point: use `(frame.mmuSicht)` wherever `translate` is called
    with the acting frame. -/
theorem translate_mmuSicht {k : Katalog} {h : Katalog.Umgebung} (hw : Hardware k h)
    (frame : MemFrame) (core space addr : Nat) (right : Speicherdienst) :
    h.translate frame.mmuSicht core space addr right =
      uebersetze h.ziel frame.mmuSicht core space addr right := by
  rw [hw.mmu]

private def leerFrame : MemFrame := {}

private def fremdSicht : MmuSicht :=
  { tables := fun _ _ => some ⟨1, [.read], 0⟩, tlb := fun _ _ _ => none }

/-- A view is bound to a frame when it IS the frame's MMU view: installed tables plus cached
    translations of exactly that frame. This is the one new premise at every memory access of the
    composed machine (`sicht = (s.lokal c).mmuSicht`). -/
def MmuGebunden (frame : MemFrame) (sicht : MmuSicht) : Prop :=
  sicht = frame.mmuSicht

/-- A bound view reads its tables from the frame. -/
theorem MmuGebunden.tabellen {frame : MemFrame} {sicht : MmuSicht}
    (h : MmuGebunden frame sicht) (space page : Nat) :
    sicht.tables space page = frame.tabellenSicht space page := by
  unfold MmuGebunden at h
  rw [h]
  rfl

/-- The bound translation step of the composed machine: thread the acting frame into each
    `translate` call. Every memory access translates over `(s.lokal c).mmuSicht`. -/
def GebundeneUebersetzung (h : Katalog.Umgebung) (frame : MemFrame)
    (core space addr : Nat) (right : Speicherdienst) : Except MmuFehler (Nat × Nat) :=
  h.translate frame.mmuSicht core space addr right

/-- The bound step decodes exactly as the catalogue row demands. -/
theorem gebundeneUebersetzung_eq {k : Katalog} {h : Katalog.Umgebung} (hw : Hardware k h)
    (frame : MemFrame) (core space addr : Nat) (right : Speicherdienst) :
    GebundeneUebersetzung h frame core space addr right =
      uebersetze h.ziel frame.mmuSicht core space addr right := by
  unfold GebundeneUebersetzung
  exact translate_mmuSicht hw frame core space addr right

/-- **Bound hardware assumption.** The catalogue row fixes HOW a view translates
    (`Hardware.mmu`); the binding fixes WHERE the view comes from: every translation of the
    composed machine runs over the MMU view of the acting memory state,
    `(s.lokal c).mmuSicht` — installed tables plus cached translations of exactly that frame.
    The statement takes no free `MmuSicht`: the view is a parameter read off the state.
    It lives here, above the catalogue, because `Katalog` cannot import `MemFrame`
    (`Mem.State` sits above `Maschine`, which sits above `Katalog`); moving the frame down
    would make the rows unit-specific instead of hardware-generic. -/
def HardwareGebunden (k : Katalog) (h : Katalog.Umgebung) (s : MemState) : Prop :=
  ∀ (c : Kontext) (core space addr : Nat) (right : Speicherdienst),
    h.translate (s.lokal c).mmuSicht core space addr right =
      uebersetze h.ziel (s.lokal c).mmuSicht core space addr right

/-- Every catalogue-conformant environment satisfies the bound hardware assumption on every
    memory state: the bound view decodes exactly as the row demands. -/
theorem hardware_gebunden {k : Katalog} {h : Katalog.Umgebung} (hw : Hardware k h)
    (s : MemState) : HardwareGebunden k h s := by
  intro c core space addr right
  rw [hw.mmu]

/-- **Bound hardware exists for a nontrivial table.** The reference environment is
    catalogue-conformant, hence bound on the reachable mapped-and-cached state, and the bound
    translation over the acting frame succeeds. -/
theorem hardwareGebunden_erfuellbar :
    ∃ (h : Katalog.Umgebung) (s : MemState),
      Hardware Plattform.x86_64.katalog h ∧ HardwareGebunden Plattform.x86_64.katalog h s ∧
        h.translate (s.lokal entryContext).mmuSicht 0 0 0 .read = .ok (4096, 0) := by
  let h : Katalog.Umgebung :=
    Umgebung.referenz Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)
  have hw : Hardware Plattform.x86_64.katalog h :=
    Umgebung.referenz_hardware _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)
  obtain ⟨E, start, code, s, _, _, _, _, _, _, _, _, hok⟩ := tabelle_nichtvakant
  have bound := hardware_gebunden hw s entryContext 0 0 0 .read
  have hziel : h.ziel = Plattform.x86_64.katalog.plattform.ziel := rfl
  refine ⟨h, s, hw, hardware_gebunden hw s, ?_⟩
  rw [bound, hziel]
  exact hok

/-- The old foreign view is not bound to the empty frame. -/
private theorem leer_nicht_gebunden : ¬ MmuGebunden leerFrame fremdSicht := by
  intro h
  have heq := MmuGebunden.tabellen h 0 0
  have hleer : leerFrame.tabellenSicht 0 0 = none := by
    apply MemFrame.tabellenSicht_none
    rfl
  have hfremd : fremdSicht.tables 0 0 = some ⟨1, [.read], 0⟩ := rfl
  rw [hfremd, hleer] at heq
  cases heq

/-- **The Hauptbefund is inadmissible under binding.** No bound pair diverges: a bound view that
    serves a table entry forces the frame to hold that entry. -/
theorem hauptbefund_gebunden_unmoeglich :
    ¬ ∃ (frame : MemFrame) (sicht : MmuSicht),
      MmuGebunden frame sicht ∧
      sicht.tables 0 0 = some ⟨1, [.read], 0⟩ ∧
      frame.tabellenSicht 0 0 = none := by
  intro h
  obtain ⟨frame, sicht, hbound, htab, hnone⟩ := h
  have heq := MmuGebunden.tabellen hbound 0 0
  rw [htab, hnone] at heq
  cases heq

/-- **The bound hardware still translates.** A reachable run maps a page and translates over the
    full bound view (`tabelle_nichtvakant`); bound runs exist. -/
theorem gebundene_plattform_erfuellbar :
    ∃ (frame : MemFrame) (sicht : MmuSicht),
      MmuGebunden frame sicht ∧
      uebersetze Plattform.x86_64.katalog.plattform.ziel sicht 0 0 0 .read = .ok (4096, 0) := by
  obtain ⟨E, start, code, s, _, _, _, _, _, _, _, _, hok⟩ := tabelle_nichtvakant
  exact ⟨s.lokal entryContext, (s.lokal entryContext).mmuSicht, rfl, hok⟩

/-- **Bound hardware keeps admissible runs.** The reference environment and its fair run satisfy
    `Hardware`/`FairLaeufe`, and the bound step on the reachable frame succeeds: the sharpening is
    satisfiable (`Katalog.plattform_erfuellbar` still holds, now with a bound translation). -/
theorem gebundene_hardware_erfuellbar :
    ∃ (h : Katalog.Umgebung) (run : HwLauf) (frame : MemFrame),
      Hardware Plattform.x86_64.katalog h ∧ FairLaeufe Plattform.x86_64.katalog h run ∧
      GebundeneUebersetzung h frame 0 0 0 .read = .ok (4096, 0) := by
  let h : Katalog.Umgebung :=
    Umgebung.referenz Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)
  let run : HwLauf :=
    Umgebung.referenzLauf Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)
  have hw : Hardware Plattform.x86_64.katalog h :=
    Umgebung.referenz_hardware _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)
  have fair : FairLaeufe Plattform.x86_64.katalog h run :=
    Umgebung.referenz_fair _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)
  obtain ⟨E, start, code, s, _, _, _, _, _, _, _, _, hok⟩ := tabelle_nichtvakant
  have hbound : GebundeneUebersetzung h (s.lokal entryContext) 0 0 0 .read =
      uebersetze h.ziel (s.lokal entryContext).mmuSicht 0 0 0 .read :=
    gebundeneUebersetzung_eq hw (s.lokal entryContext) 0 0 0 .read
  have hziel : h.ziel = Plattform.x86_64.katalog.plattform.ziel := rfl
  rw [hziel] at hbound
  refine ⟨h, run, s.lokal entryContext, hw, fair, ?_⟩
  rw [hbound]
  exact hok

end Gabbro.Core.Ast.LowLevel
