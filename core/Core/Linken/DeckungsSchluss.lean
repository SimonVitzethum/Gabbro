module

public import Core.Linken.DeckungsZustand
public import Core.Linken.GuardTransfer
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- Linker acceptance for frame-only code, reduced to the one missing step. The state-level
    coverage of `DeckungsZustand` attributes every guard use to a state of some module; the premise
    below asks that this state be reached by a maximal ideal run of that module. Given that reach,
    the part's acceptance discharges the whole's guard conjunct. -/
theorem linker_akzeptiert_aus_zustandsErreichbarkeit (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hpriv : ∀ b ∈ (verknuepfteFragmente plan).code, b.Privat)
    (hparts : ∀ m ∈ plan.module, Akzeptiert (m.fragment.einheit plan.plattform))
    (hreach : ∀ (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
        (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op),
        (kanonischeVerwendung _).bedarf ρ t op args →
        ∃ m, m ∈ plan.module ∧
        ∃ (s' : Zustand), zustandsBedarf m.fragment s' op args ∧
        ∃ (ρm : I.Lauf (m.fragment.einheit plan.plattform))
          (hm : I.Laeufe (m.fragment.einheit plan.plattform) ρm) (tm : I.Schnitt _ ρm),
          ρm.zeit.zustand tm.val = s') :
    Akzeptiert (frag.einheit plan.plattform) := by
  apply linker_akzeptiert_aus_teilLauf plan frag hlink hpriv hparts
  intro ρ hρ t op args need
  obtain ⟨m, hm, s', needm, ρm, hρm, tm, heq⟩ := hreach ρ hρ t op args need
  refine ⟨m, hm, ρm, hρm, tm, ?_⟩
  rw [bedarf_ist_zustandsBedarf]
  rw [heq]
  exact needm

/-- A state-level guard use of the linked whole already yields a module and a local state. The
    statement separates this proved part from the reach of that state by a run, which is the
    precise missing step of the run surgery. -/
theorem zustandsErreichbarkeit_aus_laufErreichbarkeit (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hcover : ∀ (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
        (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op),
        (kanonischeVerwendung _).bedarf ρ t op args →
        ∃ m, m ∈ plan.module ∧
        ∃ (ρm : I.Lauf (m.fragment.einheit plan.plattform))
          (hm : I.Laeufe (m.fragment.einheit plan.plattform) ρm) (tm : I.Schnitt _ ρm),
          (kanonischeVerwendung (m.fragment.einheit plan.plattform)).bedarf ρm tm op args) :
    ∀ (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
        (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op),
        (kanonischeVerwendung _).bedarf ρ t op args →
        ∃ m, m ∈ plan.module ∧
        ∃ (s' : Zustand), zustandsBedarf m.fragment s' op args ∧
        ∃ (ρm : I.Lauf (m.fragment.einheit plan.plattform))
          (hm : I.Laeufe (m.fragment.einheit plan.plattform) ρm) (tm : I.Schnitt _ ρm),
          ρm.zeit.zustand tm.val = s' := by
  intro ρ hρ t op args need
  obtain ⟨m, hm, ρm, hρm, tm, needm⟩ := hcover ρ hρ t op args need
  refine ⟨m, hm, ρm.zeit.zustand tm.val, ?_, ρm, hρm, tm, rfl⟩
  rw [← bedarf_ist_zustandsBedarf]
  exact needm

/-- Linker acceptance for frame-only code without partial operations: the linked unit is accepted
    directly, with no guard transfer and no run surgery. This is the unconditional case that the
    general frame-only statement contains. -/
theorem linker_akzeptiert_framefrei_ohne_guard (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hpriv : ∀ b ∈ (verknuepfteFragmente plan).code, b.Privat)
    (hguard : ∀ b ∈ (verknuepfteFragmente plan).code, ∀ frame, b.guard frame = none) :
    Akzeptiert (frag.einheit plan.plattform) := by
  obtain ⟨hok, hfrag⟩ := linke_eq_some hlink
  subst frag
  have hcompat : annahmenKompatibel plan = true := by
    simp only [bauplanOk] at hok
    rw [Bool.and_eq_true] at hok
    rw [Bool.and_eq_true] at hok
    exact hok.1.2
  have hklauseln : (verknuepfteFragmente plan).klauseln = .leer :=
    verknuepfte_klauseln_leer hcompat
  exact Fragment.akzeptiert_ohne_bedarf (verknuepfteFragmente plan) plan.plattform
    hklauseln hpriv hguard

/-- The guard uses of a sealed linked whole are attributed to a module at the level of states.
    This is proved from the seal-free concatenation alone; no property of the parts is used. -/
theorem ganzes_hat_modul_zustand (plan : Bauplan)
    (ρ : I.Lauf ((verknuepfteFragmente plan).einheit plan.plattform))
    (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op)
    (need : (kanonischeVerwendung ((verknuepfteFragmente plan).einheit plan.plattform)).bedarf
      ρ t op args) :
    ∃ m ∈ plan.module, ∃ s' : Zustand, zustandsBedarf m.fragment s' op args := by
  rw [bedarf_ist_zustandsBedarf] at need
  exact zustandsBedarf_hat_modul plan (ρ.zeit.zustand t.val) op args need

end Gabbro.Core.Linken
