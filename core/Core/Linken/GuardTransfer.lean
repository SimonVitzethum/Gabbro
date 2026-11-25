module

public import Core.Linken.Abgeschottet
public import Core.Linken.GegenbeispielVerknuepft

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- A guard-conjunct transfer reduced to its missing premise: if every guard use of a run of
    the linked whole is covered by a guard use of a run of some module, with the same operation
    and operands, then each part's acceptance discharges the whole's guard conjunct. The only
    step left is the construction of the covering part run (run surgery): from a whole run that
    executes module `m`'s code, a run of `m` that reaches the same guard operands, using the
    seal, the relocation of entries and the empty temporaries at call and entry. -/
theorem linker_akzeptiert_aus_teilLauf (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hpriv : ∀ b ∈ (verknuepfteFragmente plan).code, b.Privat)
    (hparts : ∀ m ∈ plan.module, Akzeptiert (m.fragment.einheit plan.plattform))
    (hcover : ∀ (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
      (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op),
      (kanonischeVerwendung _).bedarf ρ t op args →
      ∃ m, m ∈ plan.module ∧
      ∃ (ρm : I.Lauf (m.fragment.einheit plan.plattform))
        (hm : I.Laeufe (m.fragment.einheit plan.plattform) ρm) (tm : I.Schnitt _ ρm),
        (kanonischeVerwendung (m.fragment.einheit plan.plattform)).bedarf ρm tm op args) :
    Akzeptiert (frag.einheit plan.plattform) := by
  apply linker_akzeptiert_aus_guard_transfer plan frag hlink hparts hpriv
  intro ρ hρ t op args need
  obtain ⟨m, hm, ρm, hρm, tm, needm⟩ := hcover ρ hρ t op args need
  exact (hparts m hm).2.2.1 ρm hρm tm op args needm

end Gabbro.Core.Linken
