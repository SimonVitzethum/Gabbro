module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Erfuellbar
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # The MMU view is not drawn from the memory state

`Katalog.Lauf` fixes how a view translates (`Hardware.mmu`: `h.translate = uebersetze h.ziel`) but
never says where the view comes from. `Umgebung.translate` takes an arbitrary `MmuSicht`; `memProgram`
pins `quelltabellen` to empty and never instantiates the view; no definition in `core/` applies
`translate` or `uebersetze` to `MemFrame.mmuSicht` outside the table proofs. The view can therefore
diverge from the frame: the counterexample below pairs an empty frame with a view that serves an
entry. That is the Hauptbefund.

The binding itself is implemented without touching the statement: `MemFrame.mmuSicht` (installed
tables plus cached translations) is the view a core translates over, and on a reference environment
it decodes exactly as the hardware row demands. Wiring the binding into `Lauf` — requiring every
`translate` argument to equal some frame's `mmuSicht` — would change `Hardware` and `FairLaeufe`
(both pinned) and the goal statement built on them, so it is NOT done here. Recommendation: add a
named composition rule that threads the acting `MemFrame` into each `translate` call (one new
premise `sicht = (s.lokal c).mmuSicht` at every memory access of the composed machine), with a
`Spec.lean` diff and re-pinned `Hardware`/`FairLaeufe`/`uebersetze`, reviewed before merge. -/

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

/-- **Hauptbefund: the view is unconstrained.** An empty frame coexists with a view that serves a
    table entry: nothing in `Katalog.Lauf` forces `sicht.tables` to equal any frame's
    `tabellenSicht`. A stale or foreign view therefore translates successfully while the frame holds
    no such mapping. -/
theorem hauptbefund_gegenbeispiel :
    ∃ (frame : MemFrame) (sicht : MmuSicht),
      sicht.tables 0 0 = some ⟨1, [.read], 0⟩ ∧
      frame.tabellenSicht 0 0 = none := by
  refine ⟨leerFrame, fremdSicht, rfl, ?_⟩
  apply MemFrame.tabellenSicht_none
  rfl

end Gabbro.Core.Ast.LowLevel
