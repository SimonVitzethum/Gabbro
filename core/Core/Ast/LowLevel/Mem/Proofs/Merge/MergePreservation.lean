module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Annahme.AussenLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine
open Gabbro.Core.Annahme
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)
open Gabbro.Core.Aussen

namespace MemInstruction

theorem genauInternal {k : Katalog} {t : Nat} {c : Kontext} {s u : MemState}
    {trace : SchrittSpur Nat UInt8} {next : MemState}
    (execute : FuehrtSchrittAus memSetup t c s u plan trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨rahmen, _, _, _, action, memory, nextEq⟩ := execute
  cases trace with
  | mk events outside =>
      cases action
      simp only [plan, List.nil_append, schreibEreignisse, List.map_nil, List.filter_nil, List.append_nil] at memory
      have unchanged : ∀ {recorded graph},
          Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
            recorded = [] ∧ graph = s.graph := by
        intro _ _ run
        cases run
        exact ⟨rfl, rfl⟩
      obtain ⟨rfl, graph⟩ := unchanged memory
      rw [graph] at nextEq
      rw [← rahmen.graph] at nextEq
      exact ⟨rfl, nextEq⟩

end MemInstruction

end Gabbro.Core.Ast.LowLevel
