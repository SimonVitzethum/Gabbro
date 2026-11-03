module

public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.String.Basic
import all Init.Data.String.Defs

/-! Kernel witness of the consuming-header gate. It runs the lexer and parser in the
    kernel and therefore lives with the heavy probe modules (final round build only). -/

@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

theorem consuming_bound_zeuge :
    bodyMetadata 3 (.each "k" none "slots" (.variable "T") "consuming"
      "decreases 1 touches consumes T.slots" none (.block [] none)) = false ∧
    bodyMetadata 3 (.each "k" none "slots" (.variable "T") "consuming"
      "touches consumes T.slots" none (.block [] none)) = true := by
  exact ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.ExportMetadata
