module

public import Stage0.Compiler
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Zeugen
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Stage0.CheckConsumerWitness

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A real selected Stage-0 source: check, measured local, floor and ordinary
    gate. The image configuration explicitly selects its retiring consumer. -/
def text : String :=
  "impl fn main() { return; } impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { let x: u64 = 3; return x >= 2; } floor x >= 2 }"

def options : Profil.Options := { checkConsumer := some retiringSelection }

theorem selected_compiles : (compile text options).toOption.isSome = true := by
  kernel_rfl

def compiled : Compiled text options :=
  (compile text options).toOption.get selected_compiles

/-- Acceptance is the actual compiler's full checker result. -/
theorem selected_accepted :
    OldSource.accepts compiled.unit compiled.program compiled.main = .ok true := compiled.accepted

/-- Entry selection is retained in the source-to-program certificate. -/
theorem selected_entry :
    fnIdx compiled.unit.fns "p#driver#g" = .ok compiled.main := compiled.entry

/-- The generated entry's returning resource inventory is empty. -/
theorem selected_retired :
    (Gabbro.Grammatik.vertragVon (declOf compiled.unit) compiled.main).ende = [] := by
  kernel_rfl

/-- The same canonical-source theorem used by every emitted image includes
    the exact selected source tree and selected elaboration. -/
theorem selected_canonical : CanonicalSourceProgram compiled :=
  compile_source_program text compiled

end Gabbro.Stage0.CheckConsumerWitness
