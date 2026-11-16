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

/-- The constant u64 local passes. The selected consumer still needs a control
    statement outside this checker's currently supported fragment. -/
theorem selected_refused_zeuge : compile text options = .error
    "unsupported invariant constructor: contract statement is outside the checked scalar/control fragment" := by
  kernel_rfl

/-- The request explicitly selects the physical consumer's driver. -/
theorem selected_entry_requested_zeuge : Profil.entryName options = "p#driver#g" := rfl

/-- A complete source request with a constant u64 local and a small result.
    The binding is checked without enumerating the u64 range. -/
def constantLocalSource : String :=
  "impl fn main() -> u32 in 0 .. 1 { let x: u64 = 3; return 0; }"

theorem constant_local_compiles_zeuge :
    (compile constantLocalSource {}).toOption.isSome = true := by
  kernel_rfl

end Gabbro.Stage0.CheckConsumerWitness
