module
public import Stage0.IRBild
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


namespace Gabbro.Stage0.Pipeline.TaggedDispatchWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Both closed cases have distinct payload types and implementations. Main dispatches
    both values and makes its numeric answer depend on both Boolean results. -/
def text : String :=
  "module tagged_dispatch_probe { spec Select[T] { fn choose(value : T) -> bool effects {} costs <= 8 ops; } impl Select[u8] { fn choose(value : u8) -> bool effects {} costs <= 3 ops { return value == 7; } } impl Select[bool] { fn choose(value : bool) -> bool effects {} costs <= 3 ops { return value; } } tagged type Choice = { Number(u8), Truth(bool) } by Select; impl fn main() -> u8 { let left : Choice = Number(7); let a = Select::choose(left); let right : Choice = Truth(false); let b = Select::choose(right); if a && !b { return 23; } return 0; } }"

/-- The actual source frontend retains the parsed closed-dispatch declarations. -/
theorem source_present : (Frontend.source text).toOption.isSome = true := by
  decide +kernel

/-- The candidate includes spec resolution, both implementation bodies and the generated dispatcher. -/
def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- Both case implementations and the dispatcher are emitted with the caller; the sum is retained. -/
theorem image_shape :
    output.compiled.unit.fns.length = 4 ∧
    output.compiled.unit.sums.map (·.name) = ["Choice"] ∧
    output.compiled.unit.fns.any (fun fn => fn.name ==
      Gabbro.Grammatik.Parser.taggedDispatchName "Choice" "Select" "choose") = true ∧
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .bindCall _ callee _ => callee ==
        Gabbro.Grammatik.Parser.taggedDispatchName "Choice" "Select" "choose" | _ => false) = 2 ∧
    0 < output.image.code.length ∧ 16 < output.image.bytes.length := by
  decide +kernel

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

end Gabbro.Stage0.Pipeline.TaggedDispatchWitness
