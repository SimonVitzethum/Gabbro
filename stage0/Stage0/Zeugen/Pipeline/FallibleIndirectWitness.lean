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


namespace Gabbro.Stage0.Pipeline.FallibleIndirectWitness
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The same local pointer is called with a success input and a reason input. The second
    handler returns the first indirect result, so neither call is an unused fixture. -/
def text : String :=
  "module fallible_indirect_probe { reason R { Empty = 1 \"empty\" exhaustive } impl fn target(x : u8) -> u8 or R { if x == 0 { return R::Empty; } return x; } impl fn main() -> u8 { let pointer = &target; let first = pointer(7) else (e) { match e { Empty => { return 9; } } return 0; } let second = pointer(0) else (e) { match e { Empty => { return first; } } return 0; } return second; } }"

def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- The source exporter retains both fallible indirect binds in the very unit whose
    canonical lowered program was passed to the successful IR image emitter. -/
theorem image_shape :
    output.compiled.unit.fns.map (·.name) = ["target", "main"] ∧
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .bindCallIndElse .. => true | _ => false) = 2 ∧
    output.compiled.unit.whys.length = 1 ∧
    0 < output.image.code.length ∧ 16 < output.image.bytes.length := by
  decide +kernel

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

/-- The value-discarding statement variant needs the same explicit reason handler.
    It is kept separate so its parser refusal cannot mask the accepted binding form. -/
def statementText : String :=
  "module fallible_indirect_statement_probe { reason R { Empty = 1 \"empty\" exhaustive } impl fn target(x : u8) -> u8 or R { if x == 0 { return R::Empty; } return x; } impl fn main() -> u8 { let pointer = &target; pointer(0) else (e) { match e { Empty => { return 23; } } return 0; } return 7; } }"

/-- `callIndElse` exists in G and the IR lowerer, but has no statement-else parser path. -/
theorem statement_parser_refused :
    ((Gabbro.Grammatik.Parser.lex statementText).mapError (fun _ => "lex")).bind
      Gabbro.Grammatik.Parser.parseTopTief = .error "wanted ;" := by
  decide +kernel

theorem statement_image_refused : emit statementText 256 = .error "wanted ;" := by
  decide +kernel

end Gabbro.Stage0.Pipeline.FallibleIndirectWitness
