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


namespace Gabbro.Stage0.Pipeline.AdapterReasonWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The adapter keeps the fallible source signature; main handles the propagated reason.
    Both the adapter's call and the explicit `?` binding contribute to the returned value. -/
def text : String :=
  "module adapter_reason_probe { reason R { Empty = 1 \"empty\" exhaustive } impl fn original(x : u8) -> u8 or R { if x == 0 { return R::Empty; } return x; } impl fn adapted(..) -> u8 or R from original; impl fn propagate(x : u8) -> u8 or R { let y = adapted(x) ?; return y; } impl fn main() -> u8 { let answer = propagate(0) else (e) { match e { Empty => { return 23; } } return 0; } return answer; } }"

/-- Lexing, parsing, profile selection and source-scope collection all succeed. -/
theorem source_present : (Frontend.source text).toOption.isSome = true := by
  decide +kernel

/-- This candidate uses the production compiler and image emitter, including shared expansion. -/
def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- The adapter and both reason-propagating functions survive into a nonempty IR image. -/
theorem image_shape :
    output.compiled.unit.fns.map (·.name) = ["original", "adapted", "propagate", "main"] ∧
    output.compiled.unit.whys.map (·.name) = ["R"] ∧
    (output.compiled.unit.fns.flatMap (·.body)).countP
      (fun | .bindElse .. => true | _ => false) = 3 ∧
    0 < output.image.code.length ∧ 16 < output.image.bytes.length := by
  decide +kernel

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- Isolate `?` from the earlier adapter refusal, retaining a live reason return and handler. -/
def propagationText : String :=
  "module reason_propagation_probe { reason R { Empty = 1 \"empty\" exhaustive } impl fn original(x : u8) -> u8 or R { if x == 0 { return R::Empty; } return x; } impl fn propagate(x : u8) -> u8 or R { let y = original(x) ?; return y; } impl fn main() -> u8 { let answer = propagate(0) else (e) { match e { Empty => { return 23; } } return 0; } return answer; } }"

/-- Keep the standalone propagation case, so adapter expansion cannot hide a missing `?` path. -/
def propagationCandidate : Except String (Emitted propagationText 256) := emit propagationText 256

theorem propagation_candidate_present : propagationCandidate.toOption.isSome = true := by
  decide +kernel

def propagationOutput : Emitted propagationText 256 :=
  propagationCandidate.toOption.get propagation_candidate_present

theorem propagation_accepted_image : emit propagationText 256 = .ok propagationOutput :=
  Gabbro.Grammatik.except_ok_get propagation_candidate_present

theorem propagation_image_shape :
    propagationOutput.compiled.unit.fns.length = 3 ∧
    0 < propagationOutput.image.code.length ∧ 16 < propagationOutput.image.bytes.length := by
  decide +kernel

theorem propagation_canonical_source : CanonicalSourceProgram propagationOutput.compiled :=
  compile_source_program propagationText propagationOutput.compiled

end Gabbro.Stage0.Pipeline.AdapterReasonWitness
