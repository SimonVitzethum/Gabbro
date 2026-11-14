module
public import Stage0.IRBild
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Repr
import all Init.Data.ToString.Basic
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


namespace Gabbro.Stage0.Pipeline.NumberWildcardWitness
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Distinct numeric arms and the final wildcard use the existing conditional path. -/
def text : String :=
  "module number_wildcard { impl fn choose(n : u8) -> u8 { match n { 0 => { return 11; } 1 => { return 13; } _ => { return 17; } } } impl fn main() -> u8 { let result = choose(2); return result; } }"

def candidate : Except String (Emitted text 256) := emit text 256

#eval candidate.map (fun _ => ())

theorem candidate_present : candidate.toOption.isSome = true := by
  kernel_rfl

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- The poison differs only by the missing exhaustive fallback. -/
def missingFallback : String :=
  "module number_wildcard { impl fn choose(n : u8) -> u8 { match n { 0 => { return 11; } 1 => { return 13; } } } impl fn main() -> u8 { let result = choose(2); return result; } }"

theorem missing_fallback_refused_zeuge :
    (emit missingFallback 256).toOption.isSome = false := by
  kernel_rfl

/-- Duplicate numeric patterns cannot silently select the first arm. -/
def duplicatePattern : String :=
  "module number_wildcard { impl fn choose(n : u8) -> u8 { match n { 0 => { return 11; } 0 => { return 13; } _ => { return 17; } } } impl fn main() -> u8 { let result = choose(2); return result; } }"

theorem duplicate_pattern_refused_zeuge :
    (emit duplicatePattern 256).toOption.isSome = false := by
  kernel_rfl

end Gabbro.Stage0.Pipeline.NumberWildcardWitness
