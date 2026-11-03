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


namespace Gabbro.Stage0.Pipeline.RangeFoldsWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A range add with a nonzero lower bound and a filter. -/
def boundsText : String :=
  "module range_probe { const XS : [u8; 4] = [3, 5, 7, 9]; " ++
  "fn sum_range(xs: [u8; 4]) -> u16 effects { pure } " ++
  "{ return add i in 2 ..< 4 where xs[i] > 6 : xs[i]; } " ++
  "impl fn main() -> u8 effects { pure } { " ++
  "let s = sum_range(XS); if s == 16 { return 7; } return 0; } }"

/-- A range min with an else value. -/
def minText : String :=
  "module range_min_probe { const YS : [u8; 4] = [3, 5, 7, 9]; " ++
  "fn min_range(xs: [u8; 4]) -> u8 effects { pure } " ++
  "{ return min i in 0 ..< 4 : xs[i] else 255; } " ++
  "impl fn main() -> u8 effects { pure } { " ++
  "let m = min_range(YS); if m == 3 { return 5; } return 0; } }"

/-- Nested range adds over the same array. -/
def nestedText : String :=
  "module range_nested_probe { const ZS : [u8; 2] = [3, 5]; " ++
  "fn total2(xs: [u8; 2]) -> u16 effects { pure } " ++
  "{ return add i in 0 ..< 2 : xs[i] + add j in 0 ..< 2 : xs[j]; } " ++
  "impl fn main() -> u8 effects { pure } { " ++
  "let t = total2(ZS); if t == 24 { return 1; } return 0; } }"

def boundsCandidate : Except String (Emitted boundsText 256) := emit boundsText 256

theorem bounds_present : boundsCandidate.toOption.isSome = true := by
  decide +kernel

def boundsOutput : Emitted boundsText 256 := boundsCandidate.toOption.get bounds_present

theorem bounds_accepted : emit boundsText 256 = .ok boundsOutput :=
  Gabbro.Grammatik.except_ok_get bounds_present

theorem bounds_canonical : CanonicalSourceProgram boundsOutput.compiled :=
  compile_source_program boundsText boundsOutput.compiled

theorem bounds_correct [Runner.IR.Kern] [Senke.CloneOK] : boundsOutput.Correct :=
  boundsOutput.correct

def minCandidate : Except String (Emitted minText 256) := emit minText 256

theorem min_present : minCandidate.toOption.isSome = true := by
  decide +kernel

def minOutput : Emitted minText 256 := minCandidate.toOption.get min_present

theorem min_accepted : emit minText 256 = .ok minOutput :=
  Gabbro.Grammatik.except_ok_get min_present

theorem min_canonical : CanonicalSourceProgram minOutput.compiled :=
  compile_source_program minText minOutput.compiled

theorem min_correct [Runner.IR.Kern] [Senke.CloneOK] : minOutput.Correct :=
  minOutput.correct

def nestedCandidate : Except String (Emitted nestedText 256) := emit nestedText 256

theorem nested_present : nestedCandidate.toOption.isSome = true := by
  decide +kernel

def nestedOutput : Emitted nestedText 256 := nestedCandidate.toOption.get nested_present

theorem nested_accepted : emit nestedText 256 = .ok nestedOutput :=
  Gabbro.Grammatik.except_ok_get nested_present

theorem nested_canonical : CanonicalSourceProgram nestedOutput.compiled :=
  compile_source_program nestedText nestedOutput.compiled

theorem nested_correct [Runner.IR.Kern] [Senke.CloneOK] : nestedOutput.Correct :=
  nestedOutput.correct

end Gabbro.Stage0.Pipeline.RangeFoldsWitness
