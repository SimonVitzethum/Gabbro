module
public import Stage0.SourceWitness
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

namespace Gabbro.Stage0.OptionalAxiomWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Uebersetze UebersetzeAllg UebersetzeAllg2
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A value-returning foreign call using the optional binding spelling. -/
def text : String :=
  "module optional_probe { axiom ax() -> u8 effects { pure } unfalsifiable \"probe\"; impl fn main() -> u8 { let r? = ax(); return 23; } }"

def parsed := (lexL text.toList).bind parseTopTief

theorem parsed_present : parsed.toOption.isSome = true := by decide +kernel

def unitCandidate := elabU (pre108 (parsed.toOption.get parsed_present))
theorem unit_present : unitCandidate.toOption.isSome = true := by decide +kernel
def unit := unitCandidate.toOption.get unit_present

theorem caller_present : 0 < unit.fns.length := by decide +kernel

def blockCandidate :=
  lowSeqL (l := false) unit ⟨0, caller_present⟩ [] (fnAt unit ⟨0, caller_present⟩)
    20 (resOf unit ⟨0, caller_present⟩) (some ⟨rfl⟩) [.bindOptBeg "r" "ax" []]

/-- The actual sequence lowerer constructs the canonical optional axiom block. -/
theorem optional_constructor :
    (match blockCandidate with
     | .ok (.bindAxiomOpt .., _) => true
     | _ => false) = true := by decide +kernel

end Gabbro.Stage0.OptionalAxiomWitness
