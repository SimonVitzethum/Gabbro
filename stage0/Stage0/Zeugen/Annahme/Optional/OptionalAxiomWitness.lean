module
public import Stage0.SourceWitness
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

namespace Gabbro.Stage0.OptionalAxiomWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Uebersetze UebersetzeAllg UebersetzeAllg2
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A value-returning foreign call using the optional binding spelling. -/
def characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'o', 'p', 't', 'i', 'o', 'n', 'a', 'l', '_',
   'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 'a', 'x', 'i', 'o', 'm', ' ', 'a', 'x',
   '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's',
   ' ', '{', ' ', 'p', 'u', 'r', 'e', ' ', '}', ' ', 'u', 'n', 'f', 'a', 'l', 's',
   'i', 'f', 'i', 'a', 'b', 'l', 'e', ' ', '\"', 'p', 'r', 'o', 'b', 'e', '\"', ';',
   ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ',
   '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'l', 'e', 't', ' ', 'r', '?', ' ', '=',
   ' ', 'a', 'x', '(', ')', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '2', '3',
   ';', ' ', '}', ' ', '}']

def text : String := String.ofList characters

def parsed := ((lexL characters).mapError reprStr).bind parseTopTief

/-- The staged lexer receives exactly the declared source characters. -/
theorem parsed_from_text_zeuge :
    parsed = ((lexL text.toList).mapError reprStr).bind parseTopTief := by
  simp only [text, String.toList_ofList]
  rfl

theorem parsed_present : parsed.toOption.isSome = true := by kernel_rfl

def unitCandidate := elabU (pre108 (parsed.toOption.get parsed_present))
theorem unit_present : unitCandidate.toOption.isSome = true := by kernel_rfl
def unit := unitCandidate.toOption.get unit_present

theorem caller_present : 0 < unit.fns.length := by
  have size : unit.fns.length = 1 := by kernel_rfl
  rw [size]
  decide

def blockCandidate :=
  lowSeqL (l := false) unit ⟨0, caller_present⟩ [] (fnAt unit ⟨0, caller_present⟩)
    20 (resOf unit ⟨0, caller_present⟩) [] [.bindOptBeg "r" "ax" []]

/-- The actual sequence lowerer constructs the canonical optional axiom block. -/
theorem optional_constructor :
    (match blockCandidate with
     | .ok (⟨_, .bindAxiomOpt ..⟩, _) => true
     | _ => false) = true := by kernel_rfl

end Gabbro.Stage0.OptionalAxiomWitness
