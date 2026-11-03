module

public import Grammatik.Parser.Elab.Proben.IndirectElse.Parser
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Cover.Mitglieder

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
namespace Gabbro.Grammatik.Parser.IndirectElseProben
open Uebersetze UebersetzeAllg UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def reasonHead : String := "reason G { Weg = 1 \"failed\" exhaustive } "
def pointerHead : String := reasonHead ++
  "impl fn f(p: fn(x: u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } costs <= 2 ops) " ++
  "-> u32 in 0 .. 9 "

/-- The success answer is discarded; the pre-existing local survives the call.
    Only the ending failure handler can refer to the reason. -/
def namedSource : String := pointerHead ++
  "{ let kept = 1; (p)(kept) else (reason) { " ++
  "match reason { Weg => { return 0; } } return 0; }; return kept; }"

def unnamedSource : String := pointerHead ++
  "{ let kept = 1; p(kept) else { return 0; }; return kept; }"

def nestedSource : String := pointerHead ++
  "{ if true { (p)(1) else { return 0; }; } return 1; }"

def referenceSource : String := reasonHead ++
  "impl fn read(x: u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } { return x; } " ++
  "impl fn f() -> u32 in 0 .. 9 { (&read)(1) else { return 0; }; return 1; }"

/-- Actual source export followed by the goal theorem's checker. -/
def acceptedText (text : String) : Bool :=
  match uebersetzeAllg text with
  | .error _ => false
  | .ok ⟨u, program, functions⟩ =>
    AkzeptiertX program (Cover.Differenz.sperrFamilie u) functions [] [] []

def hasCanonicalHandler (text : String) : Bool :=
  match uebersetzeAllg text with
  | .error _ => false
  | .ok ⟨u, program, functions⟩ =>
    (Cover.Mitglieder.mitglieder u program functions).contains "Stmt.callIndElse"

theorem named_accepted_zeuge : acceptedText namedSource = true := by decide +kernel
theorem unnamed_accepted_zeuge : acceptedText unnamedSource = true := by decide +kernel
theorem nested_accepted_zeuge : acceptedText nestedSource = true := by decide +kernel
theorem reference_accepted_zeuge : acceptedText referenceSource = true := by decide +kernel
theorem canonical_handler_zeuge : hasCanonicalHandler namedSource = true := by decide +kernel

end Gabbro.Grammatik.Parser.IndirectElseProben
