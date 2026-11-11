module

public import Grammatik.Parser.Elab.Proben.CallElse.Accepted

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
namespace Gabbro.Grammatik.Parser.CallElseProben
open Uebersetze UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def sourceError (text : String) : Option String :=
  match lex text with
  | .error _ => some "lex"
  | .ok tokens => match parseTopTief tokens with
    | .error e => some ("parse: " ++ e)
    | .ok items => match elabU (pre108 items) with
      | .error e => some e
      | .ok _ => none

def infallibleSource : String :=
  "extern fn rd(x: u32 in 0 .. 9) -> u32 in 0 .. 9 effects { pure }; " ++
  "impl fn f() { rd(1) else { return; }; }"

theorem infallible_refused_zeuge :
    sourceError infallibleSource = some "call else needs a fallible axiom callee" := by decide +kernel

def userFunctionSource : String :=
  "reason G { Weg = 1 \"failed\" exhaustive } " ++
  "impl fn rd(x: u32 in 0 .. 9) -> u32 in 0 .. 9 or G { return x; } " ++
  "impl fn f() { rd(1) else { return; }; }"

theorem user_function_refused_zeuge :
    sourceError userFunctionSource = some "call else needs an axiom callee" := by decide +kernel

/-- An error handler must terminate; a statement handler cannot silently recover
    by falling off its block and pretending the call succeeded. -/
def fallingHandlerSource : String := foreignHead ++
  "impl fn f() { rd(1) else { }; }"

theorem falling_handler_refused_zeuge :
    (match uebersetzeAllg fallingHandlerSource with
      | .error e => some e
      | .ok _ => none) = some "lower: an else branch falls through" := by decide +kernel

end Gabbro.Grammatik.Parser.CallElseProben
