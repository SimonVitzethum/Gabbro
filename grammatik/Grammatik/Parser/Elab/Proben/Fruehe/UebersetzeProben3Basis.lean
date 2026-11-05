module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Basis
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

namespace Gabbro.Grammatik.Parser.UebersetzeProben3

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- The stage of `uebersetzeAllg` that stops a source (`OK` when none does). -/
def stufe (s : String) : String :=
  match lex s with
  | .error _ => "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse: " ++ e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => "elab: " ++ e
      | .ok u =>
        match lowerAllg u with
        | .error e => "lower: " ++ e
        | .ok _ => "OK"

/-- The elaborated roots and handlers of a source (`none` when a stage stops it). -/
def roots (s : String) : Option (List String × List String) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.roots, u.hands)

def maskFlags (s : String) : Option (List Bool) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.locks.map (·.masks))

end Gabbro.Grammatik.Parser.UebersetzeProben3
