module
public import Grammatik.Parser.Elab.Konst.Scopes.Functions
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

-- One canonical source-scope implementation, shared with the Stage0 compiler.
namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Only the exact option constructors lack a function dependency. An actual
    const declaration keeps priority, as in canonical const substitution.
    Wrong arities and every other name retain the ordinary function edge. -/
def dependencyCallHead (declared : String → Bool) (name : String) (args : List SExpr) : List String :=
  if declared name then [name] else
  match name, args with
  | "Some", [_] | "None", [] => []
  | _, _ => [name]

mutual
/-- One traversal retains every operand while the caller classifies call heads. -/
def callsWith {α : Type} (head : String → List SExpr → List α) : SExpr → List α
  | .call name args => head name args ++ callsListWith head args
  | .field a _ | .arrow a _ | .un _ a | .old a => callsWith head a
  | .index a b | .bin _ a b => callsWith head a ++ callsWith head b
  | .built _ args | .ext _ _ args => callsListWith head args
  | _ => []
def callsListWith {α : Type} (head : String → List SExpr → List α) : List SExpr → List α
  | [] => []
  | a :: rest => callsWith head a ++ callsListWith head rest
end

/-- The safety hull conservatively retains all original call-shaped heads,
    including absent constructor names; its existing guarantees are unchanged. -/
def calls (expr : SExpr) : List String := callsWith (fun name _ => [name]) expr

def callsList (args : List SExpr) : List String := callsListWith (fun name _ => [name]) args

theorem calls_call (name : String) (args : List SExpr) :
    calls (.call name args) = name :: callsList args := rfl

end Gabbro.Stage0.Frontend
