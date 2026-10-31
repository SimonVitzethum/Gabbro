import Stage0.StartArgument
import Grammatik.Parser.Elab.UebersetzeAllg3

namespace Gabbro.Stage0.StartArgument
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Exercise the actual canonical parser/elaborator with repeated functions and distinct
    source arguments; this adapter does not enable the still parameterless image startup. -/
def sourceArguments (text : String) : Except String (List (List SExpr)) := do
  let tokens ← (lex text).mapError (fun _ => "lex")
  let parsed ← parseTopTief tokens
  let items := uMembers (pre108 parsed)
  let unit ← elabU items
  let starts ← fromItems unit items
  pure (starts.map (·.sourceArgs))

def argumentSource : String :=
  "module m { impl fn worker(i : u32 in 0 .. 9, b : bool) { } concurrent { worker(7, true), worker(2, false) }; }"

#eval do
  match sourceArguments argumentSource with
  | .error e => throw (IO.userError e)
  | .ok starts =>
    unless starts.length == 2 && beqSExprList (starts[0]?.getD []) [.lit 7, .tru] &&
        beqSExprList (starts[1]?.getD []) [.lit 2, .fls] do
      throw (IO.userError "source start arguments or multiplicity changed")
  if (sourceArguments
      "module m { impl fn worker(i : u32 in 0 .. 9) { } concurrent { worker(10) }; }").isOk then
    throw (IO.userError "out-of-range source start argument accepted")

#print axioms expression_literal
#print axioms expression_negative
#print axioms expression_literal_zeuge
#print axioms expression_negative_zeuge
end Gabbro.Stage0.StartArgument
