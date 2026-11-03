module

public import Grammatik.Parser.Elab.Proben.IndirectElse.Accepted

@[expose] public section
namespace Gabbro.Grammatik.Parser.IndirectElseProben
open Uebersetze UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def sourceError (text : String) : Option String :=
  match lex text with
  | .error e => some ("lex: " ++ e)
  | .ok tokens => match parseTopTief tokens with
    | .error e => some ("parse: " ++ e)
    | .ok items => match elabU (pre108 items) with
      | .error e => some e
      | .ok _ => none

def infallibleSource : String :=
  "impl fn f(p: fn(x: u32 in 0 .. 9) -> u32 in 0 .. 9 effects { pure } costs <= 2 ops) " ++
  "{ (p)(1) else { return; }; }"

theorem infallible_refused_zeuge : sourceError infallibleSource =
    some "indirect call else needs a fallible function pointer" := by decide +kernel

def notPointerSource : String :=
  "impl fn f() { let p = 1; (p)(1) else { return; }; }"

theorem not_pointer_refused_zeuge : sourceError notPointerSource =
    some "call else needs a function pointer" := by decide +kernel

def fallingHandlerSource : String := pointerHead ++
  "{ (p)(1) else { }; return 1; }"

theorem falling_handler_refused_zeuge :
    (match uebersetzeAllg fallingHandlerSource with
      | .error e => some e
      | .ok _ => none) = some "lower: an else branch falls through" := by decide +kernel

end Gabbro.Grammatik.Parser.IndirectElseProben
