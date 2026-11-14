module

public import Grammatik.Parser.Print.Stmt
import Lean.Elab.Tactic.Cbv
import all Grammatik.Parser.Stmt.Anweisung.BoundedHeaders
import all Grammatik.Parser.Stmt.Anweisung.Defs2a
import all Grammatik.Parser.Stmt.Anweisung.Defs2
import all Grammatik.Parser.Expr.Tokens
import all Grammatik.Parser.Print.Stmt
import all Grammatik.Parser.Lex.Lexer.Teil1
import all Grammatik.Parser.Lex.Lexer.Teil2

import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
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

namespace Gabbro.Grammatik.Parser.BoundedWitness
attribute [local cbv_eval] strEq_apply_eq_decide

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Small statement-only fixtures: no module elaboration or corpus parser probes. -/
def sourceStatement (text : String) : Except String SAnw := do
  let tokens ← match lex text with
    | .ok ts => pure ts
    | .error _ => throw "lex"
  parseTopStmt tokens

def accepts (text : String) : Bool :=
  match sourceStatement text with
  | .ok (.boundedLoop _ (.block _ _)) => true
  | _ => false

def roundTrip (text : String) : Bool :=
  match sourceStatement text with
  | .ok statement => rundlaufBlock (.block [statement] none)
  | _ => false

theorem while_parser_zeuge :
    accepts "while count < 3 bounded 8 ops on_exceeded overrun { count += 1; }" = true := by
  cbv

theorem for_parser_zeuge :
    accepts "for i in 1 ..< 5 { sum += i; }" = true ∧
    accepts "for i in 1 ..< 5 on_exceeded overrun { i = 1; }" = true := by
  cbv

theorem while_round_trip_zeuge :
    roundTrip "while count < 3 bounded 8 ops on_exceeded overrun { count += 1; }" = true := by
  cbv

theorem for_round_trip_zeuge :
    roundTrip "for i in 1 ..< 5 { sum += i; }" = true ∧
    roundTrip "for i in 1 ..< 5 on_exceeded overrun { next i; }" = true := by
  cbv

theorem missing_bound_refused_zeuge :
    beqTopStmt (sourceStatement "while true on_exceeded overrun { }")
      (.error "while.bound.missing") = true := by
  cbv

theorem missing_handler_refused_zeuge :
    beqTopStmt (sourceStatement "while true bounded 3 ops { }")
      (.error "while.on_exceeded.required") = true := by
  cbv

theorem malformed_range_refused_zeuge :
    beqTopStmt (sourceStatement "for i in 1 .. 5 { }")
      (.error "for.range.half-open-required") = true := by
  cbv

theorem trailing_clause_refused_zeuge :
    beqTopStmt (sourceStatement "for i in 1 ..< 5 bounded 2 ops { }")
      (.error "for.header.trailing-clause") = true := by
  cbv

end Gabbro.Grammatik.Parser.BoundedWitness
