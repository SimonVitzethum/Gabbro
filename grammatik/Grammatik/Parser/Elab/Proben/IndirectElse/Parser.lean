module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil4a

import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
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

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def named : SAnw := .callIndElse (.variable "p") [.lit 1] "reason"
  (.block [] (some (.ret none)))
def unnamed : SAnw := .callIndElse (.fnref "read") [.lit 1] ""
  (.block [] (some (.ret none)))

/-- The printed statement without its closing `;` is refused. -/
theorem missing_semicolon_zeuge :
    (parseTopStmt ((druckAnw named).dropLast ++ [.ende])).toOption.isNone = true := by
  decide +kernel

/-- Without its parentheses the reason binder is malformed and refused. -/
theorem malformed_reason_binder_zeuge :
    (parseTopStmt (((druckAnw named).filter fun t => !(t == Token.zeichen ")")) ++ [.ende])).toOption.isNone
      = true := by
  decide +kernel

theorem named_roundtrip_zeuge :
    beqTopStmt (parseTopStmt (druckAnw named ++ [.ende])) (.ok named) = true := by decide +kernel

theorem unnamed_roundtrip_zeuge :
    beqTopStmt (parseTopStmt (druckAnw unnamed ++ [.ende])) (.ok unnamed) = true := by decide +kernel

/-- This fixture also exercises the generic printability derivation. -/
theorem named_printable_zeuge : AnwGut .anw named := by
  apply AnwGut.callIndElse
  · decide
  · decide
  · exact .block [] (some (.ret none)) (by intro s h; cases h) trivial (by intro h; cases h)

end Gabbro.Grammatik.Parser.IndirectElseProben
