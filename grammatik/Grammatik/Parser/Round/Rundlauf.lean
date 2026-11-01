/-
  File:      Grammatik/Parser/Rundlauf.lean
  Subject:   T3 (lane 161): printer and general round trip by induction,
              expressions first (MUSE-REPORT-135 findings 2 and 3).

  (1) soundness of the structural equality `beqSExpr`
  (`beqSExpr a b = true -> a = b`); (2) a token-level printer
  `druckToks : SExpr -> List Token`, fully parenthesised (every
  binary operator rides inside its own parens, so no level of the
  precedence chain can misread the shape); (3) `parse_druck`: every
  printable (`gut`) expression parses back from its printed tokens
  with fuel `brennstoff e` (lane 172: `12 * (groesse e + 1) +
  groesse e + 8` -- measured, see its doc comment), by induction
  over `e`; (4) the analogous statement for statements.

  The round trip needs a printability premise (`gut`): the parser
  is fixed, and several `SExpr` shapes have no token spelling that
  parses back (reserved head words, unknown operator spellings,
  `sizeof` over a non-place, `old` over a non-place, `Some` with
  /= 1 argument, `u64::max`-style `Grund` with an integer head,
  suffixes on non-place bases). Each is booked in CUTS.
-/
module

public import Grammatik.Parser.Round.Rundlauf.Teil1
public import Grammatik.Parser.Round.Rundlauf.Teil2
public import Grammatik.Parser.Round.Rundlauf.Teil3
public import Grammatik.Parser.Round.Rundlauf.Teil4
public import Grammatik.Parser.Round.Rundlauf.Teil5
public import Grammatik.Parser.Round.Rundlauf.Teil6
public import Grammatik.Parser.Round.Rundlauf.Teil7
