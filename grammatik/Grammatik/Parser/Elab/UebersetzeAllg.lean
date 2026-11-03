/-
  File:      Grammatik/Parser/UebersetzeAllg.lean
  Subject:   T3 PART 5: generic lowering from source to the G program.

  Lane 160 (`Parser/Uebersetze.lean`) elaborates the parsed surface tree
  to plain data (`UProg`) generically, but lowers only onto the 104
  declaration universe (`G104_referenz.gD`). This file builds the
  declaration from the `UProg` itself, with index carriers (`Fin n`
  for tables, locks, fields and functions): `declOf : UProg ->
  Deklaration` and `lowerAllg : (u : UProg) -> Except String
  (Programm (declOf u) x List (declOf u).Fn)`.

  The 104 and 108 instances pin the fragment and footprint checks on
  the generically lowered programs (`by decide`), the data agreement
  with the exporter programs, the real-text lexer pin (comments lex
  away, no lexer change was needed), and one theorem chaining all
  stages for 104.
-/
module

public import Grammatik.Parser.Elab.Generic.Signatures
public import Grammatik.Parser.Elab.Generic.C09Sig
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil1
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2
public import Grammatik.Parser.Elab.UebersetzeAllg.Eingebaut
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil4
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
