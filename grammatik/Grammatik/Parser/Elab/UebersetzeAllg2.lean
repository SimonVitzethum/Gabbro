/-
  File:      Grammatik/Parser/UebersetzeAllg2.lean
  Subject:   T3 PART 6: generic lowering, second half.

  Lane 162 (`Parser/UebersetzeAllg.lean`) builds `declOf : UProg ->
  Deklaration` with `Fin` carriers and the generic lowering of
  indices, sides and ensures. This file finishes it: statement
  lowering (`UStmt.assign`/`assignTab`/`call` to
  `Stmt.assignDurch`/`assignSlot`/`Stmt.call`), call arguments
  (`var`/`freshPtr`/`wert`), `RufPasst` assembly by harvest, bodies
  and `Endblock`s, program assembly, and `lowerAllg : (u : UProg) ->
  Except String (Programm (declOf u) x List (declOf u).Fn)`.

  Then the 104 pins on the generically lowered program
  (`programmImFragmentG`/`fussOrtGB` by `decide`, data agreement
  with `G104_referenz.gD`), the real-text lexer pin for 104, and one
  theorem chaining all stages for 104.
-/
module

public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil2
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil3
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil4
