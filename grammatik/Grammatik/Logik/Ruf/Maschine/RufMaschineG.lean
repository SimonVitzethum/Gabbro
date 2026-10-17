/-
  File:      Grammatik/RufMaschineG.lean
  Subject:   THE CALL MACHINE WITH COMPOUND STATEMENTS (attempt G) -- the F
              machine (frames with stored environments, call-log fidelity
              `rufF_treu`) extended with a residue that can hold
              "block, then rest", so every compound statement form unfolds
              step by step instead of getting stuck.

  Why: `RufMaschineF.lean` steps only leaves (`blatt`), calls (`ruf`) and
  returns (`rueck`); a body with `if`, `match`, a `let` binding, a `locks`
  block or a loop cannot advance (see its CUTS). Here the frame residue is
  a `GRest`: an `Endblock` (`ende`), a `Block` followed by a rest (`dann`),
  an environment shrink (`schrumpf`), a lock release marker (`frei`), and
  bounded-loop states (`trav`/`wieder`/`ewig` with their remaining bound),
  and the residues of a caller waiting for a bound value (`wartet`, and
  `wartetSonst`, which keeps the else block of `let x = g(…) else { … }`).
  New steps unfold compounds into that residue; only pushes and pops touch
  the call log (`eintritt`, `rueck`, and `grund` for the error channel), so
  fidelity (`rufG_treu`) follows the F proof pattern. A waiting caller is
  resumed only by a binding pop: no reachable head waits
  (`rufG_nie_wartend`).
-/

import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T2
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T6
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T7
