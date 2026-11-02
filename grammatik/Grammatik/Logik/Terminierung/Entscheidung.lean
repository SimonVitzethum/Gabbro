/-
  File:      Grammatik/Logik/Terminierung/Entscheidung.lean
  Subject:   T5 -- THE CLASSES MEET THE SEMANTICS (2026-10-22).

  * `tor_gut` -- the call gate of T4 holds for EVERY program, with the rank computed from the call graph
    (`rangB f`: how many functions `f` reaches) and the cycles of `zykS`: a callee reaches no more than its
    caller, and as many only if it reaches the caller back. So T4 needs nothing static beyond measures of one
    length along a cycle.
  * `terminierung` -- for every program whose measures meet the user's duty (`MassPflicht`, the `decreases`
    obligation): on every infinite run of machine GX every thread takes only finitely many steps. The budget
    `passes` is what makes a `forever` finite here; machine G grants the passes from outside.
  * `endet_ohne_budget` -- a thread whose start is of class `endet` (`klasse`, T1) never stands at a spent budget:
    no frame of it ever runs a `forever`. Its end does not lean on the budget.
  * `umgebung` and `bedingt` carry no theorem of their own beyond these two: their runs are finite per pass (T3,
    `durchgang_schritte`) and they may stop at the budget; whether a `leave` guard, a `return` inside the loop or a
    base path is ever taken is the program's question (undecidable in general).
-/
module

public import Grammatik.Logik.Terminierung.Entscheidung.Teil1
public import Grammatik.Logik.Terminierung.Entscheidung.Teil1a
public import Grammatik.Logik.Terminierung.Entscheidung.Teil2
