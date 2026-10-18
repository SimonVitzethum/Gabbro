/-
  File:      Grammatik/KostenG.lean
  Subject:   A STEP BOUND PER FRAME ON THE CALL MACHINE G -- the time half
             of the goal: a frame's OWN steps between its entry and its
             return are bounded by a syntax-directed cost of its body.

  Claim (in one sentence):
    On any run of G, the number of steps thread `f` takes between the entry
    of a frame and that frame's return is at most `kosten` of the frame's
    body, where a call counts the callee's cost (by call depth, or by a
    declared table checked by a decidable `K001`-style test) and loops count
    their static bound; other threads' steps interleave and are not counted.

  What the bound counts: firings of `RufSchrittG P O passes M f M'` with the
    frame's thread `f` as actor, while the frame is on `f`'s stack. It does
    NOT count
    * steps of other threads (they never change `f`'s thread state,
      `rufSchrittG_fremd`), and
    * waiting: a `locks L` unfold (`dannLocks`) fires only while no other
      thread holds `L` (`RufFreiG`), an `awaits` only while the oracle says
      the payload is visible (`O.sichtbar`). While it cannot fire, it is not
      a step of anybody. How long a thread WAITS is therefore a scheduler
      fact: **SCHEDULER ASSUMPTION (not proved here): fair scheduling and a
      bounded hold time of every lock**. The surface language has the hold
      bound (`lock L … held <= N ops`, SYNTAX.md §lockdecl, checked by
      `kosten.rs` as `K002`), but the Lean declaration `Deklaration` does not
      carry it (the `Lock` fields are `rang` and `maskiert` only), so no
      waiting bound is stated here.

  The proof is a potential argument: `potRest` reads `kosten` as a function
  of the machine residue; every own step of the head frame lowers it by at
  least one (`schrittArt`), a push hands the callee at most the cost the
  caller counted for it, and a pop drops a frame whose potential is at least
  one. Nothing about reachability, lock discipline or contracts is needed.

  No `mathlib`, no `sorry`, no `axiom`.
-/


import Grammatik.Logik.Fortschritt.KostenG.T1
import Grammatik.Logik.Fortschritt.KostenG.T2
import Grammatik.Logik.Fortschritt.KostenG.T3
import Grammatik.Logik.Fortschritt.KostenG.T4
import Grammatik.Logik.Fortschritt.KostenG.T5
