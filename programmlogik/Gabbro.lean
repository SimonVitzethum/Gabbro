/-
  Gabbro -- what a Gabbro PROGRAM means, in Lean 4.

  **This is not `passlogik`, and the distinction is the reason it is a separate project.**
  `passlogik/` formalises the CHECKER: range lattices, effect hulls, rank order, linearity --
  statements about passes. What stands here is a statement about PROGRAMS: given a Gabbro
  body and a specification, does the body establish the specification?

  *A model that mixed the two would let a theorem about a pass be read as a theorem about a
  program, and those are different claims with different consequences.*

  | File        | Subject                                                        |
  |-------------|----------------------------------------------------------------|
  | `Body.lean` | the statement descent -- what a body does, statement by statement |
  | `Coverage.lean` | WHO ANSWERS for each form -- the plumbing as general lemmas, and the
    proposition that everything except the person's own logic is carried, assumed by name,
    or refused with a tag |
  | `Sicherheit.lean` | the SAFETY theorem over `Body.lean` (2026-09-09): a body the checker
    accepts gets stuck only at a `requires` or an `invariant` -- the person's own logic, and
    nothing else. `Sicherheit/Ausdruck.lean` carries the expression half, `Sicherheit/Anweisung.lean`
    the statement half; the head file names what is assumed and what was found |
-/
import Gabbro.Body
import Gabbro.Coverage
import Gabbro.Sicherheit
import Gabbro.KompositionBeweis
