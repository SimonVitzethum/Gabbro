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
-/
import Gabbro.Body
