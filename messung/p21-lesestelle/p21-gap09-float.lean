/-
  GAP-09 `float` (G-LEX) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, ninth LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): float = dec "." dec [ "e" [ "+" | "-" ] dec ].

  MAPPING RULE (tree vs token). `float` has no constructor as a term: the
  spelling feeds `Ty.fl` bounds and `Block.gleitLit`, and EXACTNESS decides
  whether `rounded` is owed. The lexer yields the rational value; elaboration
  reduces it; if the reduced denominator divides a power of two the literal is
  exact (no rounding owed), otherwise the `rounded` mark is owed at `gleitLit`.
  Maximal munch (`..` eats first) and the refusal of `1.` and upper-case `E`
  stay at the lexer: one spelling only.

  MINIMAL PARSE WITNESS. Surface `1.5` is 3/2 -- denominator 2, exact, no
  `rounded` owed. Surface `0.1` is 1/10 -- factor 5 never divides a power of
  two, so `rounded` is owed. The model below is the exactness test on the
  reduced pair; the carrier link is `Block.gleitLit`.
-/
import Grammatik.Syntax

namespace P21.Gap09Float

/-- Denominator `den` divides some power of two (fuel bounds the search). -/
def pow2divides : Nat → Nat → Bool
  | den, 0 => decide (den = 1)
  | den, k + 1 => decide (den = 1) || (decide (den % 2 = 0) && pow2divides (den / 2) k)

/-- Exactness of the reduced fraction num/den: no `rounded` owed iff true. -/
def exactBinary (_num den : Nat) : Bool := pow2divides den 64

-- Surface `1.5` = 3/2: denominator 2, exact.
example : exactBinary 3 2 = true := rfl
-- Surface `0.1` = 1/10: factor 5, never exact.
example : exactBinary 1 10 = false := rfl
-- Surface `2.0` = 2/1: integers are exact.
example : exactBinary 2 1 = true := rfl

-- Carrier link: the spelling lands at `gleitLit` in its range, `rounded` as owed.
open Gabbro.Grammatik in
#check @Block.gleitLit

end P21.Gap09Float
