/- Actual bounded dyadic normalization in integer runner instructions. -/
import Stage0.Senke.Ausdruck.Arithmetik.Adaptiv

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- State slots are quotient, exact remainder, denominator distance, target,
    remaining fuel, and completed transfers. Distances above 61 are retained
    explicitly: no machine shift attempts to materialize a large denominator.
    Preconditions for the pending simulation are a word-sized nonnegative
    remainder, target at most 2^60, and canonical input remainder. -/
def floatNormalizeLoopL (base : Nat) : Option (List II × Nat) := do
  let q := base
  let r := base+1
  let k := base+2
  let target := base+3
  let fuel := base+4
  let count := base+5
  let tmp := base+6
  let den := base+7
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  let cq ← floatNormalizeStepL false (base+8) (load q) (load r) (load den) (load target)
  let cr ← floatNormalizeStepL true (base+9) (load q) (load r) (load den) (load target)
  let small := [ci 1 tmp 1 0, ci 11 den tmp k] ++ cq.1 ++ cr.1 ++
    [ci 2 q (base+8) 0, ci 2 r (base+9) 0]
  let large := [ci 1 tmp 2 0, ci 5 q q tmp, ci 1 tmp 1 0, ci 4 k k tmp]
  let tail := [ci 1 tmp 1 0, ci 3 count count tmp, ci 4 fuel fuel tmp,
    ci 18 (-(16 * (6 + large.length + 1 + small.length + 3) : Int)) 0 0]
  let total := 6 + large.length + 1 + small.length + tail.length
  let head := [ci 19 fuel (16 * total) 0, ci 13 tmp q target,
    ci 19 tmp (16 * (total-2)) 0, ci 1 tmp 61 0,
    ci 13 tmp tmp k, ci 19 tmp (16 * (1 + large.length + 1)) 0]
  pure (head ++ large ++ [ci 18 (16 * (1 + small.length)) 0 0] ++ small ++ tail,
    max cq.2 cr.2)

end Gabbro.Stage0.Senke
