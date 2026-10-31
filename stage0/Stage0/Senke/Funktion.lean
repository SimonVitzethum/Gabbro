/-
  File:      stage0/Stage0/Senke/Funktion.lean
  Subject:   The lowering of stage 0, part 3: function bodies (end blocks) and functions with their contracts.

  A function `f` with `np` parameters runs in a frame whose slots 0 and 1 the `call` wrote, slot 2 holds the
  depth (G's `fuel`), slot 3 is the entry snapshot, and the parameters follow. Its code:
  * depth 0: `exit_group(105)` (`abstieg`); then `requires` into slot `FB + np`, false: `exit_group(101)`;
  * after `requires` succeeds, capture the postcondition's entry cell in header slot 3;
  * descending moves copy parameters above the original parameters and the two return words;
  * the body (`lowEnd`) uses that shifted environment; the original parameters remain available to `ensures`;
  * every `ret e`: `e`, into slot `lo = FB + np`, then `ensures` over the result and the parameters into the
    slot above, false: `exit_group(102)`; else the result into slot 2 and `ret`.
  Refused: a function with invariants to keep (`schuldet`), or a form outside the fragment. A function without a
  result returns whatever word slot `FB + np` holds; nobody reads it.
-/
import Stage0.Senke.Anweisung
import Stage0.Senke.Stopp
import Stage0.Senke.Ausdruck.Old.Capture

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

/-- The code of `f`, and the first slot it does not write. -/
def lowFun (passes : Nat) (P : Programm D) (A : D.Fn → Nat) (L : Lay D) (f : D.Fn) : Option (List II × Nat) :=
  let np := (D.params f).length
  if (D.invs.filter (schuldet f)).isEmpty then do
    let req ← lowE L (P.requires f) (FB + np)
    let ens ← lowEns L (P.ensures f) (FB + np + 1)
    -- Preserve the incoming ABI and both return words below the lexical environment.
    let reserved := np + 2
    let body ← lowEnd (reserved := reserved) passes A L (FB + np) ens [] (0, 0) (P.rumpf f)
    let snap ← snapC L (oldCells (P.ensures f))
    pure (guardC 2 105 (FB + np) ++ req.1 ++ guardC (FB + np) 101 (FB + np) ++ snap ++ (relocateC FB reserved np ++ body.1),
      max (FB + np + 8) (max req.2 (max (frei (D.params f) reserved) body.2)))
  else none

end Gabbro.Stage0.Senke
