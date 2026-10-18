/-
  Datei:      Grammatik/Gleitkomma.lean
  Gegenstand: A KERNEL-COMPUTABLE IEEE-754 model for binary32 and binary64.

  The current model (`Typen.lean`: `Gleit`, `Semantik.lean`: `gleitRechne`)
  computes floats with Lean's built-in `Float`, which is OPAQUE to the kernel:
  nothing about float values can be proved and no witness computed without
  `native_decide` (forbidden). This file is the replacement; since
  2026-09-14 the semantics computes with it (`Typen.lean` `GFloat`,
  `Semantik.lean` `gleitRechne`, dokumente/GLEITKOMMA.md section 7).

  Design: formats as data (`Format`: precision `p`, maximal exponent `emax`);
  values as bit triples (sign, biased exponent, significand as `Nat`) with
  finite / zero / subnormal / infinity / NaN cases; exact values as rationals
  (`Exakt`: `Int` numerator with a power-of-two exponent, plus the general
  `Bruch` for division); round-to-nearest-ties-to-even from the exact value
  (structural / fuel recursion only, so it reduces in the kernel); every op
  is "exact result, then round" -- the IEEE definition.
-/

import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T1
import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T2
import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T3
