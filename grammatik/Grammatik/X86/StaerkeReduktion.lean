/-
  File:      Grammatik/X86/StaerkeReduktion.lean
  Subject:   Range-justified integer strength reduction (lane 311).

  Multiplication/division/remainder by a power of two become shifts/masks
  ONLY where the source range proofs justify them: nonneg operands for
  `mul`/`div`/`rem` (the `M102`/`M137` side conditions carried by the
  syntax itself), a divisor `2 ^ k` that is never zero, and shift counts
  below the machine width. Signed division/remainder (`sdiv`/`srem`) are
  REFUSED: truncation differs from shift for negative numerators. No
  reassociation, no floats, no inferred contracts.

  Target helpers are the REAL canonical word operations (`BitVec` shifts
  and `&&&` over `Grammatik/X86/Typen.lean`'s `Wort`).
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Target left shift: the canonical word shift. -/
def shlW (x : Wort) (k : Nat) : Wort := x <<< k

/-- Target logical right shift: the canonical word shift. -/
def shrW (x : Wort) (k : Nat) : Wort := x >>> k

/-- Target remainder mask for `2 ^ k`: the low `k` bits set. -/
def maskW (k : Nat) : Wort := BitVec.ofNat 64 (2 ^ k - 1)

/-- Probe: `3 << 2` is `12` on real words. -/
theorem probe_shlW : shlW 3 2 = 12 := by decide

/- CUTS:
   Value correspondence (source `Zahl.mul/div/rem` vs `Zahl.shl/shr/band`),
   word bridges with checked nonoverflow/shift counts, the `sdiv` refusal,
   the syntax rewrite with its joint table-write witness, and the memory
   round-trip probe are still to come (one increment at a time).
-/

end Gabbro.Grammatik.X86
