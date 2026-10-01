/-
  File:      Grammatik/X86/Vektor.lean
  Subject:   Packed integer lanes over the canonical x86-64 words (lane 290).

  Packed 128-bit integer words for a future SIMD profile, over the SAME
  canonical vocabulary (`Grammatik/X86/Typen.lean`: `Wort`, `Breite`;
  `Wort.lean`: `addB`/`subB`/`xorB`, `trunc`/`maske`; `Speicher.lean`:
  `read64`/`write64`, frames, read-back). Lanes are 8/16/32/64-bit fields
  of one `BitVec 128`; lane arithmetic is modular at the lane width and
  memory carriage is two ordered canonical 64-bit chunk accesses.

  No XMM register file is created and `Befehl` is not extended: this is the
  data/operation foundation only. SIMD optimisation admission stays refused
  (see `simdFreigabe`) until source correspondence, fault order, tearing,
  concurrent observations and budget transfer are proved. No FP SIMD.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- A packed integer word: 128 bits holding 16/8/4/2 lanes. -/
abbrev Vektor := BitVec 128

/-- Lane count per width: 16 x 8-bit, 8 x 16-bit, 4 x 32-bit, 2 x 64-bit. -/
def laneCount : Breite → Nat
  | .b8 => 16
  | .b16 => 8
  | .b32 => 4
  | .b64 => 2

/-- Horner-packed lane values: lane `i` holds `f i % 2^w`. -/
def vecVal (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (f 0 % 2 ^ w) + 2 ^ w * vecVal w (fun i => f (i + 1)) n

/-- One-step unfolding of the Horner packing (definitional). -/
theorem vecVal_succ (w : Nat) (f : Nat → Nat) (n : Nat) :
    vecVal w f (n + 1) = (f 0 % 2 ^ w) + 2 ^ w * vecVal w (fun i => f (i + 1)) n := rfl

/- CUTS:
    Skeleton only: lane accessors, lane operations, memory carriage,
    correctness/no-carry theorems, witnesses and the SIMD refusal are open.
-/

#print axioms vecVal_succ

end Gabbro.Grammatik.X86
