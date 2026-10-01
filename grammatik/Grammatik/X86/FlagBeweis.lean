/-
  File:      Grammatik/X86/FlagBeweis.lean
  Subject:   Mathematical carry and signed-overflow characterisation of the
             EXISTING `add64`/`sub64` flag snapshots from `Grammatik/X86/Wort`.

  Lane 285 (wave A): generic mathematical facts over the REAL canonical
  `Wort` (BitVec 64) and the REAL operations `add64`/`sub64` -- a signed
  interpretation `sint` (BitVec.toInt), OF iff the exact signed sum or
  difference leaves [-2^63, 2^63-1], sign-bit readings (SF = negative,
  threshold 2^63 on toNat), unsigned carry/borrow as Nat range facts, and
  low-byte parity facts. No second add/sub function is defined; every
  lemma consumes `add64`/`sub64` (or the shared flag helpers they use).

  No source correspondence is claimed here; physical instruction semantics
  remain named silicon behaviour plus a later bridge (lane 277 owns it).
-/
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Signed interpretation of a word: two's complement value in
    [-2^63, 2^63-1]. The optimiser and the instruction-semantics consumer
    read ranges through this, never through a second adder. -/
def sint (w : Wort) : Int := w.toInt

/-- Every word denotes a value in the signed 64-bit range. -/
theorem sint_mem (w : Wort) :
    -(2 ^ 63 : Int) ≤ sint w ∧ sint w ≤ 2 ^ 63 - 1 := by
  unfold sint
  rw [BitVec.toInt_eq_toNat_bmod]
  have h1 := Int.le_bmod (x := (w.toNat : Int)) (m := 2 ^ 64) (by decide)
  have h2 := Int.bmod_le (x := (w.toNat : Int)) (m := 2 ^ 64) (by decide)
  constructor <;> omega

/- CUTS:
    OF characterisation, carry/borrow range facts, parity facts, boundary
    witnesses and memory roundtrips are not yet proved in this skeleton.
    No source/ISA hardware theorem is claimed; physical instruction
    semantics remain named silicon behaviour plus a later bridge.
-/

#print axioms sint_mem

end Gabbro.Grammatik.X86
