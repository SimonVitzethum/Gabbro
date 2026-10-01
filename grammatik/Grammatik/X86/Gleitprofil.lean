/-
  File:      Grammatik/X86/Gleitprofil.lean
  Subject:   Width-aware IEEE target FP profile over the kernel-computable model.

  Lane 286: MXCSR control-state checks (RNE, FTZ/DAZ off, masks set),
  per-context FP state, bit-pattern projection/injection for binary32/64,
  width-specific arithmetic over `Gleitkomma`, the f32-vs-f64 counterexample,
  explicit NaN/sticky/SSE gaps, and float round-trips through `X86.Speicher`.
  No `Ty.fl`/Spec change; no hardware correspondence is claimed here.
-/
import Grammatik.Gleitkomma
import Grammatik.GleitkommaBits
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Target FP control word: the 32-bit MXCSR. -/
abbrev MXCSR := BitVec 32

/-- One MXCSR bit as `Bool` (computable, `decide`-friendly). -/
def mxcsrBit (m : MXCSR) (i : Nat) : Bool := m.toNat.testBit i

/-- Rounding control is round-to-nearest-even (RC bits 13, 14 clear). -/
def mxcsrRundungRNE (m : MXCSR) : Bool :=
  !mxcsrBit m 13 && !mxcsrBit m 14

/-- All six exception masks set (bits 7-12): invalid, denormal, zero,
    overflow, underflow, precision. -/
def mxcsrMaskenAlle (m : MXCSR) : Bool :=
  mxcsrBit m 7 && mxcsrBit m 8 && mxcsrBit m 9 &&
    mxcsrBit m 10 && mxcsrBit m 11 && mxcsrBit m 12

/-- The target profile: RNE, FTZ (bit 15) off, DAZ (bit 6) off,
    all exception masks set. Sticky flags (bits 0-5) are NOT checked. -/
def mxcsrGueltig (m : MXCSR) : Bool :=
  mxcsrRundungRNE m && !mxcsrBit m 15 && !mxcsrBit m 6 && mxcsrMaskenAlle m

/-- The architectural reset value `0x1F80` meets the profile. -/
theorem mxcsr_standard : mxcsrGueltig 0x1F80 = true := by decide

/- CUTS (skeleton):
   Per-context state, pattern helpers, width arithmetic, the f32-vs-f64
   counterexample, NaN/sticky/SSE gaps and memory round-trips are open.
-/

#print axioms mxcsr_standard

end Gabbro.Grammatik.X86
