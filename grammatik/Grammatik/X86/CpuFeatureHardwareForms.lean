/-
  File:      Grammatik/X86/CpuFeatureHardwareForms.lean
  Subject:   CPUID and XGETBV fetched byte execution over canonical state.

  Lane 688: exact fetched byte forms of CPUID (0F A2) and XGETBV
  (NP 0F 01 D0) over canonical `Zustand`/`Speicher`, with one generic
  named hardware CPU-information/XCR0 answer interface. Official
  reference: Intel SDM 325462-093US (Sep 2026), Vol. 2A CPUID pp. 3-202ff
  and Vol. 2D XGETBV pp. 6-36f, plus Vol. 1 Ch. 13-14 (XSAVE/XCR0, AVX
  detection). No host probing; see CUTS.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- CPUID output: exact 32-bit EAX/EBX/ECX/EDX fields. -/
structure CpuOut where
  eax : BitVec 32
  ebx : BitVec 32
  ecx : BitVec 32
  edx : BitVec 32
  deriving DecidableEq, Repr, Inhabited

/-- Bit test of a 32-bit word. -/
def bit32 (w : BitVec 32) (i : Nat) : Bool :=
  decide ((w.toNat / 2 ^ i) % 2 = 1)

/-- Skeleton witness: bit 26 of 0x04000000 is set. -/
theorem bit32_skelett : bit32 0x04000000 26 = true := by
  decide

/- CUTS: what is not proved here.
  - Full CPUID/XGETBV execution, faults, gates and witnesses are OPEN.
  - No hardware correspondence beyond the cited manual entries.
  - No TSO serialization, entry or validator bridge is claimed yet.
-/

#print axioms bit32_skelett

end Gabbro.Grammatik.X86
