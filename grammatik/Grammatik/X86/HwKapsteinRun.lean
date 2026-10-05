/-
  File:      Grammatik/X86/HwKapsteinRun.lean
  Subject:   Capstone run: a reached multi-family program run on two cores.

  Lane 1293: on top of the capstone union step `HwVollSchritt` (lane 1149,
  `HwKapstein.lean`, reused unchanged), build ONE reached run: bytes
  `pinXadd` (LOCK XADD [rbp], rax) in the mapped executable window
  4096..4128, executed on two cores of `HwMaschine`, mixing LOCK XADD, a
  push/call/pop/ret sequence, a scalar FP op, a packed integer op and a
  plain store/load with forwarding, ending with drains observed from both
  cores. Every definition is lifted from the accepted families, never
  redefined; fetches cite the accepted decode pins.
-/
import Grammatik.X86.HwKapstein

namespace Gabbro.Grammatik.X86

/-- Run data window: 8192..8224, holding the lock word (8192), the stack
    slot (8200) and the foreign byte (8216) disjointly. -/
def runDataRW (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8224)

/-- Run registers core 0: XADD delta 5 in rax, base 8192 in rbp, divisor
    7 in rcx, 16-aligned top 8208 in rsp, everything else zero. -/
def runReg0 : Register → Wort := fun q =>
  if q = .rax then BitVec.ofNat 64 5
  else if q = .rbp then BitVec.ofNat 64 8192
  else if q = .rcx then BitVec.ofNat 64 7
  else if q = .rsp then BitVec.ofNat 64 8208
  else BitVec.ofNat 64 0

/-- Run registers core 1: same shape, delta 7 in rax. -/
def runReg1 : Register → Wort := fun q =>
  if q = .rax then BitVec.ofNat 64 7
  else if q = .rbp then BitVec.ofNat 64 8192
  else if q = .rcx then BitVec.ofNat 64 0
  else if q = .rsp then BitVec.ofNat 64 8208
  else BitVec.ofNat 64 0

/-- Run core data: both cores run from 4096 with zeroed XMM. -/
def runKern : Nat → HwKern
  | 0 => ⟨runReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | 1 => ⟨runReg1, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Run buffers: core 1 holds one pending byte 99 at 8216. -/
def runBuf : Nat → List TSOEintrag
  | 1 => [⟨BitVec.ofNat 64 8216, BitVec.ofNat 8 99⟩]
  | _ => []

/-- Run start machine: XADD bytes mapped executable, word 10 at 8192,
    two cores, full silicon with OS vector state. -/
def runStart : HwMaschine :=
  ⟨lockZeugSpeicher pinXadd 10 lockCodeExec runDataRW runDataRW,
    runKern, runBuf, basisHw, fun _ => basisBereit⟩

/-- Admission on the run baseline is the lock witness admission: the
    profiles are identical, so the accepted equation is reused. -/
theorem runStart_zugelassen (f : PerfMerkmal) :
    merkmalZugelassen basisHw basisBereit f = true :=
  hwLockWitStart_zugelassen f

/-- The run start machine is well-formed. -/
theorem runStart_wf : HwWf runStart :=
  hwWf_aus_zugelassen _ fun _ _ => runStart_zugelassen _

/- CUTS:
    Skeleton only: start machine plus well-formedness. The run steps,
    drains, observations and final memory are not yet built.
-/

#print axioms runStart_wf

end Gabbro.Grammatik.X86
