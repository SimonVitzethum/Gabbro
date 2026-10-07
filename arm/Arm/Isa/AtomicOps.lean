/-
  File:      Arm/Isa/AtomicOps.lean
  Subject:   Execute-level semantics of the AArch64 exclusive pairs, LSE
             atomics and prefetch hints, from decoded fields to `Eff Unit`.
             Agent 15 writes the decoder; agent 09 owns the memory-model
             side (`Arm.Mem.Atomics`: monitors, `aob`, atomicity) and the
             shared vocabulary below (`AtomicOp`, `atomicFun`, `casCmp`,
             `atomicReadAcc`, `AtomicAnn`, ...), which this file reuses
             without redefining. This file is the `execute` side.
-/
import Arm.Isa.Addr
import Arm.Mem.Atomics

namespace Arm

/-- Fault plus alignment gate for one atomic access of `nbytes` bytes at
    `addr`, requiring `alignReq`-byte alignment. Unlike plain loads and
    stores, an atomicop faults when misaligned at ANY ordering: Sail checks
    `IsAligned` and then `AArch64_UnalignedAccessFaults`, whose
    `exclusive | atomicop` arm fires for every atomicop.
    -- Sail: v8_base.sail:28334 (`MemAtomic`), :22799. -/
def atomCheck (cfg : MemCfg) (addr : Addr) (nbytes alignReq : Nat) : Eff Unit :=
  if cfg.fault addr nbytes then .raise (.dataAbort addr)
  else if !isAligned addr alignReq then .raise (.alignment addr)
  else pure ()

/-- `PRFM <hint>, [<Xn>, #off]`: the address is computed and then nothing
    happens architecturally. There is deliberately no `checkSP` (Sail skips
    `CheckSPAlignment` for `MemOp_PREFETCH`), no fault (hints never fault)
    and no memory event: Sail `Prefetch` decodes the hint bits and calls
    `Hint_Prefetch`, which has no architectural effect. `Eff` has no hint
    constructor, and none is added: the source emits none either.
    -- Sail: instrs64.sail:39785 (the `memop != MemOp_PREFETCH` guard);
       v8_base.sail:35873 (`Prefetch`). -/
def prfmImm (n : Nat) (off : Int) : Eff Unit := do
  let base ← rdBase n
  let _addr := addOff base off
  pure ()

theorem prfmImm_ok :
    (runEffV 10 (prfmImm 1 64) s0).map Prod.fst = some () := by decide

/-- No SP check: a misaligned SP (register 31 holds 8) still succeeds. -/
theorem prfmImm_noSPcheck :
    (runEffV 10 (prfmImm 31 64) sSP8).map Prod.fst = some () := by decide

/-- Smoke test of the shared vocabulary: sizes are in BYTES here. -/
theorem atomicFun_add_bytes : atomicFun .add 4 10 7 = 17 := by decide

end Arm

/-
CUTS: only the atomic gate, prefetch-immediate and the shared-vocabulary
smoke test are present. Exclusive pairs, CAS/CASP, the LD/ST/SWP wrappers,
register and literal prefetch, and all family examples are still missing
(listed in REPORT-12.md).
-/

#print axioms Arm.prfmImm_ok
