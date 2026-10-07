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
import Arm.Isa.LoadStore
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

/-- One raw read event: the caller has already run `atomCheck`. -/
def rawRead (a : Access) : Eff Nat := .rdMem a .ret

/-- One raw write event: the caller has already run `atomCheck`. -/
def rawWrite (a : Access) (v : Nat) : Eff Unit := .wrMem a v (.ret ())

/-- Exclusive pair load (`LDXP`/`LDAXP`): two half-size exclusive reads,
    low half to `t`, high half to `t2` (little-endian). `datasize` is the
    TOTAL width in bits: 64 (two 32-bit registers) or 128 (two 64-bit
    registers). The accessors come from agent 09 (`excl` is true: Sail
    marks `accdesc.exclusive`, `AV_exclusive`). Alignment is asymmetric by
    form: the 2x32 load needs only half (4-byte) alignment (Sail reads it
    as one `ispair` access); the 2x64 load needs full 16-byte alignment
    (Sail checks `IsAligned` explicitly).
    -- Sail: instrs64.sail:28942 (`execute_..._exclusive_pair`, load arm). -/
def ldxp (cfg : MemCfg) (acqrel : Bool) (datasize : Nat)
    (n t t2 : Nat) : Eff Unit := do
  if n == 31 then checkSP else pure ()
  let base ← rdBase n
  let k : ExclKind := if acqrel then .ldaxr else .ldxr
  let alignReq := if datasize == 128 then 16 else 4
  atomCheck cfg base (datasize / 8) alignReq
  let half := datasize / 16
  let v1 ← rawRead (exclReadAcc k base half)
  let v2 ← rawRead (exclReadAcc k (addOff base (Int.ofNat half)) half)
  wrBase t (BitVec.ofNat 64 v1)
  wrBase t2 (BitVec.ofNat 64 v2)

/-- Exclusive pair store (`STXP`/`STLXP`): two half-size exclusive writes
    (low half from `t`), status to `Ws`. The `passed` premise is the
    exclusive-monitor verdict owned by agent 09. Stores need full-size
    alignment (Sail uses plain `Mem_set`, not the `ispair` form).
    -- Sail: instrs64.sail:28942 (store arm). -/
def stxp (cfg : MemCfg) (acqrel : Bool) (datasize : Nat)
    (n t t2 s : Nat) (passed : Bool) : Eff Unit := do
  if n == 31 then checkSP else pure ()
  let base ← rdBase n
  let k : ExclKind := if acqrel then .stlxr else .stxr
  atomCheck cfg base (datasize / 8) (datasize / 8)
  if passed then
    let r1 ← rdBase t
    let r2 ← rdBase t2
    let half := datasize / 16
    rawWrite (exclWriteAcc k base half) (r1.toNat % 2 ^ (datasize / 2))
    rawWrite (exclWriteAcc k (addOff base (Int.ofNat half)) half)
      (r2.toNat % 2 ^ (datasize / 2))
    wrBase s (BitVec.ofNat 64 0)
  else
    wrBase s (BitVec.ofNat 64 1)

/-- `STLXP W5, X0, X1, [X2]` (monitor passes) then `LDAXP X3, X4, [X2]`. -/
def exLdxpStxp : Eff (BitVec 64 × BitVec 64 × BitVec 64) := do
  stxp cfgNoFault true 128 2 0 1 5 true
  ldxp cfgNoFault true 128 2 3 4
  let a ← rdBase 5
  let b ← rdBase 3
  let c ← rdBase 4
  pure (a, b, c)

theorem exLdxpStxp_ok :
    (runEffV 80 exLdxpStxp sPair).map Prod.fst
      = some (BitVec.ofNat 64 0, BitVec.ofNat 64 1229782938247303441,
        BitVec.ofNat 64 2459565876494606882) := by decide

/-- Monitor fails: status 1 and the later load reads zero memory. -/
def exStxpFail : Eff (BitVec 64 × BitVec 64 × BitVec 64) := do
  stxp cfgNoFault true 128 2 0 1 5 false
  ldxp cfgNoFault true 128 2 3 4
  let a ← rdBase 5
  let b ← rdBase 3
  let c ← rdBase 4
  pure (a, b, c)

theorem exStxpFail_ok :
    (runEffV 80 exStxpFail sPair).map Prod.fst
      = some (BitVec.ofNat 64 1, BitVec.ofNat 64 0, BitVec.ofNat 64 0) := by decide

/-- Planted wrong case: the fail path is observably not the pass path. -/
theorem exStxpFail_notPass :
    (runEffV 80 exStxpFail sPair).map Prod.fst
      ≠ some (BitVec.ofNat 64 0, BitVec.ofNat 64 1229782938247303441,
        BitVec.ofNat 64 2459565876494606882) := by decide

/-- 2x32 form on `sPair`: only the low 32 bits of each register travel. -/
def exLdxp32 : Eff (BitVec 64 × BitVec 64 × BitVec 64) := do
  stxp cfgNoFault false 64 2 0 1 5 true
  ldxp cfgNoFault false 64 2 3 4
  let a ← rdBase 5
  let b ← rdBase 3
  let c ← rdBase 4
  pure (a, b, c)

theorem exLdxp32_ok :
    (runEffV 80 exLdxp32 sPair).map Prod.fst
      = some (BitVec.ofNat 64 0, BitVec.ofNat 64 286331153,
        BitVec.ofNat 64 572662306) := by decide

/-- Fixture: as `sPair` but the base X2 is 132 (4-aligned, not 8-aligned). -/
def gprXP4 : Nat → BitVec 64 := upd gprPair 2 (BitVec.ofNat 64 132)

def sXP4 : State := { s0 with regs := { s0.regs with gpr := gprXP4 } }

/-- A 2x32 `LDXP` at a 4-aligned address succeeds (half alignment is
    enough for the load). -/
def exLdxp4ok : Eff (BitVec 64 × BitVec 64) := do
  ldxp cfgNoFault false 64 2 3 4
  let b ← rdBase 3
  let c ← rdBase 4
  pure (b, c)

theorem exLdxp4ok_ok :
    (runEffV 60 exLdxp4ok sXP4).map Prod.fst
      = some (BitVec.ofNat 64 0, BitVec.ofNat 64 0) := by decide

/-- The matching 2x32 `STXP` at the same address raises: stores need full
    8-byte alignment. -/
theorem exStxp4_refuses :
    (runEffV 60 (stxp cfgNoFault false 64 2 0 1 5 true) sXP4).isNone
      = true := by decide

end Arm

/-
CUTS: only the atomic gate, prefetch-immediate and the shared-vocabulary
smoke test are present. Exclusive pairs, CAS/CASP, the LD/ST/SWP wrappers,
register and literal prefetch, and all family examples are still missing
(listed in REPORT-12.md).
-/

#print axioms Arm.prfmImm_ok
