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

/-- LSE read-modify-write (`LDADD`/`LDCLR`/`LDEOR`/`LDSET`/`LDSMAX`/
    `LDSMIN`/`LDUMAX`/`LDUMIN`, `SWP`, and the `ST*` aliases with `t = 31`
    discarding the result): read the old value, write `atomicFun op`
    applied to old and register value, return old unless `t = 31`. `acq`
    sets acquire on the read half, `rel` sets release on the write half
    (agent 09's `atomicReadAcc`/`atomicWriteAcc`); `excl` is false for both
    (atomicop, never exclusive). Sizes 1/2/4/8 bytes.
    -- Sail: instrs64.sail:25698 (`execute_..._atomicops_ld`), :51771
       (SWP); v8_base.sail:28334 (`MemAtomic`). -/
def ldAtom (cfg : MemCfg) (op : AtomicOp) (acq rel : Bool)
    (nbytes : Nat) (n s t : Nat) : Eff Unit := do
  if n == 31 then checkSP else pure ()
  let base ← rdBase n
  atomCheck cfg base nbytes nbytes
  let ann : AtomicAnn := { acq := acq, rel := rel }
  let old ← rawRead (atomicReadAcc ann base nbytes)
  let sv ← rdBase s
  let new := atomicFun op nbytes old (sv.toNat % 2 ^ (8 * nbytes))
  rawWrite (atomicWriteAcc ann base nbytes) new
  if t == 31 then pure ()
  else wrBase t (BitVec.ofNat 64 (mask nbytes old))

/-- `CAS`/`CASA`/`CASL`/`CASAL` (byte/half/word/doubleword): compare memory
    with `Xs`, on equality write `Xt`, and always update `Xs` with the old
    value (zero-extended). On mismatch nothing is written (a lone read
    event, no `rmw` pair on agent 09's side).
    -- Sail: instrs64.sail:6382; v8_base.sail:28403 (`cmpfail`). -/
def cas (cfg : MemCfg) (acq rel : Bool) (nbytes : Nat)
    (n s t : Nat) : Eff Unit := do
  if n == 31 then checkSP else pure ()
  let base ← rdBase n
  atomCheck cfg base nbytes nbytes
  let ann : AtomicAnn := { acq := acq, rel := rel }
  let csv ← rdBase s
  let nsv ← rdBase t
  let old ← rawRead (atomicReadAcc ann base nbytes)
  if casCmp nbytes csv.toNat old then
    rawWrite (atomicWriteAcc ann base nbytes) (mask nbytes nsv.toNat)
  else pure ()
  wrBase s (BitVec.ofNat 64 (mask nbytes old))

/-- `CASP`/`CASPA`/`CASPL`/`CASPAL`: the pair form. `halfBits` is the HALF
    width in bits (32 or 64); the compare value is `X[s+1] @ X[s]`
    (little-endian) and the result writes back low half to `X[s]`, high
    half to `X[s+1]`. Two half-size read events and, on match, two
    half-size writes: value-identical to Sail's one joined `MemAtomic`.
    -- Sail: instrs64.sail:6494. -/
def casp (cfg : MemCfg) (acq rel : Bool) (halfBits : Nat)
    (n s t : Nat) : Eff Unit := do
  if n == 31 then checkSP else pure ()
  let base ← rdBase n
  let half := halfBits / 8
  atomCheck cfg base (2 * half) (2 * half)
  let ann : AtomicAnn := { acq := acq, rel := rel }
  let s1 ← rdBase s
  let s2 ← rdBase (s + 1)
  let t1 ← rdBase t
  let t2 ← rdBase (t + 1)
  let o1 ← rawRead (atomicReadAcc ann base half)
  let o2 ← rawRead (atomicReadAcc ann (addOff base (Int.ofNat half)) half)
  let cmp := mask half s1.toNat + mask half s2.toNat * 2 ^ halfBits
  let old := o1 + o2 * 2 ^ halfBits
  if old == cmp then
    rawWrite (atomicWriteAcc ann base half) (mask half t1.toNat)
    rawWrite (atomicWriteAcc ann (addOff base (Int.ofNat half)) half)
      (mask half t2.toNat)
  else pure ()
  wrBase s (BitVec.ofNat 64 o1)
  wrBase (s + 1) (BitVec.ofNat 64 o2)

/-- Fixture: X0 holds operand 7, X1 holds base 64, address 64 holds 10. -/
def gprA : Nat → BitVec 64 := upd (upd s0.regs.gpr 0 (BitVec.ofNat 64 7)) 1 (BitVec.ofNat 64 64)

def memA10 : Nat → Nat := storeNat s0.mem 64 10 4

def sA : State := { regs := { s0.regs with gpr := gprA }, mem := memA10 }

/-- `LDADDAL W2, W0, [X1]`: returns 10, memory becomes 17. -/
def exLdadd : Eff (BitVec 64 × Nat) := do
  ldAtom cfgNoFault .add true true 4 1 0 2
  let r ← rdBase 2
  let m ← memReadEff cfgNoFault (BitVec.ofNat 64 64) 4 .plain false
  pure (r, m)

theorem exLdadd_ok :
    (runEffV 80 exLdadd sA).map Prod.fst
      = some (BitVec.ofNat 64 10, 17) := by decide

/-- Planted wrong case: the result register holds the OLD value, not NEW. -/
theorem exLdadd_notNew :
    (runEffV 80 exLdadd sA).map Prod.fst ≠ some (BitVec.ofNat 64 17, 17) := by decide

/-- `STADDL W0, [X1]`: memory becomes 17, no result register. -/
def exStadd : Eff Nat := do
  ldAtom cfgNoFault .add false true 4 1 0 31
  memReadEff cfgNoFault (BitVec.ofNat 64 64) 4 .plain false

theorem exStadd_ok : (runEffV 80 exStadd sA).map Prod.fst = some 17 := by decide

/-- Fixture: X1 holds base 64, X5 holds `0x11223344`, address 64 holds
    `0xAABBCCDD`. -/
def gprSWP : Nat → BitVec 64 := upd (upd (upd s0.regs.gpr 1 (BitVec.ofNat 64 64)) 5 (BitVec.ofNat 64 287454020)) 6 (BitVec.ofNat 64 0)

def memSWP : Nat → Nat := storeNat s0.mem 64 2864434397 4

def sSWP : State := { regs := { s0.regs with gpr := gprSWP }, mem := memSWP }

/-- `SWPA W6, W5, [X1]`: returns old, memory takes the operand. -/
def exSwp : Eff (BitVec 64 × Nat) := do
  ldAtom cfgNoFault .swp true false 4 1 5 6
  let r ← rdBase 6
  let m ← memReadEff cfgNoFault (BitVec.ofNat 64 64) 4 .plain false
  pure (r, m)

theorem exSwp_ok :
    (runEffV 80 exSwp sSWP).map Prod.fst
      = some (BitVec.ofNat 64 2864434397, 287454020) := by decide

/-- Planted wrong case: old and new are not swapped. -/
theorem exSwp_notSwapped :
    (runEffV 80 exSwp sSWP).map Prod.fst
      ≠ some (BitVec.ofNat 64 287454020, 2864434397) := by decide

/-- Fixture: as `sSWP` but X5 (comparand) holds `0xAABBCCDD` too. -/
def gprCAS : Nat → BitVec 64 := upd (upd (upd s0.regs.gpr 1 (BitVec.ofNat 64 64)) 5 (BitVec.ofNat 64 2864434397)) 6 (BitVec.ofNat 64 287454020)

def sCAS : State := { regs := { s0.regs with gpr := gprCAS }, mem := memSWP }

/-- `CASL W5, W6, [X1]` with matching comparand: memory takes the new
    value, `W5` keeps the old one. -/
def exCas : Eff (BitVec 64 × Nat) := do
  cas cfgNoFault false true 4 1 5 6
  let r ← rdBase 5
  let m ← memReadEff cfgNoFault (BitVec.ofNat 64 64) 4 .plain false
  pure (r, m)

theorem exCas_ok :
    (runEffV 80 exCas sCAS).map Prod.fst
      = some (BitVec.ofNat 64 2864434397, 287454020) := by decide

/-- Fixture: as `sCAS` but the comparand X5 is 0 (mismatch). -/
def gprCASf : Nat → BitVec 64 := upd gprCAS 5 (BitVec.ofNat 64 0)

def sCASf : State := { regs := { s0.regs with gpr := gprCASf }, mem := memSWP }

/-- Mismatch: `W5` is updated with the old value, memory is untouched. -/
def exCasFail : Eff (BitVec 64 × Nat) := do
  cas cfgNoFault false true 4 1 5 6
  let r ← rdBase 5
  let m ← memReadEff cfgNoFault (BitVec.ofNat 64 64) 4 .plain false
  pure (r, m)

theorem exCasFail_ok :
    (runEffV 80 exCasFail sCASf).map Prod.fst
      = some (BitVec.ofNat 64 2864434397, 2864434397) := by decide

/-- Planted wrong case: failure is observably not success. -/
theorem exCasFail_notSuccess :
    (runEffV 80 exCasFail sCASf).map Prod.fst
      ≠ some (BitVec.ofNat 64 2864434397, 287454020) := by decide

/-- Fixture for `CASPAL`: base 64 in X1, comparands `0xAAAAAAAA` /
    `0xBBBBBBBB` in X4/X5, new values 1/2 in X6/X7, memory preset to the
    comparands. -/
def gprCASP : Nat → BitVec 64 := upd (upd (upd (upd (upd s0.regs.gpr 1 (BitVec.ofNat 64 64)) 4 (BitVec.ofNat 64 2863311530)) 5 (BitVec.ofNat 64 3149642683)) 6 (BitVec.ofNat 64 1)) 7 (BitVec.ofNat 64 2)

def memCASP : Nat → Nat := storeNat (storeNat s0.mem 64 2863311530 4) 68 3149642683 4

def sCASP : State := { regs := { s0.regs with gpr := gprCASP }, mem := memCASP }

/-- `CASPAL X4, X6, [X1]` with matching comparands: memory takes the new
    pair, `X4`/`X5` keep the old halves. -/
def exCasp : Eff (BitVec 64 × BitVec 64 × Nat) := do
  casp cfgNoFault true true 32 1 4 6
  let a ← rdBase 4
  let b ← rdBase 5
  let m ← memReadEff cfgNoFault (BitVec.ofNat 64 64) 4 .plain false
  pure (a, b, m)

theorem exCasp_ok :
    (runEffV 80 exCasp sCASP).map Prod.fst
      = some (BitVec.ofNat 64 2863311530, BitVec.ofNat 64 3149642683, 1) := by decide

end Arm

/-
CUTS: only the atomic gate, prefetch-immediate and the shared-vocabulary
smoke test are present. Exclusive pairs, CAS/CASP, the LD/ST/SWP wrappers,
register and literal prefetch, and all family examples are still missing
(listed in REPORT-12.md).
-/

#print axioms Arm.prfmImm_ok
