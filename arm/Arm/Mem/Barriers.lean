/-
  File:      Arm/Mem/Barriers.lean
  Subject:   Barrier-ordered-before (bob, Arm ARM B2.3) over candidate executions.
  Sail:
    - sail-arm/arm-v9.4-a/src/interface.sail:166-184 (DxB, Barrier union)
    - sail-arm/arm-v9.4-a/src/impdefs.sail:880-894 (DataMemoryBarrier et al.)
    - sail-arm/arm-v9.4-a/src/v8_base.sail:1911-1919 (MBReqDomain, MBReqTypes)
    - sail-arm/arm-v9.4-a/src/instrs64.sail:10271-10277 (DMB),
      10342-10345 (DSB), 22746-22748 (ISB)
    - sail/lib/concurrency_interface/read_write_v1.sail
      (AS_rel_or_acq = LDAR/STLR, AS_acq_rcpc = LDAPR)
-/
module

public import Arm.Mem.Barriers.Teil1
public import Arm.Mem.Barriers.Teil2
