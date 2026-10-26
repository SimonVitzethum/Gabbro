/-
  File:      stage0/Stage0/Tor/Roh.lean
  Subject:   The raw system call: the Lean face of the trampoline `c/syscall.c`. `which < 6` replaces that argument by
             the address of `buf`; the answer is the kernel's word and the buffer after the call. The world lock of a run
             on several OS threads lives beside it.
-/
namespace Gabbro.Stage0

@[extern "gabbro_stage0_syscall"]
opaque roherSyscall (nr a0 a1 a2 a3 a4 a5 : UInt64) (buf : ByteArray) (which : UInt8) : IO (UInt64 × ByteArray)

/-- Take the world lock (a futex word, `c/syscall.c`). -/
@[extern "gabbro_stage0_nimm"] opaque weltNimm : IO Unit

/-- Give the world lock back. -/
@[extern "gabbro_stage0_gib"] opaque weltGib : IO Unit

/-- The number of steps taken so far, as the threads waiting for a step see it. -/
@[extern "gabbro_stage0_generation"] opaque weltGeneration : IO UInt32

/-- Sleep while the generation is still `g`. -/
@[extern "gabbro_stage0_warte"] opaque weltWarte (g : UInt32) : IO Unit

/-- A step was taken: count it and wake every sleeping thread. -/
@[extern "gabbro_stage0_wecke"] opaque weltWecke : IO Unit

end Gabbro.Stage0
