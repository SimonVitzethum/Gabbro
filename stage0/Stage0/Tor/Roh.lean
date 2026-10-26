/-
  File:      stage0/Stage0/Tor/Roh.lean
  Subject:   The raw system call: the Lean face of the trampoline `c/syscall.c`. `which < 6` replaces that argument by
             the address of `buf`; the answer is the kernel's word and the buffer after the call.
-/
namespace Gabbro.Stage0

@[extern "gabbro_stage0_syscall"]
opaque roherSyscall (nr a0 a1 a2 a3 a4 a5 : UInt64) (buf : ByteArray) (which : UInt8) : IO (UInt64 × ByteArray)

end Gabbro.Stage0
