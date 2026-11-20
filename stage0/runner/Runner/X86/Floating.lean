module

public import Runner.Basis.Res

@[expose] public section

namespace Runner.X86

/-- The architectural SIMD register bank, separate from the general registers. -/
inductive Xmm where
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq, Repr

def Xmm.num : Xmm → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

def Xmm.ofNum : Nat → Xmm
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11
  | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

/-- One legacy SSE scalar arithmetic instruction, never an instruction sequence. -/
inductive FPArith where
  | add | sub | mul | div
  deriving DecidableEq, Repr

def FPArith.native : FPArith → FPFormat → NativeFPOp
  | .add, format => .add format | .sub, format => .sub format
  | .mul, format => .mul format | .div, format => .div format

def FPArith.opc : FPArith → Nat
  | .add => 0x58 | .sub => 0x5C | .mul => 0x59 | .div => 0x5E

def FPArith.ofOpc : Nat → Option FPArith
  | 0x58 => some .add | 0x5C => some .sub
  | 0x59 => some .mul | 0x5E => some .div | _ => none

/-- The ordered predicates of CMPSS/CMPSD (legacy immediate values 0, 1 and 2). -/
inductive FPCompare where
  | eq | lt | le
  deriving DecidableEq, Repr

def FPCompare.native : FPCompare → FPFormat → NativeFPOp
  | .eq, format => .eq format | .lt, format => .lt format | .le, format => .le format

def FPCompare.imm : FPCompare → Nat
  | .eq => 0 | .lt => 1 | .le => 2

def FPCompare.ofImm : Nat → Option FPCompare
  | 0 => some .eq | 1 => some .lt | 2 => some .le | _ => none

def FPCompare.test : FPCompare → W → Bool
  | .eq, flags => !flags.getLsbD 2 && flags.getLsbD 6
  | .lt, flags => !flags.getLsbD 2 && flags.getLsbD 0
  | .le, flags => !flags.getLsbD 2 && (flags.getLsbD 0 || flags.getLsbD 6)

end Runner.X86
