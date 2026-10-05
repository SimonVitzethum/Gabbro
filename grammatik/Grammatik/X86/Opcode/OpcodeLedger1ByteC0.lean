/-
  File:      Grammatik/X86/OpcodeLedger1ByteC0.lean
  Subject:   Opcode ledger for one-byte opcodes C0-FF (lane 1339).

  Region C0-FF of the x86-64 opcode map (Intel SDM Vol 2 Appendix A;
  snapshot `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  edition 325462-093US): every primary opcode byte, group opcodes
  expanded by ModRM.reg extension. Statuses over the accepted
  decoder chain (`kapDecode` in `HwKapsteinDecoder.lean`) and the
  named family decoders below. No AMD manual is in the clone, so no
  AMD provenance is claimed (rule 17); alias facts (/6, /1) are
  Intel-documented and cited in CUTS.
-/
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.Befehle.Arithmetik.ShiftCodec
import Grammatik.X86.Befehle.Kompakt.CompactForms
import Grammatik.X86.Befehle.Kontrolle.IndirectControlHardwareForms
import Grammatik.X86.Befehle.Ganzzahl.IntCarryForms
import Grammatik.X86.Hw.Grundlage.DeviceHardwareForms
import Grammatik.X86.Befehle.Arithmetik.MulDivWidthHardwareForms
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloatCodec
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat32HardwareForms
import Grammatik.X86.TSO.Verriegelt.LockedInstructionExecution
import Grammatik.X86.Befehle.Vektor.Avx2Join
import Grammatik.X86.Kern.Codec

namespace Gabbro.Grammatik.X86.LedgerC0

/-- Ledger status of one opcode row. -/
inductive LStatus
  | modelliert
  | zurueckgestellt
  | verweigert
  | ungueltig64
  | fehlt
  deriving DecidableEq, Repr

/-- One ledger row: primary opcode byte, optional ModRM.reg
    extension for group opcodes, mnemonic, status, the Lean
    module that models it, and a one-line reason. -/
structure LEintrag where
  opcode : Nat
  ext : Option Nat
  mnemonik : String
  status : LStatus
  familie : String
  grund : String
  deriving DecidableEq, Repr

/-- Ledger rows C0-CF: Group 2 byte/word shifts (C0/C1 x8)
    and the miscellaneous opcodes C2-CF. -/
def tabelleC0 : List LEintrag :=
  [ ⟨192, some 0, "ROL Eb,Ib", .fehlt, "", "byte rotate left in crypto/bit code; no family decodes C0"⟩,
    ⟨192, some 1, "ROR Eb,Ib", .fehlt, "", "byte rotate right in crypto/bit code; no family decodes C0"⟩,
    ⟨192, some 2, "RCL Eb,Ib", .zurueckgestellt, "", "rotate through carry on bytes: valid, rare in compiler output"⟩,
    ⟨192, some 3, "RCR Eb,Ib", .zurueckgestellt, "", "rotate through carry on bytes: valid, rare in compiler output"⟩,
    ⟨192, some 4, "SHL Eb,Ib", .fehlt, "", "shlb $imm is emitted for 8-bit shifts; no family decodes C0"⟩,
    ⟨192, some 5, "SHR Eb,Ib", .fehlt, "", "shrb $imm is emitted for 8-bit shifts; no family decodes C0"⟩,
    ⟨192, some 6, "SHL Eb,Ib (/6 alias of /4)", .fehlt, "", "Intel SDM alias of /4; no family decodes C0"⟩,
    ⟨192, some 7, "SAR Eb,Ib", .fehlt, "", "sarb $imm is emitted for 8-bit shifts; no family decodes C0"⟩,
    ⟨193, some 0, "ROL Ev,Ib", .fehlt, "", "rotate idioms lower to rol; ShiftCodec covers only C1 /4,/5,/7"⟩,
    ⟨193, some 1, "ROR Ev,Ib", .fehlt, "", "rotate idioms lower to ror; ShiftCodec covers only C1 /4,/5,/7"⟩,
    ⟨193, some 2, "RCL Ev,Ib", .zurueckgestellt, "", "rotate through carry: valid, rare in compiler output"⟩,
    ⟨193, some 3, "RCR Ev,Ib", .zurueckgestellt, "", "rotate through carry: valid, rare in compiler output"⟩,
    ⟨193, some 4, "SHL Ev,Ib", .modelliert, "ShiftCodec.lean", "REX.W reg-direct row; memory and 16/32-bit rows refused"⟩,
    ⟨193, some 5, "SHR Ev,Ib", .modelliert, "ShiftCodec.lean", "REX.W reg-direct row; memory and 16/32-bit rows refused"⟩,
    ⟨193, some 6, "SHL Ev,Ib (/6 alias of /4)", .verweigert, "ShiftCodec.lean", "silicon SHL alias refused by the ShiftCodec digit whitelist"⟩,
    ⟨193, some 7, "SAR Ev,Ib", .modelliert, "ShiftCodec.lean", "REX.W reg-direct row; memory and 16/32-bit rows refused"⟩,
    ⟨194, none, "RET imm16", .fehlt, "", "ret imm16 stack cleanup: common in 32-bit stdcall, present in 64-bit"⟩,
    ⟨195, none, "RET", .modelliert, "Codec.lean", "pilot decode row"⟩,
    ⟨196, none, "VEX3 prefix (legacy LES invalid in 64-bit)", .modelliert, "Avx2Join.lean", "pinned VEX.256 rows; legacy LES is invalid in 64-bit mode"⟩,
    ⟨197, none, "VEX2 prefix (legacy LDS invalid in 64-bit)", .fehlt, "", "no VEX2 row modeled; VEX-encoded SSE is very common in modern output"⟩,
    ⟨198, none, "MOV Eb,Ib", .fehlt, "", "movb $imm: very common; no family decodes C6"⟩,
    ⟨199, none, "MOV Ev,Iz", .modelliert, "CompactForms.lean", "REX.W MOV r/m64,imm32 row; bare 16/32-bit rows refused"⟩,
    ⟨200, none, "ENTER imm16,imm8", .zurueckgestellt, "", "enter: valid, essentially never emitted"⟩,
    ⟨201, none, "LEAVE", .fehlt, "", "leave: common with frame pointers (-O0, kernels)"⟩,
    ⟨202, none, "RETF imm16", .zurueckgestellt, "", "far return: OS-only, rare"⟩,
    ⟨203, none, "RETF", .zurueckgestellt, "", "far return: OS-only, rare"⟩,
    ⟨204, none, "INT3", .fehlt, "", "int3: __builtin_trap and debugger traps; common"⟩,
    ⟨205, none, "INT ib", .fehlt, "", "int vector: OS handlers and legacy syscalls"⟩,
    ⟨206, none, "INTO", .ungueltig64, "", "overflow trap: invalid in 64-bit mode"⟩,
    ⟨207, none, "IRET", .fehlt, "", "iret: OS interrupt return; machine step exists, no byte decode"⟩ ]

/-- Ledger rows D0-DF: Group 2 shifts by 1 / by CL (D0-D3 x8),
    XLAT, and the x87 escapes D8-DF. -/
def tabelleD : List LEintrag :=
  [ ⟨208, some 0, "ROL Eb,1", .fehlt, "", "rotate by one on bytes; no family decodes D0"⟩,
    ⟨208, some 1, "ROR Eb,1", .fehlt, "", "rotate by one on bytes; no family decodes D0"⟩,
    ⟨208, some 2, "RCL Eb,1", .zurueckgestellt, "", "rotate through carry on bytes: valid, rare"⟩,
    ⟨208, some 3, "RCR Eb,1", .zurueckgestellt, "", "rotate through carry on bytes: valid, rare"⟩,
    ⟨208, some 4, "SHL Eb,1", .fehlt, "", "byte shift by one; no family decodes D0"⟩,
    ⟨208, some 5, "SHR Eb,1", .fehlt, "", "byte shift by one; no family decodes D0"⟩,
    ⟨208, some 6, "SHL Eb,1 (/6 alias of /4)", .fehlt, "", "Intel SDM alias of /4; no family decodes D0"⟩,
    ⟨208, some 7, "SAR Eb,1", .fehlt, "", "byte shift by one; no family decodes D0"⟩,
    ⟨209, some 0, "ROL Ev,1", .fehlt, "", "rotate by one; ShiftCodec covers no D1 row"⟩,
    ⟨209, some 1, "ROR Ev,1", .fehlt, "", "rotate by one; ShiftCodec covers no D1 row"⟩,
    ⟨209, some 2, "RCL Ev,1", .zurueckgestellt, "", "rotate through carry: valid, rare"⟩,
    ⟨209, some 3, "RCR Ev,1", .zurueckgestellt, "", "rotate through carry: valid, rare"⟩,
    ⟨209, some 4, "SHL Ev,1", .fehlt, "", "shl $1 64-bit: strength-reduced times two, very common; not covered"⟩,
    ⟨209, some 5, "SHR Ev,1", .fehlt, "", "shr $1 64-bit: strength-reduced halve, common; not covered"⟩,
    ⟨209, some 6, "SHL Ev,1 (/6 alias of /4)", .fehlt, "", "Intel SDM alias of /4; ShiftCodec covers no D1 row"⟩,
    ⟨209, some 7, "SAR Ev,1", .fehlt, "", "sar $1 64-bit: signed halve, common; not covered"⟩,
    ⟨210, some 0, "ROL Eb,CL", .fehlt, "", "variable byte rotate in crypto; no family decodes D2"⟩,
    ⟨210, some 1, "ROR Eb,CL", .fehlt, "", "variable byte rotate in crypto; no family decodes D2"⟩,
    ⟨210, some 2, "RCL Eb,CL", .zurueckgestellt, "", "rotate through carry on bytes: valid, rare"⟩,
    ⟨210, some 3, "RCR Eb,CL", .zurueckgestellt, "", "rotate through carry on bytes: valid, rare"⟩,
    ⟨210, some 4, "SHL Eb,CL", .fehlt, "", "variable 8-bit shift; no family decodes D2"⟩,
    ⟨210, some 5, "SHR Eb,CL", .fehlt, "", "variable 8-bit shift; no family decodes D2"⟩,
    ⟨210, some 6, "SHL Eb,CL (/6 alias of /4)", .fehlt, "", "Intel SDM alias of /4; no family decodes D2"⟩,
    ⟨210, some 7, "SAR Eb,CL", .fehlt, "", "variable 8-bit shift; no family decodes D2"⟩,
    ⟨211, some 0, "ROL Ev,CL", .fehlt, "", "variable rotate; ShiftCodec covers only D3 /4,/5,/7"⟩,
    ⟨211, some 1, "ROR Ev,CL", .fehlt, "", "variable rotate; ShiftCodec covers only D3 /4,/5,/7"⟩,
    ⟨211, some 2, "RCL Ev,CL", .zurueckgestellt, "", "rotate through carry: valid, rare"⟩,
    ⟨211, some 3, "RCR Ev,CL", .zurueckgestellt, "", "rotate through carry: valid, rare"⟩,
    ⟨211, some 4, "SHL Ev,CL", .modelliert, "ShiftCodec.lean", "REX.W reg-direct row"⟩,
    ⟨211, some 5, "SHR Ev,CL", .modelliert, "ShiftCodec.lean", "REX.W reg-direct row"⟩,
    ⟨211, some 6, "SHL Ev,CL (/6 alias of /4)", .verweigert, "ShiftCodec.lean", "silicon SHL alias refused by the ShiftCodec digit whitelist"⟩,
    ⟨211, some 7, "SAR Ev,CL", .modelliert, "ShiftCodec.lean", "REX.W reg-direct row"⟩,
    ⟨212, none, "AAM", .ungueltig64, "", "ASCII adjust: invalid in 64-bit mode"⟩,
    ⟨213, none, "AAD", .ungueltig64, "", "ASCII adjust: invalid in 64-bit mode"⟩,
    ⟨214, none, "SALC", .ungueltig64, "", "set AL from carry: invalid in 64-bit mode"⟩,
    ⟨215, none, "XLAT", .zurueckgestellt, "", "table translate: valid, rare"⟩,
    ⟨216, none, "FADD/FMUL/FCOM x87", .zurueckgestellt, "", "x87 escape D8: valid, legacy; compilers do not emit"⟩,
    ⟨217, none, "FLD/FST x87", .zurueckgestellt, "", "x87 escape D9: valid, legacy; compilers do not emit"⟩,
    ⟨218, none, "FIADD/FIxx x87", .zurueckgestellt, "", "x87 escape DA: valid, legacy; compilers do not emit"⟩,
    ⟨219, none, "FILD/FIST x87", .zurueckgestellt, "", "x87 escape DB: valid, legacy; compilers do not emit"⟩,
    ⟨220, none, "FADD/FDIV x87", .zurueckgestellt, "", "x87 escape DC: valid, legacy; compilers do not emit"⟩,
    ⟨221, none, "FLD/FUCOM x87", .zurueckgestellt, "", "x87 escape DD: valid, legacy; compilers do not emit"⟩,
    ⟨222, none, "FIADD/FSUB x87", .zurueckgestellt, "", "x87 escape DE: valid, legacy; compilers do not emit"⟩,
    ⟨223, none, "FILD/FISTP x87", .zurueckgestellt, "", "x87 escape DF: valid, legacy; compilers do not emit"⟩ ]

/-- Ledger rows E0-EF: LOOP/JRCXZ, ports, CALL/JMP, INT. -/
def tabelleE : List LEintrag :=
  [ ⟨224, none, "LOOPNE", .zurueckgestellt, "", "loop: valid, essentially never emitted"⟩,
    ⟨225, none, "LOOPE", .zurueckgestellt, "", "loop: valid, essentially never emitted"⟩,
    ⟨226, none, "LOOP", .zurueckgestellt, "", "loop: valid, essentially never emitted"⟩,
    ⟨227, none, "JRCXZ", .zurueckgestellt, "", "jrcxz: valid, rare (string routines)"⟩,
    ⟨228, none, "IN AL,imm8", .modelliert, "DeviceHardwareForms.lean", "port read, immediate port"⟩,
    ⟨229, none, "IN eAX,imm8", .modelliert, "DeviceHardwareForms.lean", "port read, immediate port"⟩,
    ⟨230, none, "OUT imm8,AL", .modelliert, "DeviceHardwareForms.lean", "port write, immediate port"⟩,
    ⟨231, none, "OUT imm8,eAX", .modelliert, "DeviceHardwareForms.lean", "port write, immediate port"⟩,
    ⟨232, none, "CALL rel32", .modelliert, "Codec.lean", "pilot decode row"⟩,
    ⟨233, none, "JMP rel32", .modelliert, "Codec.lean", "pilot decode row"⟩,
    ⟨234, none, "JMP far", .ungueltig64, "", "far jump: invalid in 64-bit mode"⟩,
    ⟨235, none, "JMP rel8", .modelliert, "CompactForms.lean", "short jump row"⟩,
    ⟨236, none, "IN AL,DX", .modelliert, "DeviceHardwareForms.lean", "port read, DX port"⟩,
    ⟨237, none, "IN eAX,DX", .modelliert, "DeviceHardwareForms.lean", "port read, DX port"⟩,
    ⟨238, none, "OUT DX,AL", .modelliert, "DeviceHardwareForms.lean", "port write, DX port"⟩,
    ⟨239, none, "OUT DX,eAX", .modelliert, "DeviceHardwareForms.lean", "port write, DX port"⟩ ]

/-- Ledger rows F0-FF: LOCK, INT1, string prefixes, HLT/CMC,
    Group 3 byte/word (F6/F7 x8), flags, Group 4/5 (FE/FF x8). -/
def tabelleF : List LEintrag :=
  [ ⟨240, none, "LOCK prefix", .modelliert, "LockedInstructionExecution.lean", "LOCK-prefixed XADD/CMPXCHG/MFENCE rows; bare F0 is truncation"⟩,
    ⟨241, none, "INT1", .fehlt, "", "int1: debugger and kernel use"⟩,
    ⟨242, none, "REPNE/XACQUIRE prefix", .modelliert, "ScalarFloatCodec.lean", "F2 0F scalar-double rows (MOVSD/ADDSD, low regs)"⟩,
    ⟨243, none, "REP/REPE prefix", .modelliert, "ScalarFloat32HardwareForms.lean", "F3 0F scalar-single rows (ADDSS and kin, low regs)"⟩,
    ⟨244, none, "HLT", .fehlt, "", "hlt: OS idle loop; common in kernels"⟩,
    ⟨245, none, "CMC", .zurueckgestellt, "", "complement carry: valid, rare"⟩,
    ⟨246, some 0, "TEST Eb,Ib", .verweigert, "MulDivWidthHardwareForms.lean", "byte TEST refused by decodeWd by design (word widths only); testb is common"⟩,
    ⟨246, some 1, "TEST Eb,Ib (/1 alias of /0)", .verweigert, "MulDivWidthHardwareForms.lean", "Intel SDM alias of /0; byte Group 3 refused by decodeWd"⟩,
    ⟨246, some 2, "NOT Eb", .verweigert, "MulDivWidthHardwareForms.lean", "byte Group 3 refused by decodeWd by design (word widths only)"⟩,
    ⟨246, some 3, "NEG Eb", .verweigert, "MulDivWidthHardwareForms.lean", "byte Group 3 refused by decodeWd by design (word widths only)"⟩,
    ⟨246, some 4, "MUL Eb", .verweigert, "MulDivWidthHardwareForms.lean", "byte Group 3 refused by decodeWd by design (word widths only)"⟩,
    ⟨246, some 5, "IMUL Eb", .verweigert, "MulDivWidthHardwareForms.lean", "byte Group 3 refused by decodeWd by design (word widths only)"⟩,
    ⟨246, some 6, "DIV Eb", .verweigert, "MulDivWidthHardwareForms.lean", "byte Group 3 refused by decodeWd by design (word widths only)"⟩,
    ⟨246, some 7, "IDIV Eb", .verweigert, "MulDivWidthHardwareForms.lean", "byte Group 3 refused by decodeWd by design (word widths only)"⟩,
    ⟨247, some 0, "TEST Ev,Iz", .verweigert, "MulDivWidthHardwareForms.lean", "no TEST row in WdBefehl; test $imm is common, revisit"⟩,
    ⟨247, some 1, "TEST Ev,Iz (/1 alias of /0)", .verweigert, "MulDivWidthHardwareForms.lean", "Intel SDM alias of /0; no TEST row in WdBefehl"⟩,
    ⟨247, some 2, "NOT Ev", .verweigert, "MulDivWidthHardwareForms.lean", "no NOT row in WdBefehl"⟩,
    ⟨247, some 3, "NEG Ev", .verweigert, "MulDivWidthHardwareForms.lean", "no NEG row in WdBefehl; neg is common, revisit"⟩,
    ⟨247, some 4, "MUL Ev", .modelliert, "MulDivWidthHardwareForms.lean", "bare 32-bit and REX.W 64-bit rows"⟩,
    ⟨247, some 5, "IMUL Ev", .verweigert, "MulDivWidthHardwareForms.lean", "no one-operand IMUL row in WdBefehl (only two/three-operand forms)"⟩,
    ⟨247, some 6, "DIV Ev", .modelliert, "MulDivWidthHardwareForms.lean", "bare 32-bit and REX.W 64-bit rows"⟩,
    ⟨247, some 7, "IDIV Ev", .modelliert, "MulDivWidthHardwareForms.lean", "bare 32-bit and REX.W 64-bit rows"⟩,
    ⟨248, none, "CLC", .zurueckgestellt, "", "clear carry: valid, rare"⟩,
    ⟨249, none, "STC", .zurueckgestellt, "", "set carry: valid, rare"⟩,
    ⟨250, none, "CLI", .fehlt, "", "cli: OS interrupt masking; common in kernels"⟩,
    ⟨251, none, "STI", .fehlt, "", "sti: OS interrupt masking; common in kernels"⟩,
    ⟨252, none, "CLD", .fehlt, "", "cld: string-op setup in boot and libc code"⟩,
    ⟨253, none, "STD", .fehlt, "", "std: reverse string ops; rare but real"⟩,
    ⟨254, some 0, "INC Eb", .modelliert, "IntCarryForms.lean", "Group 4 byte row"⟩,
    ⟨254, some 1, "DEC Eb", .modelliert, "IntCarryForms.lean", "Group 4 byte row"⟩,
    ⟨254, some 2, "Group 4 /2", .verweigert, "IntCarryForms.lean", "invalid extension (#UD row); chain refuses"⟩,
    ⟨254, some 3, "Group 4 /3", .verweigert, "IntCarryForms.lean", "invalid extension (#UD row); chain refuses"⟩,
    ⟨254, some 4, "Group 4 /4", .verweigert, "IntCarryForms.lean", "invalid extension (#UD row); chain refuses"⟩,
    ⟨254, some 5, "Group 4 /5", .verweigert, "IntCarryForms.lean", "invalid extension (#UD row); chain refuses"⟩,
    ⟨254, some 6, "Group 4 /6", .verweigert, "IntCarryForms.lean", "invalid extension (#UD row); chain refuses"⟩,
    ⟨254, some 7, "Group 4 /7", .verweigert, "IntCarryForms.lean", "invalid extension (#UD row); chain refuses"⟩,
    ⟨255, some 0, "INC Ev", .modelliert, "IntCarryForms.lean", "Group 5 row (REX.W 64-bit and byte/word rows)"⟩,
    ⟨255, some 1, "DEC Ev", .modelliert, "IntCarryForms.lean", "Group 5 row (REX.W 64-bit and memory rows)"⟩,
    ⟨255, some 2, "CALL Ev", .modelliert, "IndirectControlHardwareForms.lean", "register and memory indirect call rows"⟩,
    ⟨255, some 3, "CALLF Ep", .zurueckgestellt, "", "far call: OS-only, rare"⟩,
    ⟨255, some 4, "JMP Ev", .modelliert, "IndirectControlHardwareForms.lean", "register and memory indirect jump rows"⟩,
    ⟨255, some 5, "JMPF Ep", .zurueckgestellt, "", "far jump: OS-only, rare"⟩,
    ⟨255, some 6, "PUSH Ev", .fehlt, "", "push r/m64: indirect push is real but unmodeled"⟩,
    ⟨255, some 7, "Group 5 /7", .verweigert, "IndirectControlHardwareForms.lean", "invalid extension (#UD row); chain refuses"⟩ ]

/-- The full C0-FF ledger: every primary opcode byte exactly once,
    group opcodes expanded by extension. -/
def tabelleC0FF : List LEintrag :=
  tabelleC0 ++ tabelleD ++ tabelleE ++ tabelleF

/-! ## Witnesses: every `modelliert` row decodes through its family.

    Each theorem below reuses one accepted pin or round trip, never
    re-decided. -/

/-- C1 /4: `shl rax, 1` decodes through the shift family. -/
theorem lmod_C1_4 :
    decodeShift [natByte 72, natByte 193, natByte 224, natByte 1] =
      some (((.imm .shl .rax 1) : ShiftForm), []) :=
  pin_shift_imm_rax_dekode

/-- D3 /7: `sar rcx, cl` decodes through the shift family. -/
theorem lmod_D3_7 :
    decodeShift [natByte 72, natByte 211, natByte 249] =
      some (((.cl .sar .rcx) : ShiftForm), []) :=
  pin_shift_cl_rcx_dekode

/-- F0: LOCK XADD decodes through the LOCK family. -/
theorem lmod_F0 : decodeLock pinXadd =
    some (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9, []) :=
  pin_lock_xadd_decodiert

/-- C4: the pinned VEX.256 row runs through the capstone chain. -/
theorem lmod_C4 :
    kapDecode kapW_avx2 =
      some (KapDekodiert.avx2
        ⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩, []) :=
  kapKette_avx2

/-- FE /0: `INC Eb` decodes through the carry family. -/
theorem lmod_FE0 :
    decodeCarry [natByte 254, natByte 192] =
      some (.reg ⟨.incReg .b8 .rax, 2⟩, []) :=
  pin_decode_incReg8

/-- FF /0: REX.W `INC Ev` decodes through the carry family. -/
theorem lmod_FF0 :
    decodeCarry [natByte 72, natByte 255, natByte 192] =
      some (.reg ⟨.incReg .b64 .rax, 3⟩, []) :=
  pin_decode_incReg64

/-- FF /1: `DEC Ev` with a memory destination decodes. -/
theorem lmod_FF1mem :
    decodeCarry [natByte 255, natByte 9] =
      some (.mem ⟨.dec, .b32, true, 9, 1, [], 2⟩, []) :=
  pin_decode_decMem

/-- F3: scalar-single ADDSS decodes through the s32 family. -/
theorem lmod_F3 :
    s32Decode kapW_s32 =
      some (⟨.addssRR .xmm2 .xmm3,
        (s32EncodeAddssRR .xmm2 .xmm3).length⟩, []) :=
  kapW_s32_akzeptiert

/-- EB: short JMP decodes through the compact family. -/
theorem lmod_EB (rel : BitVec 8) :
    decodeC (encodeC (.jump8 rel) ++ []) =
      some (⟨.jump8 rel, (encodeC (.jump8 rel)).length⟩, []) :=
  roundtripC_jump8 rel []

/-- FF /2: register-indirect CALL decodes through the indirect family. -/
theorem lmod_FF2 :
    decodeIndirekt (encodeIndReg true .rax ++ []) =
      some (((.callReg .rax (2 + regHigh .rax))), []) :=
  roundtrip_indReg_call .rax []

/-- FF /4: register-indirect JMP decodes through the indirect family. -/
theorem lmod_FF4 :
    decodeIndirekt (encodeIndReg false .rax ++ []) =
      some (((.jmpReg .rax (2 + regHigh .rax))), []) :=
  roundtrip_indReg_jmp .rax []

/-- C3: RET decodes through the pilot. -/
theorem lmod_C3 :
    decode (encode .ret ++ []) =
      some (⟨.ret, (encode .ret).length⟩, []) :=
  roundtrip_ret []

/-- C1 /5: `shr rax, 1` decodes through the shift family. -/
theorem lmod_C1_5 :
    decodeShift [natByte 72, natByte 193, natByte 232, natByte 1] =
      some (((.imm .shr .rax 1) : ShiftForm), []) := by
  decide

/-- C1 /7: `sar rax, 1` decodes through the shift family. -/
theorem lmod_C1_7 :
    decodeShift [natByte 72, natByte 193, natByte 248, natByte 1] =
      some (((.imm .sar .rax 1) : ShiftForm), []) := by
  decide

/-- D3 /4: `shl rax, cl` decodes through the shift family. -/
theorem lmod_D3_4 :
    decodeShift [natByte 72, natByte 211, natByte 224] =
      some (((.cl .shl .rax) : ShiftForm), []) := by
  decide

/-- D3 /5: `shr rax, cl` decodes through the shift family. -/
theorem lmod_D3_5 :
    decodeShift [natByte 72, natByte 211, natByte 232] =
      some (((.cl .shr .rax) : ShiftForm), []) := by
  decide

/-- C7: REX.W `MOV r/m64, imm32` decodes through the compact family. -/
theorem lmod_C7 :
    decodeC [natByte 72, natByte 199, natByte 192, natByte 1,
      natByte 0, natByte 0, natByte 0] =
      some ((⟨.movImm32Sx .rax (BitVec.ofNat 32 1), 7⟩
        : CompactDecodiert), []) := by
  decide

/-- E8: CALL rel32 decodes through the pilot. -/
theorem lmod_E8 :
    decode [natByte 232, natByte 0, natByte 0, natByte 0, natByte 0] =
      some ((⟨.call32 (BitVec.ofNat 32 0), 5⟩ : Decodiert), []) := by
  decide

/-- E9: JMP rel32 decodes through the pilot. -/
theorem lmod_E9 :
    decode [natByte 233, natByte 0, natByte 0, natByte 0, natByte 0] =
      some ((⟨.jump32 (BitVec.ofNat 32 0), 5⟩ : Decodiert), []) := by
  decide

/-- E4: IN AL,imm8 decodes through the port family. -/
theorem lmod_E4 :
    decodeIo [natByte 228, natByte 96] =
      some ((⟨⟨.ein, .p8, .imm 96⟩, 2⟩ : IoDec), []) := by
  decide

/-- E5: IN eAX,imm8 decodes through the port family. -/
theorem lmod_E5 :
    decodeIo [natByte 229, natByte 96] =
      some ((⟨⟨.ein, .p32, .imm 96⟩, 2⟩ : IoDec), []) := by
  decide

/-- E6: OUT imm8,AL decodes through the port family. -/
theorem lmod_E6 :
    decodeIo [natByte 230, natByte 96] =
      some ((⟨⟨.aus, .p8, .imm 96⟩, 2⟩ : IoDec), []) := by
  decide

/-- E7: OUT imm8,eAX decodes through the port family. -/
theorem lmod_E7 :
    decodeIo [natByte 231, natByte 96] =
      some ((⟨⟨.aus, .p32, .imm 96⟩, 2⟩ : IoDec), []) := by
  decide

/-- EC: IN AL,DX decodes through the port family. -/
theorem lmod_EC :
    decodeIo [natByte 236] =
      some ((⟨⟨.ein, .p8, .dx⟩, 1⟩ : IoDec), []) := by
  decide

/-- ED: IN eAX,DX decodes through the port family. -/
theorem lmod_ED :
    decodeIo [natByte 237] =
      some ((⟨⟨.ein, .p32, .dx⟩, 1⟩ : IoDec), []) := by
  decide

/-- EE: OUT DX,AL decodes through the port family. -/
theorem lmod_EE :
    decodeIo [natByte 238] =
      some ((⟨⟨.aus, .p8, .dx⟩, 1⟩ : IoDec), []) := by
  decide

/-- EF: OUT DX,eAX decodes through the port family. -/
theorem lmod_EF :
    decodeIo [natByte 239] =
      some ((⟨⟨.aus, .p32, .dx⟩, 1⟩ : IoDec), []) := by
  decide

/-- F2: scalar-double MOVSD decodes through the fp family. -/
theorem lmod_F2 :
    fpDecode (fpEncodeMovsdRR .xmm0 .xmm1 ++ []) =
      some (⟨.movsdRR .xmm0 .xmm1,
        (fpEncodeMovsdRR .xmm0 .xmm1).length⟩, []) :=
  fpRoundtrip_movsdRR .xmm0 .xmm1 [] (by decide) (by decide)

/-- F7 /4: 32-bit MUL decodes through the width family. -/
theorem lmod_F7_4 :
    decodeWd [natByte 247, natByte 225] =
      some ((⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩
        : WdDecodiert), []) :=
  pin_wdmul_ecx_dekode

/-- F7 /4: REX.W 64-bit MUL decodes through the muldiv family. -/
theorem lmod_F7_4_64 :
    decodeMulDiv [natByte 72, natByte 247, natByte 225] =
      some ((⟨.mulRax .rcx, 3⟩ : MulDivDecodiert), []) :=
  pin_mulRax_rcx_dekode

/-- F7 /6: REX.W 64-bit DIV decodes through the muldiv family. -/
theorem lmod_F7_6 :
    decodeMulDiv [natByte 73, natByte 247, natByte 240] =
      some ((⟨.divRax .r8, 3⟩ : MulDivDecodiert), []) :=
  pin_divRax_r8_dekode

/-- F7 /7: REX.W 64-bit IDIV decodes through the muldiv family. -/
theorem lmod_F7_7 :
    decodeMulDiv [natByte 72, natByte 247, natByte 249] =
      some ((⟨.idivRax .rcx, 3⟩ : MulDivDecodiert), []) :=
  pin_idivRax_rcx_dekode

/-- FE /1: `DEC Eb` decodes through the carry family. -/
theorem lmod_FE1 :
    decodeCarry [natByte 254, natByte 200] =
      some (.reg ⟨.decReg .b8 .rax, 2⟩, []) := by
  decide

/-- FF /1: REX.W `DEC Ev` decodes through the carry family. -/
theorem lmod_FF1 :
    decodeCarry [natByte 72, natByte 255, natByte 200] =
      some (.reg ⟨.decReg .b64 .rax, 3⟩, []) := by
  decide

/-! ## Refusals: every `verweigert` row is refused by the chain,
    and every `ungueltig64` byte decodes to nothing. -/

/-- C1 /6: the silicon SHL alias is refused by the chain. -/
theorem lver_C1_6 :
    kapDecode [natByte 72, natByte 193, natByte 240, natByte 1] = none := by
  decide

/-- D3 /6: the silicon SHL alias is refused by the chain. -/
theorem lver_D3_6 :
    kapDecode [natByte 72, natByte 211, natByte 240] = none := by
  decide

/-- F6 /0: byte TEST is refused by the chain. -/
theorem lver_F6_0 :
    kapDecode [natByte 246, natByte 192, natByte 0] = none := by
  decide

/-- F6 /1: byte TEST alias is refused by the chain. -/
theorem lver_F6_1 :
    kapDecode [natByte 246, natByte 200, natByte 0] = none := by
  decide

/-- F6 /2: byte NOT is refused by the chain. -/
theorem lver_F6_2 :
    kapDecode [natByte 246, natByte 208] = none := by
  decide

/-- F6 /3: byte NEG is refused by the chain. -/
theorem lver_F6_3 :
    kapDecode [natByte 246, natByte 216] = none := by
  decide

/-- F6 /4: byte MUL is refused by the chain. -/
theorem lver_F6_4 :
    kapDecode [natByte 246, natByte 224] = none := by
  decide

/-- F6 /5: byte IMUL is refused by the chain. -/
theorem lver_F6_5 :
    kapDecode [natByte 246, natByte 232] = none := by
  decide

/-- F6 /6: byte DIV is refused by the chain. -/
theorem lver_F6_6 :
    kapDecode [natByte 246, natByte 240] = none := by
  decide

/-- F6 /7: byte IDIV is refused by the chain. -/
theorem lver_F6_7 :
    kapDecode [natByte 246, natByte 248] = none := by
  decide

/-- F7 /0: word TEST is refused by the chain. -/
theorem lver_F7_0 :
    kapDecode [natByte 247, natByte 192, natByte 0, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

/-- F7 /1: word TEST alias is refused by the chain. -/
theorem lver_F7_1 :
    kapDecode [natByte 247, natByte 200, natByte 0, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

/-- F7 /2: word NOT is refused by the chain. -/
theorem lver_F7_2 :
    kapDecode [natByte 247, natByte 208] = none := by
  decide

/-- F7 /3: word NEG is refused by the chain. -/
theorem lver_F7_3 :
    kapDecode [natByte 247, natByte 216] = none := by
  decide

/-- F7 /5: one-operand IMUL is refused by the chain. -/
theorem lver_F7_5 :
    kapDecode [natByte 247, natByte 232] = none := by
  decide

/-- FE /2: invalid Group 4 extension is refused by the chain. -/
theorem lver_FE_2 :
    kapDecode [natByte 254, natByte 211] = none := by
  decide

/-- FE /3: invalid Group 4 extension is refused by the chain. -/
theorem lver_FE_3 :
    kapDecode [natByte 254, natByte 219] = none := by
  decide

/-- FE /4: invalid Group 4 extension is refused by the chain. -/
theorem lver_FE_4 :
    kapDecode [natByte 254, natByte 227] = none := by
  decide

/-- FE /5: invalid Group 4 extension is refused by the chain. -/
theorem lver_FE_5 :
    kapDecode [natByte 254, natByte 235] = none := by
  decide

/-- FE /6: invalid Group 4 extension is refused by the chain. -/
theorem lver_FE_6 :
    kapDecode [natByte 254, natByte 243] = none := by
  decide

/-- FE /7: invalid Group 4 extension is refused by the chain. -/
theorem lver_FE_7 :
    kapDecode [natByte 254, natByte 251] = none := by
  decide

/-- FF /7: invalid Group 5 extension is refused by the chain. -/
theorem lver_FF_7 :
    kapDecode [natByte 255, natByte 251] = none := by
  decide

/-- CE (INTO): invalid in 64-bit mode, decodes to nothing. -/
theorem lung_CE : kapDecode [natByte 206] = none := by
  decide

/-- D4 (AAM): invalid in 64-bit mode, decodes to nothing. -/
theorem lung_D4 : kapDecode [natByte 212] = none := by
  decide

/-- D5 (AAD): invalid in 64-bit mode, decodes to nothing. -/
theorem lung_D5 : kapDecode [natByte 213] = none := by
  decide

/-- D6 (SALC): invalid in 64-bit mode, decodes to nothing. -/
theorem lung_D6 : kapDecode [natByte 214] = none := by
  decide

/-- EA (JMP far): invalid in 64-bit mode, decodes to nothing. -/
theorem lung_EA : kapDecode [natByte 234] = none := by
  decide

/-! ## Summary: counts per status and exact-once coverage. -/

/-- 32 ledger rows are modeled. -/
theorem lzahl_modelliert :
    (tabelleC0FF.filter (fun e => e.status == .modelliert)).length = 32 := by
  decide

/-- 22 ledger rows are refused by design. -/
theorem lzahl_verweigert :
    (tabelleC0FF.filter (fun e => e.status == .verweigert)).length = 22 := by
  decide

/-- 5 ledger rows are invalid in 64-bit mode. -/
theorem lzahl_ungueltig64 :
    (tabelleC0FF.filter (fun e => e.status == .ungueltig64)).length = 5 := by
  decide

/-- 42 ledger rows are gaps: real instructions no family models. -/
theorem lzahl_fehlt :
    (tabelleC0FF.filter (fun e => e.status == .fehlt)).length = 42 := by
  decide

/-- 33 ledger rows are deferred: valid but rare or legacy. -/
theorem lzahl_zurueckgestellt :
    (tabelleC0FF.filter
      (fun e => e.status == .zurueckgestellt)).length = 33 := by
  decide

set_option maxRecDepth 10000 in
/-- The ledger holds 134 rows in total. -/
theorem lzahl_gesamt : tabelleC0FF.length = 134 := by
  decide

set_option maxRecDepth 10000 in
/-- Every opcode byte C0-FF appears in the ledger. -/
theorem labdeckung_alle :
    ((List.range 64).map (fun n => n + 192)).all
      (fun n => tabelleC0FF.any (fun e => e.opcode == n)) = true := by
  decide

/-- All-pairs check that no (opcode, extension) pair repeats:
    every later pair differs from the head in the opcode or in the
    extension. (`List.pairwise` does not exist in this toolchain.) -/
def paareVerschieden : List (Nat × Option Nat) → Bool
  | [] => true
  | (o, e) :: rest =>
    rest.all (fun p => p.1 != o || p.2 != e) && paareVerschieden rest

set_option maxRecDepth 10000 in
/-- No (opcode, extension) pair is listed twice. -/
theorem lkein_duplikat :
    paareVerschieden
      (tabelleC0FF.map (fun e => (e.opcode, e.ext))) = true := by
  decide

/- CUTS:
    Proved here, over the Intel SDM snapshot
    `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
    (edition 325462-093US, verified 2026-10-02 per REFERENCES.json):
    - a 134-row ledger over primary opcodes C0-FF, group opcodes
      expanded by ModRM.reg extension (C0/C1/D0-D3/F6/F7/FE/FF x8),
      with the counts 32 modelliert / 22 verweigert / 5 ungueltig64 /
      42 fehlt / 33 zurueckgestellt (all by decide), full coverage of
      bytes 192-255 and no duplicate (opcode, extension) pair;
    - for every modelliert row a canonical witness decoded by the
      named family decoder (accepted pins reused where they exist,
      closed decide evaluations otherwise), including one capstone
      chain witness (lmod_C4 through kapKette_avx2);
    - for every verweigert row a checked chain refusal
      (kapDecode ... = none), including the silicon SHL-alias rows
      C1/6 and D3/6 refused by the ShiftCodec digit whitelist and
      the byte Group 3 rows explicitly refused by decodeWd;
    - for every ungueltig64 row (INTO, AAM, AAD, SALC, far JMP) a
      checked decode-to-nothing.
    Toolchain notes: `set_option maxRecDepth 10000` stands before
    the three whole-table decides; the no-duplicate check is the
    local all-pairs boolean `paareVerschieden` because this
    toolchain has no `List.pairwise`/`List.eraseDup`.
    NOT proved here, and not claimed:
    - no kapDecode-level witness for most modelliert rows: family
      decoders outside the chain (carry, indirect, ports, width,
      scalar FP, LOCK) are not connected to kapDecode, so their
      rows are witnessed at family level only;
    - the fehlt rows are a literature-and-code reading (SDM map vs
      the accepted decoder set), not a proved absence: absence of a
      decoder arm is argued per row in the report, not in Lean;
    - frequency notes in the report (common/rare) are estimates
      from compiler-output knowledge, not measurements;
    - no vendor-difference row was found in C0-FF, so no
      herstellerabhaengig marking was needed; with no AMD manual
      in the clone no AMD fact is claimed either way (rule 17);
    - the Group 2 /6 and Group 3 /1 alias facts are Intel SDM
      text (Appendix AORI note at intel-instruction-reference.txt
      line 207955), cited, not re-proved;
    - no silicon re-check beyond the accepted pins; no W/GX
      bridge; no source, checker, contract, entry, ABI, loader,
      budget or liveness claim.
-/

#print axioms lmod_C1_4
#print axioms lmod_D3_7
#print axioms lmod_F0
#print axioms lmod_C4
#print axioms lmod_FE0
#print axioms lmod_FF0
#print axioms lmod_FF1mem
#print axioms lmod_F3
#print axioms lmod_EB
#print axioms lmod_FF2
#print axioms lmod_FF4
#print axioms lmod_C3
#print axioms lmod_C1_5
#print axioms lmod_C1_7
#print axioms lmod_D3_4
#print axioms lmod_D3_5
#print axioms lmod_C7
#print axioms lmod_E8
#print axioms lmod_E9
#print axioms lmod_E4
#print axioms lmod_E5
#print axioms lmod_E6
#print axioms lmod_E7
#print axioms lmod_EC
#print axioms lmod_ED
#print axioms lmod_EE
#print axioms lmod_EF
#print axioms lmod_F2
#print axioms lmod_F7_4
#print axioms lmod_F7_4_64
#print axioms lmod_F7_6
#print axioms lmod_F7_7
#print axioms lmod_FE1
#print axioms lmod_FF1
#print axioms lver_C1_6
#print axioms lver_D3_6
#print axioms lver_F6_0
#print axioms lver_F6_1
#print axioms lver_F6_2
#print axioms lver_F6_3
#print axioms lver_F6_4
#print axioms lver_F6_5
#print axioms lver_F6_6
#print axioms lver_F6_7
#print axioms lver_F7_0
#print axioms lver_F7_1
#print axioms lver_F7_2
#print axioms lver_F7_3
#print axioms lver_F7_5
#print axioms lver_FE_2
#print axioms lver_FE_3
#print axioms lver_FE_4
#print axioms lver_FE_5
#print axioms lver_FE_6
#print axioms lver_FE_7
#print axioms lver_FF_7
#print axioms lung_CE
#print axioms lung_D4
#print axioms lung_D5
#print axioms lung_D6
#print axioms lung_EA
#print axioms lzahl_modelliert
#print axioms lzahl_verweigert
#print axioms lzahl_ungueltig64
#print axioms lzahl_fehlt
#print axioms lzahl_zurueckgestellt
#print axioms lzahl_gesamt
#print axioms labdeckung_alle
#print axioms lkein_duplikat

end Gabbro.Grammatik.X86.LedgerC0
