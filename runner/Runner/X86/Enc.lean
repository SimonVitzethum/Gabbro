module
public import Runner.X86.Ins
@[expose] public section


/-! # Encoding: the bytes of each instruction form

One encoding per form (`Ins.lean`). `Dec.lean` decodes exactly these; the runner's bytes are `enc` of its
instruction list, and `decode (enc i ++ rest) = some (i, (enc i).length)` is checked for every instruction the
runner contains (`Runner/Prog/`). -/

namespace Runner.X86

def byte (n : Nat) : B := BitVec.ofNat 8 n

def le32 (v : BitVec 32) : List B :=
  [byte v.toNat, byte (v.toNat / 256), byte (v.toNat / 65536), byte (v.toNat / 16777216)]

def rex (w r x b : Nat) : B := byte (0x40 + 8 * w + 4 * r + 2 * x + b)

def modrm (md reg rm : Nat) : B := byte (64 * md + 8 * reg + rm)

/-- `rex? op modrm sib disp32` for a memory operand; `g` is the ModRM reg field (a register or an opcode
    extension), its high bit goes into REX.R. -/
def memEnc (w : Nat) (op : List B) (g : Nat) (m : Addr) : List B :=
  let xi := match m.idx with | none => 0 | some i => i.num / 8
  let il := match m.idx with | none => 4 | some i => i.num % 8
  [rex w (g / 8) xi (m.base.num / 8)] ++ op ++
    [modrm 2 (g % 8) 4, byte (64 * m.sc + 8 * il + m.base.num % 8)] ++ le32 m.disp

/-- `rex op modrm` for a register operand `rm`. -/
def regEnc (w : Nat) (op : List B) (g rm : Nat) : List B :=
  [rex w (g / 8) 0 (rm / 8)] ++ op ++ [modrm 3 (g % 8) (rm % 8)]

def Alu.opc : Alu → Nat
  | .add => 0x01 | .or => 0x09 | .and => 0x21 | .sub => 0x29 | .xor => 0x31 | .cmp => 0x39 | .test => 0x85

/-- The `81 /ext` extension; `test` has none (its immediate form is not in the subset). -/
def Alu.ext : Alu → Nat
  | .add => 0 | .or => 1 | .and => 4 | .sub => 5 | .xor => 6 | .cmp => 7 | .test => 8

def Cond.cc : Cond → Nat
  | .z => 4 | .nz => 5 | .s => 8 | .l => 12 | .b => 2
  | .p => 10 | .np => 11

def _root_.Runner.FPFormat.prefix : FPFormat → B
  | .f32 => byte 0xF3 | .f64 => byte 0xF2

def _root_.Runner.FPFormat.rexWidth : FPFormat → Nat
  | .f32 => 0 | .f64 => 1

def enc : Ins → List B
  | .ld d m => memEnc 1 [byte 0x8B] d.num m
  | .st m s => memEnc 1 [byte 0x89] s.num m
  | .mov d s => regEnc 1 [byte 0x89] s.num d.num
  | .movi d i => regEnc 1 [byte 0xC7] 0 d.num ++ le32 i
  | .ldsx d m => memEnc 1 [byte 0x63] d.num m
  | .ldzx d m => memEnc 1 [byte 0x0F, byte 0xB6] d.num m
  | .zx8 d s => regEnc 1 [byte 0x0F, byte 0xB6] d.num s.num
  | .lea d m => memEnc 1 [byte 0x8D] d.num m
  | .alu o d s => regEnc 1 [byte o.opc] s.num d.num
  | .alui o d i => regEnc 1 [byte 0x81] o.ext d.num ++ le32 i
  | .imul d s => regEnc 1 [byte 0x0F, byte 0xAF] d.num s.num
  | .cqo => [byte 0x48, byte 0x99]
  | .idiv s => regEnc 1 [byte 0xF7] 7 s.num
  | .udiv s => regEnc 1 [byte 0xF7] 6 s.num
  | .shl d => regEnc 1 [byte 0xD3] 4 d.num
  | .shr d => regEnc 1 [byte 0xD3] 5 d.num
  | .set c d => regEnc 0 [byte 0x0F, byte (0x90 + c.cc)] 0 d.num
  | .jmp rel => [byte 0xE9] ++ le32 rel
  | .jcc c rel => [byte 0x0F, byte (0x80 + c.cc)] ++ le32 rel
  | .jmpm m => memEnc 0 [byte 0xFF] 4 m
  | .cmpxchg m s => [byte 0xF0] ++ memEnc 1 [byte 0x0F, byte 0xB1] s.num m
  | .syscall => [byte 0x0F, byte 0x05]
  | .ud2 => [byte 0x0F, byte 0x0B]
  | .movToXmm format d s => [byte 0x66] ++ regEnc format.rexWidth [byte 0x0F, byte 0x6E] d.num s.num
  | .movFromXmm format d s => [byte 0x66] ++ regEnc format.rexWidth [byte 0x0F, byte 0x7E] s.num d.num
  | .scalar kind format d s => [format.prefix] ++ regEnc 0 [byte 0x0F, byte kind.opc] d.num s.num
  | .compareScalar pred format d s =>
    [format.prefix] ++ regEnc 0 [byte 0x0F, byte 0xC2] d.num s.num ++ [byte pred.imm]
  | .fromIntScalar format d s => [format.prefix] ++ regEnc 1 [byte 0x0F, byte 0x2A] d.num s.num
  | .widenScalar d s => [byte 0xF3] ++ regEnc 0 [byte 0x0F, byte 0x5A] d.num s.num
  | .narrowScalar d s => [byte 0xF2] ++ regEnc 0 [byte 0x0F, byte 0x5A] d.num s.num
  | .pxor d s => [byte 0x66] ++ regEnc 0 [byte 0x0F, byte 0xEF] d.num s.num
  | .ldmxcsr m => memEnc 0 [byte 0x0F, byte 0xAE] 2 m
  | .ucomis .f32 d s => regEnc 0 [byte 0x0F, byte 0x2E] d.num s.num
  | .ucomis .f64 d s => [byte 0x66] ++ regEnc 0 [byte 0x0F, byte 0x2E] d.num s.num
  | .truncateScalar format d s => [format.prefix] ++ regEnc 1 [byte 0x0F, byte 0x2C] d.num s.num
  | .cmov c d s => regEnc 1 [byte 0x0F, byte (0x40 + c.cc)] d.num s.num

end Runner.X86

namespace Runner.X86

/-- The operands `enc` can encode: a scale below 4 and no `rsp` index; `test` has no immediate form. -/
def Addr.ok (m : Addr) : Bool := m.sc < 4 && m.idx != some .rsp

def Ins.ok : Ins → Bool
  | .ld _ m | .st m _ | .ldsx _ m | .ldzx _ m | .lea _ m | .jmpm m | .cmpxchg m _ | .ldmxcsr m => m.ok
  | .alui o _ _ => o != .test
  | _ => true

end Runner.X86
