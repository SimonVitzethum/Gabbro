/-
  File:      Grammatik/X86/CompactForms.lean
  Subject:   The performance-floor compact encodings of DIRECT-COMPILER-DESIGN.md
             §2B as ONE new instruction family over the canonical machine.

  New family (own `CompactBefehl` type, own `schrittC`/codec, following the
  `MulDiv.lean`/`MulDivCodec.lean` and `ShiftLogic.lean`/`ShiftCodec.lean`
  pattern): zero/sign-extending 32-bit immediate MOV, imm8/imm32 ALU
  (ADD/SUB/CMP/AND/OR/XOR), disp8/disp0 base-relative load/store, and
  rel8 short jump/conditional jump. Steps over the REAL canonical `Zustand`
  reusing `regSet`/`ripNach`/`schrittRegister`/`effAddr`-style helpers from
  `Ausfuehrung.lean`, the REAL `add64`/`sub64`/`xor64` from `Wort.lean` and
  `and64`/`or64` from `Ganzzahl.lean`, and the REAL permission-checked
  `read64`/`write64` from `Speicher.lean`. This file adds NO `Befehl`
  constructor and changes NO `schritt` equation: the 14 pilot forms are
  untouched, exactly like the MulDiv/Shift extension pattern. Wiring into
  `Befehl`/`schritt`/the unified decoder stays OPEN with the Typen/decoder
  owners (DIRECT-COMPILER-DESIGN.md §2B lists every row as PROPOSED/OPEN).

  No source correspondence, no TSO bridge, no branch-relaxation layout and
  no hardware verification is claimed here; see the CUTS block.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec

namespace Gabbro.Grammatik.X86

/-! ## 1. The ten compact forms. -/

/-- The six imm8/imm32 ALU operations this family lowers (Group 1
    extension digits: ADD=0, OR=1, AND=4, SUB=5, XOR=6, CMP=7; ADC/SBB
    are out of scope, matching the pilot's register forms). -/
inductive AluOp where
  | add | sub | cmp | and' | or' | xor'
  deriving DecidableEq, Repr, Inhabited

/-- The ten PROPOSED compact forms of DESIGN §2B: zero/sign-extending
    32-bit immediate MOV, imm8/imm32 ALU, disp8/disp0 base-relative
    load/store, and rel8 (unconditional/conditional) short jump. -/
inductive CompactBefehl where
  | movImm32Zx (dst : Register) (imm : BitVec 32)
  | movImm32Sx (dst : Register) (imm : BitVec 32)
  | aluImm8 (op : AluOp) (dst : Register) (imm : BitVec 8)
  | aluImm32 (op : AluOp) (dst : Register) (imm : BitVec 32)
  | load64Disp8 (dst base : Register) (disp : BitVec 8)
  | store64Disp8 (base src : Register) (disp : BitVec 8)
  | load64Disp0 (dst base : Register)
  | store64Disp0 (base src : Register)
  | jump8 (rel : BitVec 8)
  | jumpIf8 (cond : Bedingung) (rel : BitVec 8)
  deriving DecidableEq, Repr

/-- Decoded compact-form instruction: operation plus checked length data,
    mirroring `Decodiert`/`MulDivDecodiert`. -/
structure CompactDecodiert where
  befehl : CompactBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-! ## 2. Value and flag dispatch over the REUSED 64-bit operations.

    Every ALU op and every MOV/load/store in this family operates at full
    64-bit width (REX.W where a REX is used at all), so the value and flag
    computation reuses `add64`/`sub64`/`xor64` (`Wort.lean`) and
    `and64`/`or64` (`Ganzzahl.lean`) directly -- no competing redefinition.
    CMP computes SUB's flags and writes no operand, exactly like the pilot
    `cmpReg64`. -/

/-- The computed value of one ALU op (CMP's "value" is never written;
    the routed `sub64` result is carried only for uniform dispatch). -/
def aluWert : AluOp → Wort → Wort → Wort
  | .add, x, y => (add64 x y).1
  | .sub, x, y => (sub64 x y).1
  | .cmp, x, y => (sub64 x y).1
  | .and', x, y => (and64 x y).1
  | .or', x, y => (or64 x y).1
  | .xor', x, y => (xor64 x y).1

/-- The flag snapshot of one ALU op, routed to the REUSED op. -/
def aluFlags : AluOp → Wort → Wort → Flags
  | .add, x, y => (add64 x y).2
  | .sub, x, y => (sub64 x y).2
  | .cmp, x, y => (sub64 x y).2
  | .and', x, y => (and64 x y).2
  | .or', x, y => (or64 x y).2
  | .xor', x, y => (xor64 x y).2

/-- Whether an ALU op writes its destination: every op except CMP. -/
def aluSchreibt : AluOp → Bool
  | .cmp => false
  | _ => true

/-- The dispatch routes every ALU op to its canonical 64-bit op. -/
theorem aluWert_routen (x y : Wort) :
    aluWert .add x y = (add64 x y).1 ∧ aluWert .sub x y = (sub64 x y).1 ∧
    aluWert .and' x y = (and64 x y).1 ∧ aluWert .or' x y = (or64 x y).1 ∧
    aluWert .xor' x y = (xor64 x y).1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Sign extension of the two immediate widths into `Wort`.

    Both reuse `sext`/`dispWort` from `Wort.lean`/`Ausfuehrung.lean`: no
    competing extension is defined here. -/

/-- Sign extension of an 8-bit immediate to a full word (reuses `sext`). -/
def dispWort8 (d : BitVec 8) : Wort := sext .b8 (BitVec.ofNat 64 d.toNat)

/-- Zero extension of a 32-bit immediate to a full word (reuses `zext`,
    which is truncation: the low 32 bits already hold the value). -/
def zextWort32 (d : BitVec 32) : Wort := zext .b32 (BitVec.ofNat 64 d.toNat)

/-! ## 4. Effective addresses for the two memory-displacement widths. -/

/-- Base-plus-disp8 effective address (mirrors `effAddr`, narrower disp). -/
def effAddr8 (s : Zustand) (base : Register) (disp : BitVec 8) : Adresse :=
  s.register base + dispWort8 disp

/-- Base-plus-zero effective address: the base register alone. -/
def effAddr0 (s : Zustand) (base : Register) : Adresse := s.register base

/-! ## 5. The step extension: how the one target semantics grows.

    `schrittC` handles ONLY the ten new forms, reusing `laengeOk`/
    `ripNach`/`regSet`/`schrittRegister` and the dispatch of §2/§3/§4. No
    pilot `schritt` equation is touched. Outcomes stay `Option Zustand`
    like the pilot `schritt`: a failed memory access is an explicit `none`,
    never an invented halt (none of these ten forms traps on hardware). -/

/-- Single compact-form step. -/
def schrittC (d : CompactDecodiert) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .movImm32Zx dst imm =>
      some (schrittRegister s nach s.flags dst (zextWort32 imm))
    | .movImm32Sx dst imm =>
      some (schrittRegister s nach s.flags dst (dispWort imm))
    | .aluImm8 op dst imm =>
      let x := s.register dst
      let y := dispWort8 imm
      let f := aluFlags op x y
      some (if aluSchreibt op then schrittRegister s nach f dst (aluWert op x y)
        else { s with rip := nach, flags := f })
    | .aluImm32 op dst imm =>
      let x := s.register dst
      let y := dispWort imm
      let f := aluFlags op x y
      some (if aluSchreibt op then schrittRegister s nach f dst (aluWert op x y)
        else { s with rip := nach, flags := f })
    | .load64Disp8 dst base disp =>
      match read64 s.speicher (effAddr8 s base disp) with
      | some v => some (schrittRegister s nach s.flags dst v)
      | none => none
    | .store64Disp8 base src disp =>
      match write64 s.speicher (effAddr8 s base disp) (s.register src) with
      | some m => some ({ s with speicher := m, rip := nach })
      | none => none
    | .load64Disp0 dst base =>
      match read64 s.speicher (effAddr0 s base) with
      | some v => some (schrittRegister s nach s.flags dst v)
      | none => none
    | .store64Disp0 base src =>
      match write64 s.speicher (effAddr0 s base) (s.register src) with
      | some m => some ({ s with speicher := m, rip := nach })
      | none => none
    | .jump8 rel => some ({ s with rip := nach + dispWort8 rel })
    | .jumpIf8 cond rel =>
      some ({ s with rip := if bedingung cond s.flags then nach + dispWort8 rel
        else nach })

/-! ## Step equations for the ten new forms.

    Each equation pins the full successor (or explicit refusal); every
    premise is used, mirroring `Ausfuehrung.lean`/`MulDiv.lean`. -/

/-- `movImm32Zx`: the destination holds the zero-extended immediate;
    flags are preserved. -/
theorem schrittC_movImm32Zx (d : CompactDecodiert) (s : Zustand)
    (dst : Register) (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movImm32Zx dst imm) :
    schrittC d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (zextWort32 imm)) := by
  unfold schrittC
  rw [hok, h]

/-- `movImm32Sx`: the destination holds the sign-extended immediate;
    flags are preserved. -/
theorem schrittC_movImm32Sx (d : CompactDecodiert) (s : Zustand)
    (dst : Register) (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movImm32Sx dst imm) :
    schrittC d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (dispWort imm)) := by
  unfold schrittC
  rw [hok, h]

/-- `aluImm8` for a writing op: the destination holds the computed value
    with the REUSED flag snapshot. -/
theorem schrittC_aluImm8_schreibt (d : CompactDecodiert) (s : Zustand)
    (op : AluOp) (dst : Register) (imm : BitVec 8)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .aluImm8 op dst imm)
    (hw : aluSchreibt op = true) :
    schrittC d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (aluFlags op (s.register dst) (dispWort8 imm)) dst
        (aluWert op (s.register dst) (dispWort8 imm))) := by
  unfold schrittC
  simp [hok, h, hw]

/-- `aluImm8` CMP: no operand is written; only flags and RIP move. -/
theorem schrittC_aluImm8_cmp (d : CompactDecodiert) (s : Zustand)
    (dst : Register) (imm : BitVec 8) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .aluImm8 .cmp dst imm) :
    schrittC d s =
      some ({ s with rip := ripNach s.rip d.laenge, flags := aluFlags .cmp (s.register dst) (dispWort8 imm) }) := by
  unfold schrittC
  simp [hok, h, aluSchreibt]

/-- `aluImm32` for a writing op: the destination holds the computed value
    with the REUSED flag snapshot. -/
theorem schrittC_aluImm32_schreibt (d : CompactDecodiert) (s : Zustand)
    (op : AluOp) (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .aluImm32 op dst imm)
    (hw : aluSchreibt op = true) :
    schrittC d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (aluFlags op (s.register dst) (dispWort imm)) dst
        (aluWert op (s.register dst) (dispWort imm))) := by
  unfold schrittC
  simp [hok, h, hw]

/-- `aluImm32` CMP: no operand is written; only flags and RIP move. -/
theorem schrittC_aluImm32_cmp (d : CompactDecodiert) (s : Zustand)
    (dst : Register) (imm : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .aluImm32 .cmp dst imm) :
    schrittC d s =
      some ({ s with rip := ripNach s.rip d.laenge, flags := aluFlags .cmp (s.register dst) (dispWort imm) }) := by
  unfold schrittC
  simp [hok, h, aluSchreibt]

/-- `load64Disp8` success: the word at base plus sign-extended disp8
    lands in the destination; flags are preserved. -/
theorem schrittC_load64Disp8_erfolg (d : CompactDecodiert) (s : Zustand)
    (dst base : Register) (disp : BitVec 8) (v : Wort)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .load64Disp8 dst base disp)
    (hrd : read64 s.speicher (effAddr8 s base disp) = some v) :
    schrittC d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst v) := by
  unfold schrittC
  simp [hok, h, hrd]

/-- `load64Disp8` refusal: a failed read is an explicit step failure. -/
theorem schrittC_load64Disp8_verweigert (d : CompactDecodiert) (s : Zustand)
    (dst base : Register) (disp : BitVec 8) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .load64Disp8 dst base disp)
    (hrd : read64 s.speicher (effAddr8 s base disp) = none) :
    schrittC d s = none := by
  unfold schrittC
  simp [hok, h, hrd]

/-- `store64Disp8` success: memory carries the word; registers and flags
    are kept, RIP advances past the instruction. -/
theorem schrittC_store64Disp8_erfolg (d : CompactDecodiert) (s : Zustand)
    (base src : Register) (disp : BitVec 8) (m : Speicher)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = .store64Disp8 base src disp)
    (hwr : write64 s.speicher (effAddr8 s base disp) (s.register src) =
      some m) :
    schrittC d s =
      some ({ s with speicher := m, rip := ripNach s.rip d.laenge }) := by
  unfold schrittC
  simp [hok, h, hwr]

/-- `store64Disp8` refusal: a failed write is an explicit step failure. -/
theorem schrittC_store64Disp8_verweigert (d : CompactDecodiert) (s : Zustand)
    (base src : Register) (disp : BitVec 8) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .store64Disp8 base src disp)
    (hwr : write64 s.speicher (effAddr8 s base disp) (s.register src) = none) :
    schrittC d s = none := by
  unfold schrittC
  simp [hok, h, hwr]

/-- `load64Disp0` success: the word at the base register lands in the
    destination; flags are preserved. -/
theorem schrittC_load64Disp0_erfolg (d : CompactDecodiert) (s : Zustand)
    (dst base : Register) (v : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .load64Disp0 dst base)
    (hrd : read64 s.speicher (effAddr0 s base) = some v) :
    schrittC d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst v) := by
  unfold schrittC
  simp [hok, h, hrd]

/-- `load64Disp0` refusal: a failed read is an explicit step failure. -/
theorem schrittC_load64Disp0_verweigert (d : CompactDecodiert) (s : Zustand)
    (dst base : Register) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .load64Disp0 dst base)
    (hrd : read64 s.speicher (effAddr0 s base) = none) :
    schrittC d s = none := by
  unfold schrittC
  simp [hok, h, hrd]

/-- `store64Disp0` success: memory carries the word at the base address. -/
theorem schrittC_store64Disp0_erfolg (d : CompactDecodiert) (s : Zustand)
    (base src : Register) (m : Speicher) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .store64Disp0 base src)
    (hwr : write64 s.speicher (effAddr0 s base) (s.register src) = some m) :
    schrittC d s =
      some ({ s with speicher := m, rip := ripNach s.rip d.laenge }) := by
  unfold schrittC
  simp [hok, h, hwr]

/-- `store64Disp0` refusal: a failed write is an explicit step failure. -/
theorem schrittC_store64Disp0_verweigert (d : CompactDecodiert) (s : Zustand)
    (base src : Register) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .store64Disp0 base src)
    (hwr : write64 s.speicher (effAddr0 s base) (s.register src) = none) :
    schrittC d s = none := by
  unfold schrittC
  simp [hok, h, hwr]

/-- `jump8`: RIP moves to the post-decode address plus the sign-extended
    rel8; nothing else changes. -/
theorem schrittC_jump8 (d : CompactDecodiert) (s : Zustand) (rel : BitVec 8)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jump8 rel) :
    schrittC d s =
      some ({ s with rip := ripNach s.rip d.laenge + dispWort8 rel }) := by
  unfold schrittC
  rw [hok, h]

/-- `jumpIf8` taken: RIP moves past the decode point by the sign-extended
    rel8. -/
theorem schrittC_jumpIf8_genommen (d : CompactDecodiert) (s : Zustand)
    (cond : Bedingung) (rel : BitVec 8) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .jumpIf8 cond rel) (hbed : bedingung cond s.flags = true) :
    schrittC d s =
      some ({ s with rip := ripNach s.rip d.laenge + dispWort8 rel }) := by
  unfold schrittC
  simp [hok, h, hbed]

/-- `jumpIf8` not taken: RIP is the post-decode address. -/
theorem schrittC_jumpIf8_nicht (d : CompactDecodiert) (s : Zustand)
    (cond : Bedingung) (rel : BitVec 8) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .jumpIf8 cond rel) (hbed : bedingung cond s.flags = false) :
    schrittC d s = some ({ s with rip := ripNach s.rip d.laenge }) := by
  unfold schrittC
  simp [hok, h, hbed]

/-- A bad decode length refuses every compact form, unconditionally. -/
theorem schrittC_laenge_verweigert (d : CompactDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) : schrittC d s = none := by
  unfold schrittC
  simp [h]

/-! ## 6. Canonical byte codec.

    One canonical byte shape per form, chosen to be the SHORTEST legal
    encoding of DESIGN §2B's table. `movImm32Zx` reuses the bare `B8+rd`
    opcode (plus the pilot's own `0x41` REX.B-only extension pattern for
    r8-r15, exactly like `push64`/`pop64` in `Codec.lean`); the other
    nine reuse REX.W. The decoder parses bytes (never encode-equality),
    matching the `Codec.lean`/`MulDivCodec.lean` discipline. -/

/-- Group-1 ALU opcode extension digit (ADD=0, OR=1, AND=4, SUB=5,
    XOR=6, CMP=7; ADC/SBB are out of scope). -/
def aluExt : AluOp → Nat
  | .add => 0 | .or' => 1 | .and' => 4 | .sub => 5 | .xor' => 6 | .cmp => 7

/-- Inverse check: the extension digit back to an `AluOp`. -/
def extAlu : Nat → Option AluOp
  | 0 => some .add | 1 => some .or' | 4 => some .and' | 5 => some .sub
  | 6 => some .xor' | 7 => some .cmp | _ => none

/-- Decoding inverts encoding on every ALU extension digit. -/
theorem extAlu_aluExt (op : AluOp) : extAlu (aluExt op) = some op := by
  cases op <;> rfl

/-- Every ALU extension digit fits in four bits. -/
theorem aluExt_lt (op : AluOp) : aluExt op < 16 := by cases op <;> decide

/-- ModRM byte with mod=1 (register plus disp8) over low 3-bit codes. -/
def modrmMemD8 (rl rm : Nat) : Byte := natByte (64 + 8 * (rl % 8) + rm % 8)

/-- ModRM byte with mod=0 (register, no displacement) over low 3-bit
    codes. -/
def modrmMemD0 (rl rm : Nat) : Byte := natByte (8 * (rl % 8) + rm % 8)

/-- Canonical byte encoding of one compact-form instruction.
    `movImm32Zx` over an extended register reuses the pilot's `0x41`
    REX.B-only prefix (W=0); the memory forms reuse the pilot's SIB
    convention for `rsp`/`r12` bases (`regLow base == 4`, SIB byte
    `0x24`). -/
def encodeC : CompactBefehl → List Byte
  | .movImm32Zx dst imm =>
    (if regHigh dst == 1 then [natByte 65] else []) ++
      natByte (184 + regLow dst) :: leBytes32 imm
  | .movImm32Sx dst imm =>
    [rexByte 0 (regHigh dst), natByte 199, modrmReg 0 (regLow dst)] ++
      leBytes32 imm
  | .aluImm8 op dst imm =>
    [rexByte 0 (regHigh dst), natByte 131, modrmReg (aluExt op) (regLow dst), imm]
  | .aluImm32 op dst imm =>
    [rexByte 0 (regHigh dst), natByte 129, modrmReg (aluExt op) (regLow dst)] ++
      leBytes32 imm
  | .load64Disp8 dst base disp =>
    let head := [rexByte (regHigh dst) (regHigh base), natByte 139,
      modrmMemD8 (regLow dst) (regLow base)]
    (if regLow base == 4 then head ++ [natByte 36] else head) ++ [disp]
  | .store64Disp8 base src disp =>
    let head := [rexByte (regHigh src) (regHigh base), natByte 137,
      modrmMemD8 (regLow src) (regLow base)]
    (if regLow base == 4 then head ++ [natByte 36] else head) ++ [disp]
  | .load64Disp0 dst base =>
    let head := [rexByte (regHigh dst) (regHigh base), natByte 139,
      modrmMemD0 (regLow dst) (regLow base)]
    if regLow base == 4 then head ++ [natByte 36] else head
  | .store64Disp0 base src =>
    let head := [rexByte (regHigh src) (regHigh base), natByte 137,
      modrmMemD0 (regLow src) (regLow base)]
    if regLow base == 4 then head ++ [natByte 36] else head
  | .jump8 rel => [natByte 235, rel]
  | .jumpIf8 cond rel => [natByte (112 + condCode cond), rel]

/-- Decode one base-relative memory access after REX, opcode and ModRM:
    mod=1 (`mod01 = true`) carries one disp8 byte, mod=0 carries none.
    `rm == 4` needs the fixed SIB byte `0x24` (`rsp`/`r12` base, no
    index); otherwise `rm == 5` at mod=0 is the RIP-relative special
    case this family does NOT implement, and refuses. The returned
    length is the TOTAL instruction length (REX+opcode+ModRM, plus the
    optional SIB/disp8 bytes this layer itself consumes). -/
def decodeMemC (isLoad mod01 : Bool) (rBit bBit reg rm : Nat) :
    List Byte → Option (CompactDecodiert × List Byte)
  | bs =>
    if rm == 4 then
      match bs with
      | [] => none
      | sib :: rest =>
        if byteNat sib == 36 then
          match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + 4) with
          | some rr, some rb =>
            if mod01 then
              match rest with
              | [] => none
              | d :: rest' =>
                if isLoad then some (⟨.load64Disp8 rr rb d, 5⟩, rest')
                else some (⟨.store64Disp8 rb rr d, 5⟩, rest')
            else
              if isLoad then some (⟨.load64Disp0 rr rb, 4⟩, rest)
              else some (⟨.store64Disp0 rb rr, 4⟩, rest)
          | _, _ => none
        else none
    else if rm == 5 ∧ ¬ mod01 then none
    else
      match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
      | some rr, some rb =>
        if mod01 then
          match bs with
          | [] => none
          | d :: rest' =>
            if isLoad then some (⟨.load64Disp8 rr rb d, 4⟩, rest')
            else some (⟨.store64Disp8 rb rr d, 4⟩, rest')
        else
          if isLoad then some (⟨.load64Disp0 rr rb, 3⟩, bs)
          else some (⟨.store64Disp0 rb rr, 3⟩, bs)
      | _, _ => none

/-- Decode after one canonical REX.W prefix: the opcode byte selects
    `movImm32Sx` (Group 11 `/0`, mod=3 only), `aluImm8`/`aluImm32`
    (Group 1, mod=3 only) or the two memory forms (mod ∈ {0, 1} only;
    mod=2/3 belong to the pilot `load64`/`store64` and refuse here). -/
def decodeCRex (rBit bBit : Nat) :
    List Byte → Option (CompactDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    match byteNat op with
    | 199 =>
      match rest with
      | [] => none
      | m :: rest2 =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        if byteNat m / 64 == 3 ∧ rBit * 8 + reg == 0 then
          match codeReg (bBit * 8 + rm) with
          | some dst =>
            match parseLe32 rest2 with
            | some (imm, rest3) => some (⟨.movImm32Sx dst imm, 7⟩, rest3)
            | none => none
          | none => none
        else none
    | 131 =>
      match rest with
      | [] => none
      | m :: rest2 =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        if byteNat m / 64 == 3 then
          match extAlu (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
          | some op', some dst =>
            match rest2 with
            | [] => none
            | imm :: rest3 => some (⟨.aluImm8 op' dst imm, 4⟩, rest3)
          | _, _ => none
        else none
    | 129 =>
      match rest with
      | [] => none
      | m :: rest2 =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        if byteNat m / 64 == 3 then
          match extAlu (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
          | some op', some dst =>
            match parseLe32 rest2 with
            | some (imm, rest3) => some (⟨.aluImm32 op' dst imm, 7⟩, rest3)
            | none => none
          | _, _ => none
        else none
    | 139 =>
      match rest with
      | [] => none
      | m :: rest2 =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        match byteNat m / 64 with
        | 1 => decodeMemC true true rBit bBit reg rm rest2
        | 0 => decodeMemC true false rBit bBit reg rm rest2
        | _ => none
    | 137 =>
      match rest with
      | [] => none
      | m :: rest2 =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        match byteNat m / 64 with
        | 1 => decodeMemC false true rBit bBit reg rm rest2
        | 0 => decodeMemC false false rBit bBit reg rm rest2
        | _ => none
    | _ => none

/-- Decode the first canonical compact-form instruction, returning it
    with its consumed length and the remaining bytes. Only canonical
    encodings are accepted; every non-canonical or truncated input
    refuses with `none`. -/
def decodeC : List Byte → Option (CompactDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    match byteNat b with
    | 235 =>
      match rest with
      | [] => none
      | r :: rest' => some (⟨.jump8 r, 2⟩, rest')
    | 65 =>
      match rest with
      | [] => none
      | b2 :: rest2 =>
        let n := byteNat b2
        if 184 ≤ n ∧ n < 192 then
          match codeReg (n - 184 + 8) with
          | some dst =>
            match parseLe32 rest2 with
            | some (imm, rest3) => some (⟨.movImm32Zx dst imm, 6⟩, rest3)
            | none => none
          | none => none
        else none
    | 72 => decodeCRex 0 0 rest
    | 73 => decodeCRex 0 1 rest
    | 76 => decodeCRex 1 0 rest
    | 77 => decodeCRex 1 1 rest
    | n =>
      if 112 ≤ n ∧ n < 128 then
        match codeCond (n - 112) with
        | some cond =>
          match rest with
          | [] => none
          | r :: rest' => some (⟨.jumpIf8 cond r, 2⟩, rest')
        | none => none
      else if 184 ≤ n ∧ n < 192 then
        match codeReg (n - 184) with
        | some dst =>
          match parseLe32 rest with
          | some (imm, rest2) => some (⟨.movImm32Zx dst imm, 5⟩, rest2)
          | none => none
        | none => none
      else none

/-! ## 7. Round trips: decoding inverts encoding on every compact form.

    `movImm32Zx`/`movImm32Sx`/`aluImm32` carry a symbolic 32-bit
    immediate, so their round trip goes through an intermediate `rfl`
    lemma (reached by case-splitting the register, which is fast: the
    decode layers are plain `Nat`/`BitVec` literal matches) and then the
    REUSED `parseLe32_leBytes32` for the immediate reconstruction --
    never a second encode/decode of the four bytes. `load64Disp8`/
    `store64Disp8` need no such lemma (the disp8 byte is consumed
    directly, no little-endian reassembly) and round-trip for EVERY
    register pair, including `rbp`/`r13`. `load64Disp0`/`store64Disp0`
    round-trip only away from `rbp`/`r13` (§8 states the refusal). -/

/-- Intermediate unfolding of `movImm32Zx`'s decode down to its
    `parseLe32` call (fast: reached by case-splitting the register). -/
theorem decodeC_movImm32Zx_entfaltet (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) :
    decodeC (encodeC (.movImm32Zx dst imm) ++ suffix) =
      (match parseLe32 (leBytes32 imm ++ suffix) with
        | some (v, rest) => some ((⟨CompactBefehl.movImm32Zx dst v,
            if regHigh dst == 1 then 6 else 5⟩ : CompactDecodiert), rest)
        | none => none) := by
  cases dst <;> rfl

/-- Round trip for `movImm32Zx`. -/
theorem roundtripC_movImm32Zx (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) :
    decodeC (encodeC (.movImm32Zx dst imm) ++ suffix) =
      some (⟨.movImm32Zx dst imm, (encodeC (.movImm32Zx dst imm)).length⟩,
        suffix) := by
  rw [decodeC_movImm32Zx_entfaltet, parseLe32_leBytes32]
  cases dst <;> rfl

/-- Intermediate unfolding of `movImm32Sx`'s decode down to its
    `parseLe32` call. -/
theorem decodeC_movImm32Sx_entfaltet (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) :
    decodeC (encodeC (.movImm32Sx dst imm) ++ suffix) =
      (match parseLe32 (leBytes32 imm ++ suffix) with
        | some (v, rest) =>
          some ((⟨CompactBefehl.movImm32Sx dst v, 7⟩ : CompactDecodiert), rest)
        | none => none) := by
  cases dst <;> rfl

/-- Round trip for `movImm32Sx`. -/
theorem roundtripC_movImm32Sx (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) :
    decodeC (encodeC (.movImm32Sx dst imm) ++ suffix) =
      some (⟨.movImm32Sx dst imm, (encodeC (.movImm32Sx dst imm)).length⟩,
        suffix) := by
  rw [decodeC_movImm32Sx_entfaltet, parseLe32_leBytes32]
  cases dst <;> rfl

/-- Round trip for `aluImm8`. -/
theorem roundtripC_aluImm8 (op : AluOp) (dst : Register) (imm : BitVec 8)
    (suffix : List Byte) :
    decodeC (encodeC (.aluImm8 op dst imm) ++ suffix) =
      some (⟨.aluImm8 op dst imm, (encodeC (.aluImm8 op dst imm)).length⟩,
        suffix) := by
  cases op <;> cases dst <;> rfl

/-- Intermediate unfolding of `aluImm32`'s decode down to its
    `parseLe32` call. -/
theorem decodeC_aluImm32_entfaltet (op : AluOp) (dst : Register)
    (imm : BitVec 32) (suffix : List Byte) :
    decodeC (encodeC (.aluImm32 op dst imm) ++ suffix) =
      (match parseLe32 (leBytes32 imm ++ suffix) with
        | some (v, rest) =>
          some ((⟨CompactBefehl.aluImm32 op dst v, 7⟩ : CompactDecodiert), rest)
        | none => none) := by
  cases op <;> cases dst <;> rfl

/-- Round trip for `aluImm32`. -/
theorem roundtripC_aluImm32 (op : AluOp) (dst : Register) (imm : BitVec 32)
    (suffix : List Byte) :
    decodeC (encodeC (.aluImm32 op dst imm) ++ suffix) =
      some (⟨.aluImm32 op dst imm, (encodeC (.aluImm32 op dst imm)).length⟩,
        suffix) := by
  rw [decodeC_aluImm32_entfaltet, parseLe32_leBytes32]
  cases op <;> cases dst <;> rfl

/-- Round trip for `load64Disp8`, for every register pair (including
    `rbp`/`r13`: mod=1 has no RIP-relative special case). -/
theorem roundtripC_load64Disp8 (dst base : Register) (disp : BitVec 8)
    (suffix : List Byte) :
    decodeC (encodeC (.load64Disp8 dst base disp) ++ suffix) =
      some (⟨.load64Disp8 dst base disp,
        (encodeC (.load64Disp8 dst base disp)).length⟩, suffix) := by
  cases dst <;> cases base <;> rfl

/-- Round trip for `store64Disp8`, for every register pair. -/
theorem roundtripC_store64Disp8 (base src : Register) (disp : BitVec 8)
    (suffix : List Byte) :
    decodeC (encodeC (.store64Disp8 base src disp) ++ suffix) =
      some (⟨.store64Disp8 base src disp,
        (encodeC (.store64Disp8 base src disp)).length⟩, suffix) := by
  cases base <;> cases src <;> rfl

/-- Round trip for `load64Disp0`, AWAY from `rbp`/`r13` (§8 states the
    refusal there: mod=0 with those bases is the RIP-relative special
    case, which this family does not implement). -/
theorem roundtripC_load64Disp0 (dst base : Register) (suffix : List Byte)
    (h1 : base ≠ .rbp) (h2 : base ≠ .r13) :
    decodeC (encodeC (.load64Disp0 dst base) ++ suffix) =
      some (⟨.load64Disp0 dst base,
        (encodeC (.load64Disp0 dst base)).length⟩, suffix) := by
  cases dst <;> cases base <;>
    first | rfl | (exfalso; first | exact h1 rfl | exact h2 rfl)

/-- Round trip for `store64Disp0`, AWAY from `rbp`/`r13`. -/
theorem roundtripC_store64Disp0 (base src : Register) (suffix : List Byte)
    (h1 : base ≠ .rbp) (h2 : base ≠ .r13) :
    decodeC (encodeC (.store64Disp0 base src) ++ suffix) =
      some (⟨.store64Disp0 base src,
        (encodeC (.store64Disp0 base src)).length⟩, suffix) := by
  cases base <;> cases src <;>
    first | rfl | (exfalso; first | exact h1 rfl | exact h2 rfl)

/-- Round trip for `jump8`. -/
theorem roundtripC_jump8 (rel : BitVec 8) (suffix : List Byte) :
    decodeC (encodeC (.jump8 rel) ++ suffix) =
      some (⟨.jump8 rel, (encodeC (.jump8 rel)).length⟩, suffix) := rfl

/-- Round trip for `jumpIf8`. -/
theorem roundtripC_jumpIf8 (cond : Bedingung) (rel : BitVec 8)
    (suffix : List Byte) :
    decodeC (encodeC (.jumpIf8 cond rel) ++ suffix) =
      some (⟨.jumpIf8 cond rel, (encodeC (.jumpIf8 cond rel)).length⟩,
        suffix) := by
  cases cond <;> rfl

/-! ## 8. Equivalence to the pilot long forms.

    This is what makes the compact forms safe for the compiler: each one
    computes the SAME effect as the pilot long form it replaces, so a
    selection pass may rewrite one into the other without re-deriving
    any correctness fact about the source program. `movImm32Zx`/
    `movImm32Sx` compare directly against `movImm64` (same length, a
    pure value/flag fact). The disp8/disp0 memory forms compare against
    `load64`/`store64` at the sign-extended/zero displacement (again
    same length: the EFFECTIVE ADDRESS never depends on instruction
    length). `jump8` compares against `jump32` by TARGET, which is the
    one fact relaxation must preserve across a length change: the two
    forms are run from the SAME `rip` with displacements related by the
    length difference (`len_shift`), never by reusing the same raw
    bits. The ALU forms compare against the pilot's two-register ops
    over a scratch register holding the sign-extended immediate, modulo
    that scratch register and `rip` (AND/OR have no pilot register-
    register form to compare against; §9's CUTS names this). -/

/-- Sign-extending an 8-bit displacement to 64 bits directly agrees with
    sign-extending it to 32 bits first (`BitVec.signExtend`) and then
    through the pilot's own `dispWort`. REUSED by every disp8/rel8
    equivalence below. -/
theorem dispWort8_eq_signExtend (d : BitVec 8) :
    dispWort8 d = dispWort (d.signExtend 32) := by
  revert d; decide

/-- `movImm32Zx r v` is `movImm64 r` at the zero-extended value: same
    register/flags/memory/rip, by direct computation. -/
theorem equiv_movImm32Zx (dst : Register) (imm : BitVec 32) (s : Zustand) :
    schrittC ⟨.movImm32Zx dst imm, 5⟩ s =
      schritt ⟨.movImm64 dst (zextWort32 imm), 5⟩ s := rfl

/-- `movImm32Sx r v` is `movImm64 r` at the sign-extended value. -/
theorem equiv_movImm32Sx (dst : Register) (imm : BitVec 32) (s : Zustand) :
    schrittC ⟨.movImm32Sx dst imm, 7⟩ s =
      schritt ⟨.movImm64 dst (dispWort imm), 7⟩ s := rfl

/-- `load64Disp8` is `load64` at the sign-extended displacement (same
    length): the effective address agrees via `dispWort8_eq_signExtend`,
    so the whole step -- including a failed read -- agrees. -/
theorem equiv_load64Disp8 (dst base : Register) (disp : BitVec 8) (s : Zustand) :
    schrittC ⟨.load64Disp8 dst base disp, 4⟩ s =
      schritt ⟨.load64 dst base (disp.signExtend 32), 4⟩ s := by
  simp only [schrittC, schritt, effAddr8, effAddr, dispWort8_eq_signExtend]
  rfl

/-- `store64Disp8` is `store64` at the sign-extended displacement. -/
theorem equiv_store64Disp8 (base src : Register) (disp : BitVec 8) (s : Zustand) :
    schrittC ⟨.store64Disp8 base src disp, 4⟩ s =
      schritt ⟨.store64 base src (disp.signExtend 32), 4⟩ s := by
  simp only [schrittC, schritt, effAddr8, effAddr, dispWort8_eq_signExtend]
  rfl

/-- The base register alone is the effective address at a zero
    displacement -- the bridge between `effAddr0` and `effAddr`. -/
theorem effAddr0_eq_effAddr (s : Zustand) (base : Register) :
    effAddr0 s base = effAddr s base 0 := by
  unfold effAddr0 effAddr
  have h0 : dispWort (0 : BitVec 32) = 0 := by decide
  rw [h0]
  exact (BitVec.add_zero _).symm

/-- `load64Disp0` is `load64` at a zero displacement. -/
theorem equiv_load64Disp0 (dst base : Register) (s : Zustand) :
    schrittC ⟨.load64Disp0 dst base, 3⟩ s =
      schritt ⟨.load64 dst base 0, 3⟩ s := by
  show (match laengeOk 3 with
    | false => none
    | true => match read64 s.speicher (effAddr0 s base) with
      | some v => some (schrittRegister s (ripNach s.rip 3) s.flags dst v)
      | none => none) =
    (match laengeOk 3 with
    | false => none
    | true => match read64 s.speicher (effAddr s base 0) with
      | some v => some (schrittRegister s (ripNach s.rip 3) s.flags dst v)
      | none => none)
  rw [effAddr0_eq_effAddr]

/-- `store64Disp0` is `store64` at a zero displacement. -/
theorem equiv_store64Disp0 (base src : Register) (s : Zustand) :
    schrittC ⟨.store64Disp0 base src, 3⟩ s =
      schritt ⟨.store64 base src 0, 3⟩ s := by
  show (match laengeOk 3 with
    | false => none
    | true => match write64 s.speicher (effAddr0 s base) (s.register src) with
      | some m => some ({ s with speicher := m, rip := ripNach s.rip 3 })
      | none => none) =
    (match laengeOk 3 with
    | false => none
    | true => match write64 s.speicher (effAddr s base 0) (s.register src) with
      | some m => some ({ s with speicher := m, rip := ripNach s.rip 3 })
      | none => none)
  rw [effAddr0_eq_effAddr]

/-- Pure length-shift identity: adding `l1` then the ADJUSTED remainder
    `x + l2 - l1` lands at the same word as adding `l2` directly. The
    one arithmetic fact every length-changing branch-target equivalence
    below reduces to; it holds for any `l1`/`l2`, never only the pilot's
    actual lengths. -/
theorem len_shift (l1 l2 : Nat) (r x : Wort) :
    r + BitVec.ofNat 64 l1 + (x + BitVec.ofNat 64 l2 - BitVec.ofNat 64 l1) =
      r + BitVec.ofNat 64 l2 + x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_sub]
  omega

/-- The relaxed rel32 that reaches the SAME target as `jump8 d` from the
    SAME starting `rip`, accounting for the 3-byte length difference
    (2 vs 5): recomputed, never the same raw bits reused across widths. -/
def rel32C (d : BitVec 8) : BitVec 32 :=
  BitVec.ofNat 32 ((dispWort8 d + BitVec.ofNat 64 2 - BitVec.ofNat 64 5).toNat % 2 ^ 32)

/-- The relaxed rel32 round-trips: sign-extending it back gives exactly
    the adjusted 64-bit displacement (no 32-bit overflow at these
    magnitudes). -/
theorem rel32C_spec (d : BitVec 8) :
    dispWort (rel32C d) = dispWort8 d + BitVec.ofNat 64 2 - BitVec.ofNat 64 5 := by
  revert d; decide

/-- `jump8 d` and `jump32 (rel32C d)`, run from the SAME state, reach
    the SAME target -- the content of branch relaxation: the content is
    the target, not the instruction's own length. -/
theorem equiv_jump8_target (d : BitVec 8) (s : Zustand) :
    (schrittC ⟨.jump8 d, 2⟩ s).map (fun s' => s'.rip) =
      (schritt ⟨.jump32 (rel32C d), 5⟩ s).map (fun s' => s'.rip) := by
  unfold schrittC schritt ripNach
  simp only [laengeOk]
  rw [show decide (1 ≤ 2 ∧ 2 ≤ 15) = true from rfl,
      show decide (1 ≤ 5 ∧ 5 ≤ 15) = true from rfl]
  show some (s.rip + BitVec.ofNat 64 2 + dispWort8 d) =
       some (s.rip + BitVec.ofNat 64 5 + dispWort (rel32C d))
  rw [rel32C_spec]
  exact congrArg some (len_shift 5 2 s.rip (dispWort8 d)).symm

/-- The pilot register-register instruction an ALU imm8 op routes to,
    when one exists. AND/OR have no pilot register-register form
    (`Befehl` names none), so they route to `none`; this is a genuine
    scope boundary, not an oversight (CUTS). -/
def aluPilotBefehl : AluOp → Register → Register → Option Befehl
  | .add, dst, t => some (.addReg64 dst t)
  | .sub, dst, t => some (.subReg64 dst t)
  | .xor', dst, t => some (.xorReg64 dst t)
  | .cmp, dst, t => some (.cmpReg64 dst t)
  | .and', _, _ => none
  | .or', _, _ => none

/-- `aluImm8 op dst imm` produces the SAME destination register and
    flags as the pilot's two-register `op dst t` would, with `t` holding
    the sign-extended immediate (modulo the scratch register `t` itself
    and `rip`, which the two forms advance by different lengths) -- for
    every op with a pilot analog (ADD/SUB/XOR/CMP; AND/OR are excluded
    by `aluPilotBefehl`, which routes them to `none`, refusing the
    statement rather than inventing a pilot form for them). -/
theorem equiv_aluImm8 (op : AluOp) (dst t : Register) (imm : BitVec 8) (s : Zustand)
    (hdt : dst ≠ t) (pb : Befehl) (hpb : aluPilotBefehl op dst t = some pb) :
    ∃ s1 s2,
      schrittC ⟨.aluImm8 op dst imm, 4⟩ s = some s1 ∧
      schritt ⟨pb, 3⟩ ({ s with register := regSet s.register t (dispWort8 imm) }) = some s2 ∧
      (∀ q, q ≠ t → s1.register q = s2.register q) ∧
      s1.flags = s2.flags ∧ s1.speicher = s2.speicher := by
  have ht : regSet s.register t (dispWort8 imm) t = dispWort8 imm := regSet_gleich _ _ _
  cases op with
  | add =>
    simp only [aluPilotBefehl] at hpb
    cases hpb
    refine ⟨schrittRegister s (ripNach s.rip 4)
        (aluFlags .add (s.register dst) (dispWort8 imm)) dst
        (aluWert .add (s.register dst) (dispWort8 imm)),
      schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
        (ripNach s.rip 3) (add64 (s.register dst) (dispWort8 imm)).2 dst
        (add64 (s.register dst) (dispWort8 imm)).1, rfl, ?_, ?_, ?_, rfl⟩
    · show schritt ⟨.addReg64 dst t, 3⟩
          ({ s with register := regSet s.register t (dispWort8 imm) }) =
        some (schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
          (ripNach s.rip 3) (add64 (s.register dst) (dispWort8 imm)).2 dst
          (add64 (s.register dst) (dispWort8 imm)).1)
      rw [schritt_addReg64 ⟨.addReg64 dst t, 3⟩ _ dst t rfl rfl]
      dsimp only
      rw [ht, regSet_fremd s.register t dst (dispWort8 imm) hdt]
    · intro q hq
      show (schrittRegister s (ripNach s.rip 4)
          (aluFlags .add (s.register dst) (dispWort8 imm)) dst
          (aluWert .add (s.register dst) (dispWort8 imm))).register q =
        (schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
          (ripNach s.rip 3) (add64 (s.register dst) (dispWort8 imm)).2 dst
          (add64 (s.register dst) (dispWort8 imm)).1).register q
      unfold schrittRegister
      simp only [aluWert]
      by_cases hqd : q = dst
      · subst hqd; rw [regSet_gleich, regSet_gleich]
      · rw [regSet_fremd _ dst q _ hqd, regSet_fremd _ dst q _ hqd, regSet_fremd _ t q _ hq]
    · show (aluFlags .add (s.register dst) (dispWort8 imm)) =
        (add64 (s.register dst) (dispWort8 imm)).2
      rfl
  | sub =>
    simp only [aluPilotBefehl] at hpb
    cases hpb
    refine ⟨schrittRegister s (ripNach s.rip 4)
        (aluFlags .sub (s.register dst) (dispWort8 imm)) dst
        (aluWert .sub (s.register dst) (dispWort8 imm)),
      schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
        (ripNach s.rip 3) (sub64 (s.register dst) (dispWort8 imm)).2 dst
        (sub64 (s.register dst) (dispWort8 imm)).1, rfl, ?_, ?_, ?_, rfl⟩
    · show schritt ⟨.subReg64 dst t, 3⟩
          ({ s with register := regSet s.register t (dispWort8 imm) }) =
        some (schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
          (ripNach s.rip 3) (sub64 (s.register dst) (dispWort8 imm)).2 dst
          (sub64 (s.register dst) (dispWort8 imm)).1)
      rw [schritt_subReg64 ⟨.subReg64 dst t, 3⟩ _ dst t rfl rfl]
      dsimp only
      rw [ht, regSet_fremd s.register t dst (dispWort8 imm) hdt]
    · intro q hq
      show (schrittRegister s (ripNach s.rip 4)
          (aluFlags .sub (s.register dst) (dispWort8 imm)) dst
          (aluWert .sub (s.register dst) (dispWort8 imm))).register q =
        (schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
          (ripNach s.rip 3) (sub64 (s.register dst) (dispWort8 imm)).2 dst
          (sub64 (s.register dst) (dispWort8 imm)).1).register q
      unfold schrittRegister
      simp only [aluWert]
      by_cases hqd : q = dst
      · subst hqd; rw [regSet_gleich, regSet_gleich]
      · rw [regSet_fremd _ dst q _ hqd, regSet_fremd _ dst q _ hqd, regSet_fremd _ t q _ hq]
    · show (aluFlags .sub (s.register dst) (dispWort8 imm)) =
        (sub64 (s.register dst) (dispWort8 imm)).2
      rfl
  | xor' =>
    simp only [aluPilotBefehl] at hpb
    cases hpb
    refine ⟨schrittRegister s (ripNach s.rip 4)
        (aluFlags .xor' (s.register dst) (dispWort8 imm)) dst
        (aluWert .xor' (s.register dst) (dispWort8 imm)),
      schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
        (ripNach s.rip 3) (xor64 (s.register dst) (dispWort8 imm)).2 dst
        (xor64 (s.register dst) (dispWort8 imm)).1, rfl, ?_, ?_, ?_, rfl⟩
    · show schritt ⟨.xorReg64 dst t, 3⟩
          ({ s with register := regSet s.register t (dispWort8 imm) }) =
        some (schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
          (ripNach s.rip 3) (xor64 (s.register dst) (dispWort8 imm)).2 dst
          (xor64 (s.register dst) (dispWort8 imm)).1)
      rw [schritt_xorReg64 ⟨.xorReg64 dst t, 3⟩ _ dst t rfl rfl]
      dsimp only
      rw [ht, regSet_fremd s.register t dst (dispWort8 imm) hdt]
    · intro q hq
      show (schrittRegister s (ripNach s.rip 4)
          (aluFlags .xor' (s.register dst) (dispWort8 imm)) dst
          (aluWert .xor' (s.register dst) (dispWort8 imm))).register q =
        (schrittRegister ({ s with register := regSet s.register t (dispWort8 imm) })
          (ripNach s.rip 3) (xor64 (s.register dst) (dispWort8 imm)).2 dst
          (xor64 (s.register dst) (dispWort8 imm)).1).register q
      unfold schrittRegister
      simp only [aluWert]
      by_cases hqd : q = dst
      · subst hqd; rw [regSet_gleich, regSet_gleich]
      · rw [regSet_fremd _ dst q _ hqd, regSet_fremd _ dst q _ hqd, regSet_fremd _ t q _ hq]
    · show (aluFlags .xor' (s.register dst) (dispWort8 imm)) =
        (xor64 (s.register dst) (dispWort8 imm)).2
      rfl
  | cmp =>
    simp only [aluPilotBefehl] at hpb
    cases hpb
    refine ⟨({ s with rip := ripNach s.rip 4, flags := aluFlags .cmp (s.register dst) (dispWort8 imm) }),
      ({ s with register := regSet s.register t (dispWort8 imm), rip := ripNach s.rip 3, flags := (sub64 (s.register dst) (dispWort8 imm)).2 }), ?_, ?_, ?_, ?_, rfl⟩
    · show schrittC ⟨.aluImm8 .cmp dst imm, 4⟩ s = some _
      rfl
    · show schritt ⟨.cmpReg64 dst t, 3⟩ ({ s with register := regSet s.register t (dispWort8 imm) }) =
        some _
      rw [schritt_cmpReg64 ⟨.cmpReg64 dst t, 3⟩ _ dst t rfl rfl]
      dsimp only
      rw [ht, regSet_fremd s.register t dst (dispWort8 imm) hdt]
    · intro q hq
      show s.register q = (regSet s.register t (dispWort8 imm)) q
      rw [regSet_fremd s.register t q (dispWort8 imm) hq]
    · show aluFlags .cmp (s.register dst) (dispWort8 imm) = (sub64 (s.register dst) (dispWort8 imm)).2
      rfl
  | and' => simp only [aluPilotBefehl] at hpb; exact absurd hpb (by simp)
  | or' => simp only [aluPilotBefehl] at hpb; exact absurd hpb (by simp)

/-! ## 9. The decided selector: shortest legal compact form.

    `kompaktWahl` picks the shortest legal compact form for the FIVE
    pilot constructors with a direct single-instruction compact analog
    (`movImm64`, `load64`, `store64`, `jump32`, `jumpIf32`); the other
    nine pilot forms (register-register ops, stack, call/ret) have no
    narrower encoding in this family and route to `none`. Priority
    mirrors the byte count: disp0 (3-4 bytes) before disp8 (4-5 bytes)
    before the kept wide form; zero-extending MOV before sign-extending.
    `kernGleich` is the "executes like the original" conclusion for the
    data-moving forms: register file, flags and memory agree, dropping
    `rip` (a length-changing rewrite needs the LAYOUT'S bounded
    relaxation to re-validate addresses afterward, exactly as DESIGN
    §2B's relaxation paragraph states; this file proves the per-
    instruction semantic content, not a layout pass). For `jump32`/
    `jumpIf32` the conclusion is TARGET equality instead (dropping
    register/flags/memory, which control flow never touches), and the
    `jumpIf32` conclusion is scoped to the TAKEN branch: the untaken
    successor address is the next instruction's start in the FINAL
    layout, a property of the surrounding byte stream that a single
    `schritt`/`schrittC` call cannot see (CUTS). -/

/-- Zero-extended-value admission: does `v` already fit a plain 32-bit
    pattern (upper 32 bits clear)? -/
def passtZx32 (v : Wort) : Bool := decide (zextWort32 (BitVec.ofNat 32 v.toNat) = v)

/-- Sign-extended-value admission: does `v` round-trip through a signed
    32-bit immediate? -/
def passtSx32 (v : Wort) : Bool := decide (dispWort (BitVec.ofNat 32 v.toNat) = v)

/-- The low byte of a 32-bit displacement, as a candidate rel8/disp8. -/
def disp8Of (d : BitVec 32) : BitVec 8 := BitVec.ofNat 8 d.toNat

/-- Sign-extended-displacement admission: does the 32-bit displacement
    `d` round-trip through its own low byte? -/
def passtS8_32 (d : BitVec 32) : Bool := decide ((disp8Of d).signExtend 32 = d)

/-- Disp0 admission: a zero displacement over a base that is NEITHER
    `rbp` NOR `r13` (mod=0 with those low bits is the RIP-relative
    special case this family refuses; §6's codec already refuses the
    matching bytes). -/
def disp0Zulaessig (base : Register) (disp : BitVec 32) : Bool :=
  decide (disp = 0 ∧ base ≠ .rbp ∧ base ≠ .r13)

/-- The low byte of a 64-bit word, as a candidate rel8 after a length-
    adjusting shift. -/
def rel8FromWort (w : Wort) : BitVec 8 := BitVec.ofNat 8 w.toNat

/-- Length-adjusted rel8 admission: does the SHIFTED word (the target-
    preserving displacement, not the pilot's raw bits) round-trip
    through its own low byte? -/
def passtRel8Wort (w : Wort) : Bool := decide (dispWort8 (rel8FromWort w) = w)

/-- The decided selector: the shortest legal compact form for the five
    pilot constructors that have one, `none` for every other pilot
    form. The jump forms shift the displacement by the length
    difference FIRST (`len_shift`'s content) so the selected rel8
    preserves the target; the memory forms never shift (the effective
    address does not depend on instruction length). -/
def kompaktWahl : Befehl → Option CompactBefehl
  | .movImm64 dst v =>
    if passtZx32 v then some (.movImm32Zx dst (BitVec.ofNat 32 v.toNat))
    else if passtSx32 v then some (.movImm32Sx dst (BitVec.ofNat 32 v.toNat))
    else none
  | .load64 dst base disp =>
    if disp0Zulaessig base disp then some (.load64Disp0 dst base)
    else if passtS8_32 disp then some (.load64Disp8 dst base (disp8Of disp))
    else none
  | .store64 base src disp =>
    if disp0Zulaessig base disp then some (.store64Disp0 base src)
    else if passtS8_32 disp then some (.store64Disp8 base src (disp8Of disp))
    else none
  | .jump32 disp =>
    let w := dispWort disp + BitVec.ofNat 64 5 - BitVec.ofNat 64 2
    if passtRel8Wort w then some (.jump8 (rel8FromWort w)) else none
  | .jumpIf32 cond disp =>
    let w := dispWort disp + BitVec.ofNat 64 6 - BitVec.ofNat 64 2
    if passtRel8Wort w then some (.jumpIf8 cond (rel8FromWort w)) else none
  | _ => none

/-- The data-moving conclusion: register file, flags and memory agree
    (dropping `rip`, which a length-changing rewrite leaves to the
    layout pass to re-validate). -/
def kernGleich (s1 s2 : Zustand) : Prop :=
  s1.register = s2.register ∧ s1.flags = s2.flags ∧ s1.speicher = s2.speicher

/-- The effective address at an 8-bit displacement is the pilot's
    effective address at that displacement sign-extended to 32 bits --
    the memory-form bridge the selector's disp8 branch needs. -/
theorem effAddr8_eq_effAddr (s : Zustand) (base : Register) (d : BitVec 8) :
    effAddr8 s base d = effAddr s base (d.signExtend 32) := by
  unfold effAddr8 effAddr
  rw [dispWort8_eq_signExtend]

/-- SELECTOR CORRECTNESS (`movImm64`): the selected compact form
    executes like the original, for ANY two valid lengths on either
    side -- a length-changing rewrite needs no rip agreement here, only
    the kernel. -/
theorem kompaktWahl_movImm64 (dst : Register) (v : Wort) (cb : CompactBefehl)
    (h : kompaktWahl (.movImm64 dst v) = some cb) (s : Zustand)
    (cLen pLen : Nat) (hc : laengeOk cLen) (hp : laengeOk pLen)
    (s1 s2 : Zustand)
    (h1 : schrittC ⟨cb, cLen⟩ s = some s1) (h2 : schritt ⟨.movImm64 dst v, pLen⟩ s = some s2) :
    kernGleich s1 s2 := by
  simp only [kompaktWahl] at h
  split at h
  · rename_i hzx
    cases h
    rw [schritt_movImm64 _ _ dst v hp rfl] at h2
    have hv : zextWort32 (BitVec.ofNat 32 v.toNat) = v := of_decide_eq_true hzx
    rw [schrittC_movImm32Zx _ _ dst _ hc rfl] at h1
    rw [hv] at h1
    have e1 := Option.some.inj h1
    have e2 := Option.some.inj h2
    subst e1; subst e2
    exact ⟨rfl, rfl, rfl⟩
  · split at h
    · rename_i _ hsx
      cases h
      rw [schritt_movImm64 _ _ dst v hp rfl] at h2
      have hv : dispWort (BitVec.ofNat 32 v.toNat) = v := of_decide_eq_true hsx
      rw [schrittC_movImm32Sx _ _ dst _ hc rfl] at h1
      rw [hv] at h1
      have e1 := Option.some.inj h1
      have e2 := Option.some.inj h2
      subst e1; subst e2
      exact ⟨rfl, rfl, rfl⟩
    · simp at h

/-- SELECTOR CORRECTNESS (`load64`): the selected disp0/disp8 form
    executes like the original. -/
theorem kompaktWahl_load64 (dst base : Register) (disp : BitVec 32) (cb : CompactBefehl)
    (h : kompaktWahl (.load64 dst base disp) = some cb) (s : Zustand)
    (cLen pLen : Nat) (hc : laengeOk cLen) (hp : laengeOk pLen)
    (s1 s2 : Zustand)
    (h1 : schrittC ⟨cb, cLen⟩ s = some s1)
    (h2 : schritt ⟨.load64 dst base disp, pLen⟩ s = some s2) :
    kernGleich s1 s2 := by
  simp only [kompaktWahl] at h
  split at h
  · rename_i hd0
    cases h
    obtain ⟨hdisp, hnrbp, hnr13⟩ := of_decide_eq_true hd0
    subst hdisp
    have haddr : effAddr0 s base = effAddr s base 0 := effAddr0_eq_effAddr s base
    cases hrd : read64 s.speicher (effAddr s base 0) with
    | none =>
      rw [schritt_load64_verweigert _ _ dst base 0 hp rfl hrd] at h2
      simp at h2
    | some v =>
      rw [schritt_load64_erfolg _ _ dst base 0 v hp rfl hrd] at h2
      rw [← haddr] at hrd
      rw [schrittC_load64Disp0_erfolg _ _ dst base v hc rfl hrd] at h1
      have e1 := Option.some.inj h1
      have e2 := Option.some.inj h2
      subst e1; subst e2
      exact ⟨rfl, rfl, rfl⟩
  · split at h
    · rename_i _ hs8
      cases h
      have haddr : effAddr8 s base (disp8Of disp) = effAddr s base disp := by
        rw [effAddr8_eq_effAddr, of_decide_eq_true hs8]
      cases hrd : read64 s.speicher (effAddr s base disp) with
      | none =>
        rw [schritt_load64_verweigert _ _ dst base disp hp rfl hrd] at h2
        simp at h2
      | some v =>
        rw [schritt_load64_erfolg _ _ dst base disp v hp rfl hrd] at h2
        rw [← haddr] at hrd
        rw [schrittC_load64Disp8_erfolg _ _ dst base (disp8Of disp) v hc rfl hrd] at h1
        have e1 := Option.some.inj h1
        have e2 := Option.some.inj h2
        subst e1; subst e2
        exact ⟨rfl, rfl, rfl⟩
    · simp at h

/-- SELECTOR CORRECTNESS (`store64`): the selected disp0/disp8 form
    executes like the original. -/
theorem kompaktWahl_store64 (base src : Register) (disp : BitVec 32) (cb : CompactBefehl)
    (h : kompaktWahl (.store64 base src disp) = some cb) (s : Zustand)
    (cLen pLen : Nat) (hc : laengeOk cLen) (hp : laengeOk pLen)
    (s1 s2 : Zustand)
    (h1 : schrittC ⟨cb, cLen⟩ s = some s1)
    (h2 : schritt ⟨.store64 base src disp, pLen⟩ s = some s2) :
    kernGleich s1 s2 := by
  simp only [kompaktWahl] at h
  split at h
  · rename_i hd0
    cases h
    obtain ⟨hdisp, hnrbp, hnr13⟩ := of_decide_eq_true hd0
    subst hdisp
    have haddr : effAddr0 s base = effAddr s base 0 := effAddr0_eq_effAddr s base
    cases hwr : write64 s.speicher (effAddr s base 0) (s.register src) with
    | none =>
      rw [schritt_store64_verweigert _ _ base src 0 hp rfl hwr] at h2
      simp at h2
    | some m =>
      rw [schritt_store64_erfolg _ _ base src 0 m hp rfl hwr] at h2
      rw [← haddr] at hwr
      rw [schrittC_store64Disp0_erfolg _ _ base src m hc rfl hwr] at h1
      have e1 := Option.some.inj h1
      have e2 := Option.some.inj h2
      subst e1; subst e2
      exact ⟨rfl, rfl, rfl⟩
  · split at h
    · rename_i _ hs8
      cases h
      have haddr : effAddr8 s base (disp8Of disp) = effAddr s base disp := by
        rw [effAddr8_eq_effAddr, of_decide_eq_true hs8]
      cases hwr : write64 s.speicher (effAddr s base disp) (s.register src) with
      | none =>
        rw [schritt_store64_verweigert _ _ base src disp hp rfl hwr] at h2
        simp at h2
      | some m =>
        rw [schritt_store64_erfolg _ _ base src disp m hp rfl hwr] at h2
        rw [← haddr] at hwr
        rw [schrittC_store64Disp8_erfolg _ _ base src (disp8Of disp) m hc rfl hwr] at h1
        have e1 := Option.some.inj h1
        have e2 := Option.some.inj h2
        subst e1; subst e2
        exact ⟨rfl, rfl, rfl⟩
    · simp at h

/-- SELECTOR CORRECTNESS (`jump32`): the selected `jump8` reaches the
    SAME target, from the SAME starting state -- the content of
    branch relaxation. -/
theorem kompaktWahl_jump32 (disp : BitVec 32) (cb : CompactBefehl)
    (h : kompaktWahl (.jump32 disp) = some cb) (s : Zustand) :
    (schrittC ⟨cb, 2⟩ s).map (fun s' => s'.rip) =
      (schritt ⟨.jump32 disp, 5⟩ s).map (fun s' => s'.rip) := by
  simp only [kompaktWahl] at h
  split at h
  · rename_i hw
    cases h
    have hw' := of_decide_eq_true hw
    show (schrittC ⟨.jump8 (rel8FromWort
        (dispWort disp + BitVec.ofNat 64 5 - BitVec.ofNat 64 2)), 2⟩ s).map
        (fun s' => s'.rip) = (schritt ⟨.jump32 disp, 5⟩ s).map (fun s' => s'.rip)
    unfold schrittC schritt ripNach
    simp only [laengeOk]
    rw [show decide (1 ≤ 2 ∧ 2 ≤ 15) = true from rfl,
        show decide (1 ≤ 5 ∧ 5 ≤ 15) = true from rfl]
    show some (s.rip + BitVec.ofNat 64 2 + dispWort8 (rel8FromWort
          (dispWort disp + BitVec.ofNat 64 5 - BitVec.ofNat 64 2))) =
         some (s.rip + BitVec.ofNat 64 5 + dispWort disp)
    rw [hw']
    exact congrArg some (len_shift 2 5 s.rip (dispWort disp))
  · simp at h

/-- SELECTOR CORRECTNESS (`jumpIf32`, TAKEN branch): the selected
    `jumpIf8` reaches the SAME target when the condition holds. The
    untaken successor is a layout property (CUTS), not claimed here. -/
theorem kompaktWahl_jumpIf32_genommen (cond : Bedingung) (disp : BitVec 32) (cb : CompactBefehl)
    (h : kompaktWahl (.jumpIf32 cond disp) = some cb) (s : Zustand)
    (hbed : bedingung cond s.flags = true) :
    (schrittC ⟨cb, 2⟩ s).map (fun s' => s'.rip) =
      (schritt ⟨.jumpIf32 cond disp, 6⟩ s).map (fun s' => s'.rip) := by
  simp only [kompaktWahl] at h
  split at h
  · rename_i hw
    cases h
    have hw' := of_decide_eq_true hw
    rw [schritt_jumpIf32_genommen _ _ cond disp rfl rfl hbed]
    unfold schrittC
    simp only [laengeOk]
    rw [show decide (1 ≤ 2 ∧ 2 ≤ 15) = true from rfl]
    simp only [hbed]
    show some (s.rip + BitVec.ofNat 64 2 + dispWort8 (rel8FromWort
          (dispWort disp + BitVec.ofNat 64 6 - BitVec.ofNat 64 2))) =
         some (ripNach s.rip 6 + dispWort disp)
    rw [hw']
    unfold ripNach
    exact congrArg some (len_shift 2 6 s.rip (dispWort disp))
  · simp at h


/- CUTS:
   Proved here: the ten DESIGN-§2B compact forms as one new instruction
   family (`CompactBefehl`/`CompactDecodiert`) with its own step
   (`schrittC`, reusing `regSet`/`ripNach`/`schrittRegister`/`effAddr`-
   style helpers from `Ausfuehrung.lean`, the REUSED `add64`/`sub64`/
   `xor64` from `Wort.lean` and `and64`/`or64` from `Ganzzahl.lean`, and
   the REUSED permission-checked `read64`/`write64` from `Speicher.lean`
   -- no duplicated evaluator); a canonical byte codec (`encodeC`/
   `decodeC` with per-layer decoders `decodeCRex`/`decodeMemC`) with
   round trips for every form (`roundtripC_*`, two via an intermediate
   `rfl` unfolding plus the REUSED `parseLe32_leBytes32` for the 32-bit
   immediate forms), length bounds, pinned byte/decode pairs, explicit
   refusals of truncated/non-canonical inputs and of the `rbp`/`r13`
   disp0 RIP-relative special case, and boundary probes showing the
   pilot `decode` and this family's `decodeC` never claim each other's
   canonical bytes; EQUIVALENCE lemmas to the pilot long forms for
   `movImm32Zx`/`movImm32Sx` (against `movImm64`, by direct computation),
   `load64Disp8`/`store64Disp8`/`load64Disp0`/`store64Disp0` (against
   `load64`/`store64` at the sign-extended/zero displacement), `jump8`
   (against `jump32` by TARGET equality through the relaxed `rel32C`,
   via the generic arithmetic identity `len_shift`), and `aluImm8`
   ADD/SUB/XOR/CMP (against the pilot's two-register forms over a
   scratch register holding the sign-extended immediate, modulo that
   register and `rip`); and the decided selector `kompaktWahl` (the
   five pilot forms with a direct compact analog: `movImm64`, `load64`,
   `store64`, `jump32`, `jumpIf32`) with its correctness theorems
   (`kompaktWahl_*`: kernel equivalence for the data-moving forms,
   target equality -- for `jumpIf32`, the TAKEN branch only -- for the
   control forms).

   NOT proved here, and not claimed:
   - No `Befehl` extension and no `schritt` equation change: the 14
     pilot forms are untouched, exactly like the `MulDiv`/`ShiftLogic`
     extension pattern. Wiring these ten forms into `Befehl`/`schritt`/
     a unified decoder/image stays OPEN with the Typen/decoder owners.
   - No pilot register-register form for AND/OR (`Befehl` has none), so
     `aluPilotBefehl` routes them to `none` and `equiv_aluImm8` excludes
     them by hypothesis -- a genuine scope boundary, not an oversight.
   - No ARBITRARY-INPUT decoder length soundness in the `MulDivCodec`
     style (every successful decode of ANY input consumes exactly its
     stated length): the round trips here establish exact lengths only
     for CONSTRUCTED (encode-then-decode) instances, via `encodeC_len`
     and the per-form `roundtripC_*`/`decodeC_*_entfaltet` lemmas.
   - No branch-relaxation LAYOUT pass: `equiv_jump8_target` and
     `kompaktWahl_jump32`/`_jumpIf32_genommen` are per-INSTRUCTION
     target-preservation facts over one `Zustand`; the bounded
     multi-branch compression rounds, fall-through convergence and
     full-image revalidation DESIGN §2B describes are a consumer's
     business (`BranchLayout.lean`/`RelocatedExecution.lean`'s own
     scope, which this file does not touch or extend).
   - `kompaktWahl_jumpIf32_genommen` is scoped to the TAKEN branch only:
     the untaken successor address is a property of where the next
     instruction starts in the FINAL byte layout, which a single
     `schritt`/`schrittC` call from one `Zustand` cannot see.
   - `kernGleich` drops `rip`: a length-changing rewrite between a
     compact and a pilot form needs the surrounding layout to
     re-validate addresses afterward (DESIGN §2B's relaxation
     paragraph); this file proves the per-instruction semantic content
     the selector preserves, not a layout/relocation pass.
   - No source correspondence: nothing here speaks about Gabbro source
     ranges, duties, lowering or bridges; no `-O3`-like cost transfer
     (code-size/latency measurement) is modelled.
   - No TSO/concurrency bridge: all facts are sequential over one
     `Zustand`/`Speicher`; aligned multi-byte atomicity, tearing and the
     GX refinement stay with the TSO lane.
   - No hardware verification: the canonical byte shapes (bare `B8+rd`
     plus the pilot's own `0x41` REX.B-only extension; REX.W `C7 /0`;
     Group 1 `83`/`81 /n`; mod=0/1 memory forms; `EB`/`70+cc`), the
     REX.R-unused choice for the Group-1/11 opcode extension, and the
     `rbp`/`r13` disp0 refusal are STATED canonical-subset semantics,
     not verified against silicon.
   - This file adds no new source-language construct or checker rule:
     no diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms aluWert_routen
#print axioms schrittC_movImm32Zx
#print axioms schrittC_movImm32Sx
#print axioms schrittC_aluImm8_schreibt
#print axioms schrittC_aluImm8_cmp
#print axioms schrittC_aluImm32_schreibt
#print axioms schrittC_aluImm32_cmp
#print axioms schrittC_load64Disp8_erfolg
#print axioms schrittC_load64Disp8_verweigert
#print axioms schrittC_store64Disp8_erfolg
#print axioms schrittC_store64Disp8_verweigert
#print axioms schrittC_load64Disp0_erfolg
#print axioms schrittC_load64Disp0_verweigert
#print axioms schrittC_store64Disp0_erfolg
#print axioms schrittC_store64Disp0_verweigert
#print axioms schrittC_jump8
#print axioms schrittC_jumpIf8_genommen
#print axioms schrittC_jumpIf8_nicht
#print axioms schrittC_laenge_verweigert
#print axioms extAlu_aluExt
#print axioms aluExt_lt
#print axioms decodeC_movImm32Zx_entfaltet
#print axioms roundtripC_movImm32Zx
#print axioms decodeC_movImm32Sx_entfaltet
#print axioms roundtripC_movImm32Sx
#print axioms roundtripC_aluImm8
#print axioms decodeC_aluImm32_entfaltet
#print axioms roundtripC_aluImm32
#print axioms roundtripC_load64Disp8
#print axioms roundtripC_store64Disp8
#print axioms roundtripC_load64Disp0
#print axioms roundtripC_store64Disp0
#print axioms roundtripC_jump8
#print axioms roundtripC_jumpIf8
#print axioms dispWort8_eq_signExtend
#print axioms equiv_movImm32Zx
#print axioms equiv_movImm32Sx
#print axioms equiv_load64Disp8
#print axioms equiv_store64Disp8
#print axioms effAddr0_eq_effAddr
#print axioms equiv_load64Disp0
#print axioms equiv_store64Disp0
#print axioms len_shift
#print axioms rel32C_spec
#print axioms equiv_jump8_target
#print axioms equiv_aluImm8
#print axioms effAddr8_eq_effAddr
#print axioms kompaktWahl_movImm64
#print axioms kompaktWahl_load64
#print axioms kompaktWahl_store64
#print axioms kompaktWahl_jump32
#print axioms kompaktWahl_jumpIf32_genommen

end Gabbro.Grammatik.X86
