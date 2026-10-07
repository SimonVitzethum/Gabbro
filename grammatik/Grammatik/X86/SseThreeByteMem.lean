/-
  File:      Grammatik/X86/SseThreeByteMem.lean
  Subject:   Memory operands, MMX and REX.W forms of the SSSE3 three-byte
    maps over the 0F 38 / 0F 3A escapes.

  Lane 1377: Lane 1369 admitted register-direct XMM rows only
  (`SseThreeByte.lean`: PSHUFB `66 0F 38 00 /r`, PABSB/W/D
  `66 0F 38 1C/1D/1E /r`, PALIGNR `66 0F 3A 0F /r ib`). This file adds
  the three refused classes: memory-ModRM sources (ModRM with SIB,
  RIP-relative, disp8/disp32 through the accepted `AddressEncoding`
  vocabulary), MMX no-prefix forms (`NP 0F 38 ...`, `NP 0F 3A 0F`),
  and REX.W forms (silicon ignores REX.W on these rows). Semantics
  reuse the accepted lane vocabulary (`vecPabs`/`vecPshufb`/
  `vecPalignr`, never redefined); memory moves through the accepted
  `concLoad` TSO events. Silicon provenance: Intel SDM 325462-093US
  (Sep 2026), clone-local `.tmp/HARDWARE-REFERENCES/`
  `intel-instruction-reference.txt` (PABS 4-176, PALIGNR 4-216,
  PSHUFB 4-422).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Speicher.AddressEncoding
import Grammatik.X86.Befehle.Sse.SseThreeByte
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.TSO.Verriegelt.ConcurrentIntegerExecution
import Grammatik.X86.Flags.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- MMX registers mm0-mm7. Architecturally these alias the x87 stack;
    the coherent machine carries no MMX file, so MMX steps stay
    value-level in this file (see CUTS). -/
inductive MmxReg where
  | mm0 | mm1 | mm2 | mm3 | mm4 | mm5 | mm6 | mm7
  deriving DecidableEq, Repr

/-- Architectural MMX code: mm0=0 through mm7=7. -/
def mmCode : MmxReg → Nat
  | .mm0 => 0 | .mm1 => 1 | .mm2 => 2 | .mm3 => 3
  | .mm4 => 4 | .mm5 => 5 | .mm6 => 6 | .mm7 => 7

/-- Three-bit code back to an MMX register; extension bits are refused
    (under-admission: silicon has no mm8-mm15). -/
def codeMmx : Nat → Option MmxReg
  | 0 => some .mm0 | 1 => some .mm1 | 2 => some .mm2 | 3 => some .mm3
  | 4 => some .mm4 | 5 => some .mm5 | 6 => some .mm6 | 7 => some .mm7
  | _ => none

/-! ## 1. Covered forms: XMM memory, XMM REX.W register, MMX.

  Five SSSE3 rows (PSHUFB, PABSB/W/D, PALIGNR) in four classes:
  XMM with a memory source (`w` is the admitted REX.W bit, ignored
  by silicon), XMM register-direct with REX.W = 1 (the W=0 rows are
  owned by `SseThreeByte.lean`), MMX no-prefix register-direct, and
  MMX no-prefix with an m64 source (no alignment fault, SDM
  25.25.3 class). -/
inductive SseMemOp where
  | pshufbRM (w : Bool) (dst : XmmReg) (mem : AdrForm)
  | pabsBRM (w : Bool) (dst : XmmReg) (mem : AdrForm)
  | pabsWRM (w : Bool) (dst : XmmReg) (mem : AdrForm)
  | pabsDRM (w : Bool) (dst : XmmReg) (mem : AdrForm)
  | palignrRM (w : Bool) (dst : XmmReg) (mem : AdrForm) (imm : Byte)
  | pshufbRW (dst src : XmmReg)
  | pabsBRW (dst src : XmmReg)
  | pabsWRW (dst src : XmmReg)
  | pabsDRW (dst src : XmmReg)
  | palignrRW (dst src : XmmReg) (imm : Byte)
  | pshufbMM (dst src : MmxReg)
  | pabsBMM (dst src : MmxReg)
  | pabsWMM (dst src : MmxReg)
  | pabsDMM (dst src : MmxReg)
  | palignrMM (dst src : MmxReg) (imm : Byte)
  | pshufbMN (dst : MmxReg) (mem : AdrForm)
  | pabsBMN (dst : MmxReg) (mem : AdrForm)
  | pabsWMN (dst : MmxReg) (mem : AdrForm)
  | pabsDMN (dst : MmxReg) (mem : AdrForm)
  | palignrMN (dst : MmxReg) (mem : AdrForm) (imm : Byte)
  deriving DecidableEq, Repr

/-- Escape byte after `0F`: 56 (`0F 38`) for shuffle/abs, 58
    (`0F 3A`) for align-right. -/
def sseMemEscape : SseMemOp → Nat
  | .pshufbRM _ _ _ => 56 | .pabsBRM _ _ _ => 56
  | .pabsWRM _ _ _ => 56 | .pabsDRM _ _ _ => 56
  | .palignrRM _ _ _ _ => 58
  | .pshufbRW _ _ => 56 | .pabsBRW _ _ => 56
  | .pabsWRW _ _ => 56 | .pabsDRW _ _ => 56
  | .palignrRW _ _ _ => 58
  | .pshufbMM _ _ => 56 | .pabsBMM _ _ => 56
  | .pabsWMM _ _ => 56 | .pabsDMM _ _ => 56
  | .palignrMM _ _ _ => 58
  | .pshufbMN _ _ => 56 | .pabsBMN _ _ => 56
  | .pabsWMN _ _ => 56 | .pabsDMN _ _ => 56
  | .palignrMN _ _ _ => 58

/-- Third opcode byte: 0 PSHUFB, 28/29/30 PABSB/W/D, 15 PALIGNR. -/
def sseMemThird : SseMemOp → Nat
  | .pshufbRM _ _ _ => 0 | .pabsBRM _ _ _ => 28
  | .pabsWRM _ _ _ => 29 | .pabsDRM _ _ _ => 30
  | .palignrRM _ _ _ _ => 15
  | .pshufbRW _ _ => 0 | .pabsBRW _ _ => 28
  | .pabsWRW _ _ => 29 | .pabsDRW _ _ => 30
  | .palignrRW _ _ _ => 15
  | .pshufbMM _ _ => 0 | .pabsBMM _ _ => 28
  | .pabsWMM _ _ => 29 | .pabsDMM _ _ => 30
  | .palignrMM _ _ _ => 15
  | .pshufbMN _ _ => 0 | .pabsBMN _ _ => 28
  | .pabsWMN _ _ => 29 | .pabsDMN _ _ => 30
  | .palignrMN _ _ _ => 15

/-- No-prefix (MMX) class: no `66` byte is emitted or accepted. -/
def sseMemNP : SseMemOp → Bool
  | .pshufbRM _ _ _ => false | .pabsBRM _ _ _ => false
  | .pabsWRM _ _ _ => false | .pabsDRM _ _ _ => false
  | .palignrRM _ _ _ _ => false
  | .pshufbRW _ _ => false | .pabsBRW _ _ => false
  | .pabsWRW _ _ => false | .pabsDRW _ _ => false
  | .palignrRW _ _ _ => false
  | .pshufbMM _ _ => true | .pabsBMM _ _ => true
  | .pabsWMM _ _ => true | .pabsDMM _ _ => true
  | .palignrMM _ _ _ => true
  | .pshufbMN _ _ => true | .pabsBMN _ _ => true
  | .pabsWMN _ _ => true | .pabsDMN _ _ => true
  | .palignrMN _ _ _ => true

/-- The REX.W bit of one form: carried for XMM memory forms, 1 for
    XMM register REX.W forms, 0 for MMX (silicon ignores W here). -/
def sseMemW : SseMemOp → Nat
  | .pshufbRM w _ _ => if w then 1 else 0
  | .pabsBRM w _ _ => if w then 1 else 0
  | .pabsWRM w _ _ => if w then 1 else 0
  | .pabsDRM w _ _ => if w then 1 else 0
  | .palignrRM w _ _ _ => if w then 1 else 0
  | .pshufbRW _ _ => 1 | .pabsBRW _ _ => 1
  | .pabsWRW _ _ => 1 | .pabsDRW _ _ => 1
  | .palignrRW _ _ _ => 1
  | .pshufbMM _ _ => 0 | .pabsBMM _ _ => 0
  | .pabsWMM _ _ => 0 | .pabsDMM _ _ => 0
  | .palignrMM _ _ _ => 0
  | .pshufbMN _ _ => 0 | .pabsBMN _ _ => 0
  | .pabsWMN _ _ => 0 | .pabsDMN _ _ => 0
  | .palignrMN _ _ _ => 0

/-- Canonical tail (ModRM [+ SIB] [+ displacement]) of one admitted
    form for one reg field, REX excluded. This mirrors the accepted
    `encodeAdr` arm for arm (same shapes, same pilot refusals:
    base-only disp32 and SIB-36 disp32 stay refused); only the reg
    field differs (an XMM or MMX low code instead of a GPR). -/
def encodeMemTail (rl : Nat) (f : AdrForm) : Option (List Byte) :=
  match adrOk f with
  | false => none
  | true =>
    match f.base, f.index, f.art, f.rip with
    | none, none, .d32, true =>
      some (modrmByte 0 rl 5 :: leBytes32 f.disp)
    | none, none, .d32, false =>
      some (modrmByte 0 rl 4 :: sibByte 0 4 5 :: leBytes32 f.disp)
    | none, some idx, _, false =>
      match f.art with
      | .d32 =>
        some (modrmByte 0 rl 4 :: sibByte (skalaCode f.skala) (regLow idx) 5 :: leBytes32 f.disp)
      | _ => none
    | some b, none, _, false =>
      if regLow b == 4 then
        match f.art with
        | .kein => some [modrmByte 0 rl 4, sibByte 0 4 4]
        | .d8 => some (modrmByte 1 rl 4 :: sibByte 0 4 4 :: [natByte (f.disp.toNat % 256)])
        | .d32 => none
      else
        match f.art with
        | .kein => some [modrmByte 0 rl (regLow b)]
        | .d8 => some (modrmByte 1 rl (regLow b) :: [natByte (f.disp.toNat % 256)])
        | .d32 => none
    | some b, some idx, _, false =>
      match f.art with
      | .kein => some [modrmByte 0 rl 4, sibByte (skalaCode f.skala) (regLow idx) (regLow b)]
      | .d8 => some (modrmByte 1 rl 4 :: sibByte (skalaCode f.skala) (regLow idx) (regLow b) :: [natByte (f.disp.toNat % 256)])
      | .d32 => some (modrmByte 2 rl 4 :: sibByte (skalaCode f.skala) (regLow idx) (regLow b) :: leBytes32 f.disp)
    | _, _, _, _ => none

/-- Canonical byte encoding: REX (`0100WRXB`, always emitted), the
    `66` prefix for XMM only, `0F`, escape, third byte, the ModRM
    tail, plus the imm8 of PALIGNR. -/
def encodeSseMem : SseMemOp → Option (List Byte)
  | op@(.pshufbRM _w dst f) =>
    match encodeMemTail (xmmLow dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      some (natByte (64 + 8 * sseMemW op + 4 * xmmHigh dst + 2 * x + b) ::
        natByte 102 :: natByte 15 :: natByte (sseMemEscape op) ::
        natByte (sseMemThird op) :: tail)
  | op@(.pabsBRM _w dst f) =>
    match encodeMemTail (xmmLow dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      some (natByte (64 + 8 * sseMemW op + 4 * xmmHigh dst + 2 * x + b) ::
        natByte 102 :: natByte 15 :: natByte (sseMemEscape op) ::
        natByte (sseMemThird op) :: tail)
  | op@(.pabsWRM _w dst f) =>
    match encodeMemTail (xmmLow dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      some (natByte (64 + 8 * sseMemW op + 4 * xmmHigh dst + 2 * x + b) ::
        natByte 102 :: natByte 15 :: natByte (sseMemEscape op) ::
        natByte (sseMemThird op) :: tail)
  | op@(.pabsDRM _w dst f) =>
    match encodeMemTail (xmmLow dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      some (natByte (64 + 8 * sseMemW op + 4 * xmmHigh dst + 2 * x + b) ::
        natByte 102 :: natByte 15 :: natByte (sseMemEscape op) ::
        natByte (sseMemThird op) :: tail)
  | op@(.palignrRM _w dst f imm) =>
    match encodeMemTail (xmmLow dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      some (natByte (64 + 8 * sseMemW op + 4 * xmmHigh dst + 2 * x + b) ::
        natByte 102 :: natByte 15 :: natByte (sseMemEscape op) ::
        natByte (sseMemThird op) :: tail ++ [imm])
  | op@(.pshufbRW dst src) =>
    some [natByte (72 + 4 * xmmHigh dst + xmmHigh src), natByte 102,
      natByte 15, natByte (sseMemEscape op), natByte (sseMemThird op),
      modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsBRW dst src) =>
    some [natByte (72 + 4 * xmmHigh dst + xmmHigh src), natByte 102,
      natByte 15, natByte (sseMemEscape op), natByte (sseMemThird op),
      modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsWRW dst src) =>
    some [natByte (72 + 4 * xmmHigh dst + xmmHigh src), natByte 102,
      natByte 15, natByte (sseMemEscape op), natByte (sseMemThird op),
      modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsDRW dst src) =>
    some [natByte (72 + 4 * xmmHigh dst + xmmHigh src), natByte 102,
      natByte 15, natByte (sseMemEscape op), natByte (sseMemThird op),
      modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.palignrRW dst src imm) =>
    some [natByte (72 + 4 * xmmHigh dst + xmmHigh src), natByte 102,
      natByte 15, natByte (sseMemEscape op), natByte (sseMemThird op),
      modrmReg (xmmLow dst) (xmmLow src), imm]
  | op@(.pshufbMM dst src) =>
    some [natByte 64, natByte 15, natByte (sseMemEscape op),
      natByte (sseMemThird op), modrmReg (mmCode dst) (mmCode src)]
  | op@(.pabsBMM dst src) =>
    some [natByte 64, natByte 15, natByte (sseMemEscape op),
      natByte (sseMemThird op), modrmReg (mmCode dst) (mmCode src)]
  | op@(.pabsWMM dst src) =>
    some [natByte 64, natByte 15, natByte (sseMemEscape op),
      natByte (sseMemThird op), modrmReg (mmCode dst) (mmCode src)]
  | op@(.pabsDMM dst src) =>
    some [natByte 64, natByte 15, natByte (sseMemEscape op),
      natByte (sseMemThird op), modrmReg (mmCode dst) (mmCode src)]
  | op@(.palignrMM dst src imm) =>
    some [natByte 64, natByte 15, natByte (sseMemEscape op),
      natByte (sseMemThird op), modrmReg (mmCode dst) (mmCode src), imm]
  | op@(.pshufbMN dst f) =>
    match encodeMemTail (mmCode dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      if x == 0 && b == 0 then
        some (natByte 64 :: natByte 15 :: natByte (sseMemEscape op) ::
          natByte (sseMemThird op) :: tail)
      else none
  | op@(.pabsBMN dst f) =>
    match encodeMemTail (mmCode dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      if x == 0 && b == 0 then
        some (natByte 64 :: natByte 15 :: natByte (sseMemEscape op) ::
          natByte (sseMemThird op) :: tail)
      else none
  | op@(.pabsWMN dst f) =>
    match encodeMemTail (mmCode dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      if x == 0 && b == 0 then
        some (natByte 64 :: natByte 15 :: natByte (sseMemEscape op) ::
          natByte (sseMemThird op) :: tail)
      else none
  | op@(.pabsDMN dst f) =>
    match encodeMemTail (mmCode dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      if x == 0 && b == 0 then
        some (natByte 64 :: natByte 15 :: natByte (sseMemEscape op) ::
          natByte (sseMemThird op) :: tail)
      else none
  | op@(.palignrMN dst f imm) =>
    match encodeMemTail (mmCode dst) f with
    | none => none
    | some tail =>
      let x := match f.index with | some i => regHigh i | none => 0
      let b := match f.base with | some q => regHigh q | none => 0
      if x == 0 && b == 0 then
        some (natByte 64 :: natByte 15 :: natByte (sseMemEscape op) ::
          natByte (sseMemThird op) :: tail ++ [imm])
      else none

/-- Encoder spot-check: REX.W PSHUFB xmm1, xmm0 is six bytes. -/
theorem encodeSseMem_pshufbRW_pin :
    encodeSseMem (.pshufbRW .xmm1 .xmm0) =
      some [natByte 72, natByte 102, natByte 15, natByte 56,
        natByte 0, natByte 200] := by
  decide

/-- Encoder spot-check: PSHUFB xmm1, [rbx] without REX.W. -/
theorem encodeSseMem_pshufbRM_pin :
    encodeSseMem (.pshufbRM false .xmm1 (basisKeinForm .rbx)) =
      some [natByte 64, natByte 102, natByte 15, natByte 56,
        natByte 0, natByte 11] := by
  decide

/-- Encoder spot-check: MMX PABSB mm1, mm0 has no `66` prefix. -/
theorem encodeSseMem_pabsBMM_pin :
    encodeSseMem (.pabsBMM .mm1 .mm0) =
      some [natByte 64, natByte 15, natByte 56, natByte 28,
        natByte 200] := by
  decide

/-- Encoder spot-check: PABSB xmm2, [rbx + 5] tail. -/
theorem encodeSseMem_pabsBRM_pin :
    encodeSseMem (.pabsBRM false .xmm2 (basisDisp8Form .rbx (natByte 5))) =
      some [natByte 64, natByte 102, natByte 15, natByte 56,
        natByte 28, natByte 83, natByte 5] := by
  decide

/-- Encoder spot-check: REX.W PABSW xmm3, SIB tail. -/
theorem encodeSseMem_pabsWRM_pin :
    encodeSseMem (.pabsWRM true .xmm3
      (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 16) .d32)) =
      some [natByte 72, natByte 102, natByte 15, natByte 56,
        natByte 29, natByte 156, natByte 203, natByte 16, natByte 0,
        natByte 0, natByte 0] := by
  decide

/-- Encoder spot-check: PABSD xmm4, RIP-relative tail. -/
theorem encodeSseMem_pabsDRM_pin :
    encodeSseMem (.pabsDRM false .xmm4 (ripForm (BitVec.ofNat 32 4096))) =
      some [natByte 64, natByte 102, natByte 15, natByte 56,
        natByte 30, natByte 37, natByte 0, natByte 16, natByte 0,
        natByte 0] := by
  decide

/-- Encoder spot-check: PALIGNR xmm5, [rbx], 7 tail. -/
theorem encodeSseMem_palignrRM_pin :
    encodeSseMem (.palignrRM false .xmm5 (basisKeinForm .rbx)
      (natByte 7)) =
      some [natByte 64, natByte 102, natByte 15, natByte 58,
        natByte 15, natByte 43, natByte 7] := by
  decide

/-- Encoder spot-check: MMX PSHUFB mm1, [rbx] tail. -/
theorem encodeSseMem_pshufbMN_pin :
    encodeSseMem (.pshufbMN .mm1 (basisKeinForm .rbx)) =
      some [natByte 64, natByte 15, natByte 56, natByte 0,
        natByte 11] := by
  decide

/-- Encoder spot-check: MMX PALIGNR mm5, [rbx], 7 tail. -/
theorem encodeSseMem_palignrMN_pin :
    encodeSseMem (.palignrMN .mm5 (basisKeinForm .rbx) (natByte 7)) =
      some [natByte 64, natByte 15, natByte 58, natByte 15,
        natByte 43, natByte 7] := by
  decide

/-! ## 2. Canonical decoder.

  The decoder parses bytes, never encode-equality. A canonical REX
  prefix (`0100WRXB`) is always required. Behind it, `66` selects the
  XMM class and a bare `0F` the MMX class; then `0F`, the escape
  (`38`/`3A`), the third byte, and the ModRM tail. Register-direct
  (mod=3) is admitted only with REX.W = 1 (XMM) or in the MMX class
  (the W=0 XMM rows are owned by `SseThreeByte.lean`); memory tails
  reuse the accepted `sibReg`/`codeReg`/`parseLe32` leaf vocabulary
  with the same pilot refusals as `parseAdrTail` (mod=2 non-SIB and
  SIB-36 disp32 stay refused). MMX admits W in {0,1} but requires
  R=X=B=0 (under-admission: silicon has no mm8-mm15). PALIGNR reads
  its imm8 behind the tail. -/

/-- A decoded new form: the form plus its decode length (checked
    `1..15` data, exactly as the pilot `Decodiert`). -/
structure SseMemDec where
  op : SseMemOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- Register-direct XMM constructor (REX.W rows only). -/
def regOpXmm (esc third : Nat) (dst src : XmmReg)
    (imm : Option Byte) : Option SseMemOp :=
  match esc, third, imm with
  | 56, 0, _ => some (.pshufbRW dst src)
  | 56, 28, _ => some (.pabsBRW dst src)
  | 56, 29, _ => some (.pabsWRW dst src)
  | 56, 30, _ => some (.pabsDRW dst src)
  | 58, 15, some i => some (.palignrRW dst src i)
  | _, _, _ => none

/-- Register-direct MMX constructor. -/
def regOpMmx (esc third : Nat) (dst src : MmxReg)
    (imm : Option Byte) : Option SseMemOp :=
  match esc, third, imm with
  | 56, 0, _ => some (.pshufbMM dst src)
  | 56, 28, _ => some (.pabsBMM dst src)
  | 56, 29, _ => some (.pabsWMM dst src)
  | 56, 30, _ => some (.pabsDMM dst src)
  | 58, 15, some i => some (.palignrMM dst src i)
  | _, _, _ => none

/-- Memory-source XMM constructor. -/
def memOpXmm (w : Bool) (esc third : Nat) (dst : XmmReg)
    (f : AdrForm) (imm : Option Byte) : Option SseMemOp :=
  match esc, third, imm with
  | 56, 0, _ => some (.pshufbRM w dst f)
  | 56, 28, _ => some (.pabsBRM w dst f)
  | 56, 29, _ => some (.pabsWRM w dst f)
  | 56, 30, _ => some (.pabsDRM w dst f)
  | 58, 15, some i => some (.palignrRM w dst f i)
  | _, _, _ => none

/-- Memory-source MMX constructor. -/
def memOpMmx (esc third : Nat) (dst : MmxReg)
    (f : AdrForm) (imm : Option Byte) : Option SseMemOp :=
  match esc, third, imm with
  | 56, 0, _ => some (.pshufbMN dst f)
  | 56, 28, _ => some (.pabsBMN dst f)
  | 56, 29, _ => some (.pabsWMN dst f)
  | 56, 30, _ => some (.pabsDMN dst f)
  | 58, 15, some i => some (.palignrMN dst f i)
  | _, _, _ => none

/-- Parse one memory ModRM/SIB/displacement tail under REX bits X/B
    into the selected form and the remaining bytes. This mirrors the
    accepted `parseAdrTail` mod=0/1/2 arms exactly (same shapes, same
    pilot refusals); only the reg field is left to the caller. -/
def parseSseMemRM (x b mod rm : Nat) :
    List Byte → Option (AdrForm × List Byte)
  | rest =>
    if mod == 2 then
      if rm == 4 then
        match rest with
        | [] => none
        | sib :: rest2 =>
          if byteNat sib == 36 && x == 0 then none
          else
            let sk := byteNat sib / 64
            let ii := byteNat sib / 8 % 8
            let bb := byteNat sib % 8
            match sibReg x ii, codeReg (b * 8 + bb) with
            | some idxO, some baseR =>
              match parseLe32 rest2 with
              | some (d, rest3) =>
                some (⟨some baseR, idxO, codeSkala sk, d, .d32, false⟩, rest3)
              | none => none
            | _, _ => none
      else none
    else if mod == 1 then
      if rm == 4 then
        match rest with
        | [] => none
        | _ :: [] => none
        | sib :: e :: rest2 =>
          let sk := byteNat sib / 64
          let ii := byteNat sib / 8 % 8
          let bb := byteNat sib % 8
          match sibReg x ii, codeReg (b * 8 + bb) with
          | some idxO, some baseR =>
            some (⟨some baseR, idxO, codeSkala sk, u8Nach32 e, .d8, false⟩, rest2)
          | _, _ => none
      else
        match rest with
        | [] => none
        | e :: rest2 =>
          match codeReg (b * 8 + rm) with
          | some baseR =>
            some (⟨some baseR, none, 1, u8Nach32 e, .d8, false⟩, rest2)
          | none => none
    else if mod == 0 then
      if rm == 5 then
        match parseLe32 rest with
        | some (d, rest') => some (ripForm d, rest')
        | none => none
      else if rm == 4 then
        match rest with
        | [] => none
        | sib :: rest2 =>
          let sk := byteNat sib / 64
          let ii := byteNat sib / 8 % 8
          let bb := byteNat sib % 8
          if bb == 5 then
            match sibReg x ii, parseLe32 rest2 with
            | some idxO, some (d, rest3) =>
              some (⟨none, idxO, codeSkala sk, d, .d32, false⟩, rest3)
            | _, _ => none
          else
            match sibReg x ii, codeReg (b * 8 + bb) with
            | some idxO, some baseR =>
              some (⟨some baseR, idxO, codeSkala sk, BitVec.ofNat 32 0, .kein, false⟩, rest2)
            | _, _ => none
      else
        match codeReg (b * 8 + rm) with
        | some baseR =>
          some (⟨some baseR, none, 1, BitVec.ofNat 32 0, .kein, false⟩, rest)
        | none => none
    else none

/-- Decode one ModRM tail: register-direct only with REX.W = 1
    (XMM) or in the MMX class, memory otherwise. -/
def decodeSseMemTail (np : Bool) (w r x b esc third : Nat) :
    List Byte → Option (SseMemOp × List Byte)
  | [] => none
  | m :: rest =>
    let mod := byteNat m / 64
    let rg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if np then
      if r == 0 && x == 0 && b == 0 then
        match codeMmx rg with
        | none => none
        | some dst =>
          if mod == 3 then
            match codeMmx rm with
            | none => none
            | some src =>
              if esc == 58 && third == 15 then
                match rest with
                | [] => none
                | imm :: rest2 =>
                  match regOpMmx esc third dst src (some imm) with
                  | some op => some (op, rest2)
                  | none => none
              else
                match regOpMmx esc third dst src none with
                | some op => some (op, rest)
                | none => none
          else
            match parseSseMemRM x b mod rm rest with
            | none => none
            | some (f, rest2) =>
              if esc == 58 && third == 15 then
                match rest2 with
                | [] => none
                | imm :: rest3 =>
                  match memOpMmx esc third dst f (some imm) with
                  | some op => some (op, rest3)
                  | none => none
              else
                match memOpMmx esc third dst f none with
                | some op => some (op, rest2)
                | none => none
      else none
    else
      match codeXmm (r * 8 + rg) with
      | none => none
      | some dst =>
        if mod == 3 then
          if w == 1 then
            match codeXmm (b * 8 + rm) with
            | none => none
            | some src =>
              if esc == 58 && third == 15 then
                match rest with
                | [] => none
                | imm :: rest2 =>
                  match regOpXmm esc third dst src (some imm) with
                  | some op => some (op, rest2)
                  | none => none
              else
                match regOpXmm esc third dst src none with
                | some op => some (op, rest)
                | none => none
          else none
        else
          match parseSseMemRM x b mod rm rest with
          | none => none
          | some (f, rest2) =>
            if esc == 58 && third == 15 then
              match rest2 with
              | [] => none
              | imm :: rest3 =>
                match memOpXmm (w == 1) esc third dst f (some imm) with
                | some op => some (op, rest3)
                | none => none
            else
              match memOpXmm (w == 1) esc third dst f none with
              | some op => some (op, rest2)
              | none => none

/-- Decode after the class prefix: `0F`, the escape byte, the third
    byte, then the ModRM tail. -/
def decodeSseMemNach (np : Bool) (w r x b : Nat) :
    List Byte → Option (SseMemOp × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 15 then
      match rest with
      | [] => none
      | esc :: rest2 =>
        if byteNat esc == 56 || byteNat esc == 58 then
          match rest2 with
          | [] => none
          | op :: rest3 =>
            decodeSseMemTail np w r x b (byteNat esc) (byteNat op) rest3
        else none
    else none

/-- Top-level decode: the REX prefix selects W/R/X/B; `66` behind it
    selects XMM, a bare `0F` the MMX class. The decoded length is the
    consumed byte count. -/
def decodeSseMem : List Byte → Option (SseMemDec × List Byte)
  | [] => none
  | r :: tail =>
    if 64 ≤ byteNat r && byteNat r < 80 then
      let vv := byteNat r - 64
      let w := vv / 8
      let rr := vv / 4 % 2
      let xx := vv / 2 % 2
      let bb := vv % 2
      let weiter (np : Bool) (bs : List Byte) :=
        match decodeSseMemNach np w rr xx bb bs with
        | some (op, rest) =>
          match encodeSseMem op with
          | some canon => some (⟨op, canon.length⟩, rest)
          | none => none
        | none => none
      match tail with
      | [] => none
      | p0 :: rest0 =>
        if byteNat p0 == 102 then weiter false rest0
        else if byteNat p0 == 15 then weiter true tail
        else none
    else none

/-! ## 3. Round trips for the register forms.

  Every register-direct form (XMM REX.W and MMX) decodes from its
  canonical bytes over any suffix; the decoded length is the
  canonical encoding length. Memory forms round-trip per shape
  (§3b): a general inversion over open `AdrForm` would need a
  general `parse ∘ encode = id` the accepted `AddressEncoding`
  never proved (its encoder is lossy on non-canonical disp
  bytes), so memory rows are pinned per canonical constructor. -/

/-- Round trip for REX.W PSHUFB, over any suffix. -/
theorem roundtrip_pshufbRW (dst src : XmmReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pshufbRW dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pshufbRW dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for REX.W PABSB, over any suffix. -/
theorem roundtrip_pabsBRW (dst src : XmmReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pabsBRW dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pabsBRW dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for REX.W PABSW, over any suffix. -/
theorem roundtrip_pabsWRW (dst src : XmmReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pabsWRW dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pabsWRW dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for REX.W PABSD, over any suffix. -/
theorem roundtrip_pabsDRW (dst src : XmmReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pabsDRW dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pabsDRW dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for REX.W PALIGNR, over any suffix. -/
theorem roundtrip_palignrRW (dst src : XmmReg) (imm : Byte)
    (suffix : List Byte) :
    ∃ bs, encodeSseMem (.palignrRW dst src imm) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.palignrRW dst src imm, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for MMX PSHUFB, over any suffix. -/
theorem roundtrip_pshufbMM (dst src : MmxReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pshufbMM dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pshufbMM dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for MMX PABSB, over any suffix. -/
theorem roundtrip_pabsBMM (dst src : MmxReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pabsBMM dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pabsBMM dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for MMX PABSW, over any suffix. -/
theorem roundtrip_pabsWMM (dst src : MmxReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pabsWMM dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pabsWMM dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for MMX PABSD, over any suffix. -/
theorem roundtrip_pabsDMM (dst src : MmxReg) (suffix : List Byte) :
    ∃ bs, encodeSseMem (.pabsDMM dst src) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.pabsDMM dst src, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-- Round trip for MMX PALIGNR, over any suffix. -/
theorem roundtrip_palignrMM (dst src : MmxReg) (imm : Byte)
    (suffix : List Byte) :
    ∃ bs, encodeSseMem (.palignrMM dst src imm) = some bs ∧
      decodeSseMem (bs ++ suffix) =
        some (⟨.palignrMM dst src imm, bs.length⟩, suffix) := by
  cases dst <;> cases src <;> exact ⟨_, rfl, rfl⟩

/-! ## 3b. Memory round-trip pins, one per constructor.

  Each pin states the exact canonical bytes (hand-computed from the
  REX/ModRM/SIB rules) and checks both directions by `decide`:
  the old chain refuses them (§6 reuses these), the new decoder
  takes them with the canonical length. Shapes: base without
  displacement, base plus disp8, scaled SIB plus disp32,
  RIP-relative, and a high-register REX row. -/

/-- PSHUFB xmm1, [rbx]: base without displacement. -/
theorem pin_pshufbRM :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 11] =
      some (⟨.pshufbRM false .xmm1 (basisKeinForm .rbx), 6⟩, []) := by
  decide

/-- PABSB xmm2, [rbx + 5]: base plus disp8. -/
theorem pin_pabsBRM :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 28, natByte 83, natByte 5] =
      some (⟨.pabsBRM false .xmm2
        (basisDisp8Form .rbx (natByte 5)), 7⟩, []) := by
  decide

/-- PABSW xmm3, [rbx + rcx*8 + 16] with REX.W: scaled SIB plus
    disp32, W admitted. -/
theorem pin_pabsWRM :
    decodeSseMem [natByte 72, natByte 102, natByte 15, natByte 56,
      natByte 29, natByte 156, natByte 203, natByte 16, natByte 0,
      natByte 0, natByte 0] =
      some (⟨.pabsWRM true .xmm3
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 16) .d32), 11⟩, []) := by
  decide

/-- PABSD xmm4, [rip + 4096]: RIP-relative. -/
theorem pin_pabsDRM :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 30, natByte 37, natByte 0, natByte 16, natByte 0,
      natByte 0] =
      some (⟨.pabsDRM false .xmm4 (ripForm (BitVec.ofNat 32 4096)),
        10⟩, []) := by
  decide

/-- PALIGNR xmm5, [rbx], 7: base without displacement plus imm8. -/
theorem pin_palignrRM :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 43, natByte 7] =
      some (⟨.palignrRM false .xmm5 (basisKeinForm .rbx)
        (natByte 7), 7⟩, []) := by
  decide

/-- PSHUFB xmm9, [r8] with REX.W: high registers on both sides. -/
theorem pin_pshufbRM_hoch :
    decodeSseMem [natByte 77, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 8] =
      some (⟨.pshufbRM true .xmm9 (basisKeinForm .r8), 6⟩, []) := by
  decide

/-- MMX PSHUFB mm1, [rbx]: no `66`, five bytes. -/
theorem pin_pshufbMN :
    decodeSseMem [natByte 64, natByte 15, natByte 56, natByte 0,
      natByte 11] =
      some (⟨.pshufbMN .mm1 (basisKeinForm .rbx), 5⟩, []) := by
  decide

/-- MMX PABSB mm2, [rbx + 5]: base plus disp8. -/
theorem pin_pabsBMN :
    decodeSseMem [natByte 64, natByte 15, natByte 56, natByte 28,
      natByte 83, natByte 5] =
      some (⟨.pabsBMN .mm2 (basisDisp8Form .rbx (natByte 5)), 6⟩, []) := by
  decide

/-- MMX PABSW mm3, [rbx + rcx*8 + 16]: scaled SIB plus disp32. -/
theorem pin_pabsWMN :
    decodeSseMem [natByte 64, natByte 15, natByte 56, natByte 29,
      natByte 156, natByte 203, natByte 16, natByte 0, natByte 0,
      natByte 0] =
      some (⟨.pabsWMN .mm3
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 16) .d32), 10⟩, []) := by
  decide

/-- MMX PABSD mm4, [rip + 4096]: RIP-relative. -/
theorem pin_pabsDMN :
    decodeSseMem [natByte 64, natByte 15, natByte 56, natByte 30,
      natByte 37, natByte 0, natByte 16, natByte 0, natByte 0] =
      some (⟨.pabsDMN .mm4 (ripForm (BitVec.ofNat 32 4096)), 9⟩, []) := by
  decide

/-- MMX PALIGNR mm5, [rbx], 7: base plus imm8. -/
theorem pin_palignrMN :
    decodeSseMem [natByte 64, natByte 15, natByte 58, natByte 15,
      natByte 43, natByte 7] =
      some (⟨.palignrMN .mm5 (basisKeinForm .rbx) (natByte 7), 6⟩, []) := by
  decide

/-! ## 3c. Planted decoder refusals.

  A W=0 XMM register-direct row belongs to `SseThreeByte.lean`;
  truncated prefixes, a wrong escape, the pilot-owned mod=2
  non-SIB shape, a missing PALIGNR imm8, a missing REX, a
  no-REX MMX row, MMX extension bits, and foreign third bytes
  (MOVBE) are all refused. -/

/-- A W=0 XMM register-direct row is refused (old lane owns it). -/
theorem sseMem_nichts_w0reg :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := rfl

/-- A truncated prefix (REX + `66` only) is refused. -/
theorem sseMem_nichts_kurz :
    decodeSseMem [natByte 72, natByte 102] = none := rfl

/-- A wrong escape (`0F 39`) is refused. -/
theorem sseMem_nichts_escape :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 57,
      natByte 0, natByte 11] = none := rfl

/-- The pilot-owned mod=2 non-SIB shape (base plus disp32) is
    refused. -/
theorem sseMem_nichts_pilot :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 139, natByte 5, natByte 0, natByte 0,
      natByte 0] = none := rfl

/-- PALIGNR without its imm8 is refused. -/
theorem sseMem_nichts_ohne_imm :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 43] = none := rfl

/-- A first byte without REX is refused. -/
theorem sseMem_nichts_ohne_rex :
    decodeSseMem [natByte 102, natByte 15, natByte 56, natByte 0,
      natByte 200] = none := rfl

/-- A no-REX MMX row is refused (canonical REX always required). -/
theorem sseMem_nichts_mmx_ohne_rex :
    decodeSseMem [natByte 15, natByte 56, natByte 28,
      natByte 200] = none := rfl

/-- MMX with a REX extension bit (R here) is refused. -/
theorem sseMem_nichts_mmx_erweitert :
    decodeSseMem [natByte 68, natByte 15, natByte 56, natByte 28,
      natByte 200] = none := rfl

/-- MOVBE (`0F 38 F0`) is refused: a different family owns it. -/
theorem sseMem_nichts_movbe :
    decodeSseMem [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 240, natByte 11] = none := rfl

/-! ## 4. Alignment gates and MMX lane semantics.

  A 128-bit XMM memory source must be 16-byte aligned, else #GP
  (SDM PSHUFB 4-422, PALIGNR 4-216: "must be aligned on a 16-byte
  boundary or a general-protection exception (#GP) will be
  generated"). An m64 MMX source never faults on alignment (legacy
  MMX exception class, SDM 25.25.3 note). XMM value semantics reuse
  the accepted `vecPabs`/`vecPshufb`/`vecPalignr` unchanged; MMX
  64-bit semantics are new but built from the same accepted
  `laneNat`/`vecMk`/`pabsLane` vocabulary on the low lanes only
  (PSHUFB indexes low 3 bits, PALIGNR zeroes past a count of 16). -/

/-- Alignment need of one form: XMM memory sources only. -/
def sseMemBrauchtAusrichtung : SseMemOp → Bool
  | .pshufbRM _ _ _ => true | .pabsBRM _ _ _ => true
  | .pabsWRM _ _ _ => true | .pabsDRM _ _ _ => true
  | .palignrRM _ _ _ _ => true
  | _ => false

/-- #GP predicate of one form at one address: XMM memory sources
    fault exactly on 16-byte-misaligned addresses. -/
def sseMemGp (op : SseMemOp) (a : Adresse) : Bool :=
  if sseMemBrauchtAusrichtung op then decide (a.toNat % 16 ≠ 0)
  else false

/-- An aligned XMM source never faults. -/
theorem sseMemGp_ausgerichtet_ok (op : SseMemOp)
    (h : sseMemBrauchtAusrichtung op = true) :
    sseMemGp op (BitVec.ofNat 64 12288) = false := by
  unfold sseMemGp
  rw [h]
  decide

/-- A misaligned XMM source faults. -/
theorem sseMemGp_fehltritt (op : SseMemOp)
    (h : sseMemBrauchtAusrichtung op = true) :
    sseMemGp op (BitVec.ofNat 64 12289) = true := by
  unfold sseMemGp
  rw [h]
  decide

/-- No MMX form ever faults on alignment, at any address. -/
theorem sseMemGp_nie_mmx (dst : MmxReg) (f : AdrForm)
    (a : Adresse) :
    sseMemGp (.pshufbMN dst f) a = false ∧
      sseMemGp (.pabsBMN dst f) a = false ∧
      sseMemGp (.pabsWMN dst f) a = false ∧
      sseMemGp (.pabsDMN dst f) a = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold sseMemGp sseMemBrauchtAusrichtung <;> rfl

/-- No REX.W register form touches memory, so none faults. -/
theorem sseMemGp_nie_reg (dst src : XmmReg) (a : Adresse) :
    sseMemGp (.pshufbRW dst src) a = false := by
  unfold sseMemGp sseMemBrauchtAusrichtung
  rfl

/-- Forwarding-aware 128-bit source load: two ordered 8-byte
    `concLoad` chunks through the shared TSO view, joined low-first
    exactly like the accepted `vecRead` chunks. -/
def sseMemLade (s : TSOZustand) (c : Nat) (a : Adresse) :
    Option Vektor :=
  match concLoad s c .b64 a, concLoad s c .b64 (vecHiAddr a) with
  | some lo, some hi => some (vecJoin lo hi)
  | _, _ => none

/-- A refused low chunk refuses the whole source load. -/
theorem sseMemLade_verweigert_lo (s : TSOZustand) (c : Nat)
    (a : Adresse)
    (h : concLoad s c .b64 a = none) :
    sseMemLade s c a = none := by
  unfold sseMemLade
  rw [h]

/-- A refused high chunk refuses the whole source load. -/
theorem sseMemLade_verweigert_hi (s : TSOZustand) (c : Nat)
    (a : Adresse) (lo : Wort)
    (h1 : concLoad s c .b64 a = some lo)
    (h2 : concLoad s c .b64 (vecHiAddr a) = none) :
    sseMemLade s c a = none := by
  unfold sseMemLade
  rw [h1, h2]

/-- A successful source load is the joined halves. -/
theorem sseMemLade_ok (s : TSOZustand) (c : Nat) (a : Adresse)
    (lo hi : Wort)
    (h1 : concLoad s c .b64 a = some lo)
    (h2 : concLoad s c .b64 (vecHiAddr a) = some hi) :
    sseMemLade s c a = some (vecJoin lo hi) := by
  unfold sseMemLade
  rw [h1, h2]

/-- MMX shuffle (PSHUFB mm): low-3-bit indices over the low eight
    lanes, zero above (MMX values live in bits 63:0). -/
def mmPshufb (dst src : Vektor) : Vektor :=
  vecMk .b8 (fun i =>
    if i < 8 then
      let c := laneNat .b8 src i
      if c / 128 = 1 then 0 else laneNat .b8 dst (c % 8)
    else 0)

/-- MMX absolute value (PABSB/W/D mm) at width `b`: low half only. -/
def mmPabs (b : Breite) (x : Vektor) : Vektor :=
  vecMk b (fun i =>
    if i < laneCount b / 2 then pabsLane b (laneNat b x i) else 0)

/-- MMX align right (PALIGNR mm): the 128-bit `DEST:SRC` composite
    shifted right by `imm8*8`, low 64 bits; counts past 16 zero. -/
def mmPalignr (dst src : Vektor) (imm : Byte) : Vektor :=
  vecMk .b8 (fun i =>
    if i < 8 then
      let j := i + byteNat imm
      if j < 8 then laneNat .b8 src j
      else if j < 16 then laneNat .b8 dst (j - 8)
      else 0
    else 0)

/-- Per-lane MMX shuffle is the 3-bit control function. -/
theorem laneNat_mmPshufb (dst src : Vektor) (i : Nat)
    (hi : i < laneCount .b8) (h8 : i < 8) :
    laneNat .b8 (mmPshufb dst src) i =
      ((let c := laneNat .b8 src i
        if c / 128 = 1 then 0 else laneNat .b8 dst (c % 8)) %
        2 ^ Breite.b8.bits) := by
  unfold mmPshufb
  rw [laneGet_mk .b8 _ i hi, if_pos h8]

/-- High lanes of an MMX shuffle are zero. -/
theorem laneNat_mmPshufb_hoch (dst src : Vektor) (i : Nat)
    (hi : i < laneCount .b8) (h8 : 8 ≤ i) :
    laneNat .b8 (mmPshufb dst src) i = 0 := by
  unfold mmPshufb
  rw [laneGet_mk .b8 _ i hi, if_neg (by omega), Nat.zero_mod]

/-- Per-lane MMX absolute value is the lane function. -/
theorem laneNat_mmPabs (b : Breite) (x : Vektor) (i : Nat)
    (hi : i < laneCount b) (hh : i < laneCount b / 2) :
    laneNat b (mmPabs b x) i =
      pabsLane b (laneNat b x i) % 2 ^ b.bits := by
  unfold mmPabs
  rw [laneGet_mk b _ i hi, if_pos hh]

/-- High lanes of an MMX absolute value are zero. -/
theorem laneNat_mmPabs_hoch (b : Breite) (x : Vektor) (i : Nat)
    (hi : i < laneCount b) (hh : laneCount b / 2 ≤ i) :
    laneNat b (mmPabs b x) i = 0 := by
  unfold mmPabs
  rw [laneGet_mk b _ i hi, if_neg (by omega), Nat.zero_mod]

/-- Per-lane MMX align is the composite byte. -/
theorem laneNat_mmPalignr (dst src : Vektor) (imm : Byte) (i : Nat)
    (hi : i < laneCount .b8) (h8 : i < 8) :
    laneNat .b8 (mmPalignr dst src imm) i =
      ((let j := i + byteNat imm
        if j < 8 then laneNat .b8 src j
        else if j < 16 then laneNat .b8 dst (j - 8)
        else 0) % 2 ^ Breite.b8.bits) := by
  unfold mmPalignr
  rw [laneGet_mk .b8 _ i hi, if_pos h8]

/-- High lanes of an MMX align are zero. -/
theorem laneNat_mmPalignr_hoch (dst src : Vektor) (imm : Byte)
    (i : Nat) (hi : i < laneCount .b8) (h8 : 8 ≤ i) :
    laneNat .b8 (mmPalignr dst src imm) i = 0 := by
  unfold mmPalignr
  rw [laneGet_mk .b8 _ i hi, if_neg (by omega), Nat.zero_mod]

/-- Silicon spot-check: a 3-bit index selects (control 9 reads lane
    1, unlike the 4-bit XMM form), bit 7 zeroes. -/
theorem mmPshufb_silicon :
    laneNat .b8 (mmPshufb (vecMk .b8 (fun i => i))
      (vecMk .b8 (fun _ => 9))) 0 = 1 ∧
    laneNat .b8 (mmPshufb (vecMk .b8 (fun i => i))
      (vecMk .b8 (fun _ => 128))) 0 = 0 := by
  decide

/-- Silicon spot-check: MMX absolute value at the low lanes, zero
    above. -/
theorem mmPabs_silicon :
    laneNat .b8 (mmPabs .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else 5))) 0 = 1 ∧
    laneNat .b8 (mmPabs .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else 5))) 1 = 5 ∧
    laneNat .b8 (mmPabs .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else 5))) 8 = 0 := by
  decide

/-- Silicon spot-check: MMX align shifts the 16-byte composite and
    zeroes past a count of 16. -/
theorem mmPalignr_silicon :
    laneNat .b8 (mmPalignr (vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun _ => 3)) (natByte 1)) 0 = 3 ∧
    laneNat .b8 (mmPalignr (vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun _ => 3)) (natByte 8)) 0 = 7 ∧
    laneNat .b8 (mmPalignr (vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun _ => 3)) (natByte 16)) 0 = 0 := by
  decide

/-- The XMM destination register one form writes (`none` for the
    MMX value-level forms, which have no machine step here). -/
def sseMemDstX : SseMemOp → Option XmmReg
  | .pshufbRM _ dst _ => some dst | .pabsBRM _ dst _ => some dst
  | .pabsWRM _ dst _ => some dst | .pabsDRM _ dst _ => some dst
  | .palignrRM _ dst _ _ => some dst
  | .pshufbRW dst _ => some dst | .pabsBRW dst _ => some dst
  | .pabsWRW dst _ => some dst | .pabsDRW dst _ => some dst
  | .palignrRW dst _ _ => some dst
  | _ => none

/-! ## 5. Machine adapter: the XMM family on the coherent machine.

  The producer plug instantiates `HwAdapter SseMemDec`. Memory
  sources load through the accepted `sseMemLade` TSO events at the
  `adrEff` address (with the #GP gate beside the load); REX.W
  register forms reuse the accepted lane values on the pre-state
  XMM file. MMX forms admit no step (`none`): the coherent
  `HwKern` carries no MMX file, so there is no state to move
  (see CUTS for the maintainer hook). -/

/-- Advance RIP on an extended state (variable target, exactly like
    the `stepSseThree` successor updates). -/
def sseMemNachKern (t : FpZustand) (l : Nat) : Zustand :=
  { t.kern with rip := ripNach t.kern.rip l }

/-- Install a successor XMM value with advanced RIP. -/
def sseMemNach (t : FpZustand) (l : Nat) (x : XmmDatei) : FpZustand :=
  { t with kern := sseMemNachKern t l, xmm := x }

/-- The new-forms plug: one checked family event step on the
    coherent machine. `none` = refusal, never a silent successor. -/
def adapterSseMem : HwAdapter SseMemDec :=
  ⟨fun m c d =>
    match laengeOk d.laenge with
    | false => none
    | true =>
      match vecEintritt (m.bereit c) with
      | false => none
      | true =>
        match d.op with
        | .pshufbRM w dst f =>
          match sseMemGp (.pshufbRM w dst f)
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f),
            sseMemLade (tsoAnsicht m) c
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f) with
          | false, some v =>
            some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst
                (vecPshufb ((projFp m c).xmm dst) v))))
          | _, _ => none
        | .pabsBRM w dst f =>
          match sseMemGp (.pabsBRM w dst f)
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f),
            sseMemLade (tsoAnsicht m) c
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f) with
          | false, some v =>
            some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst (vecPabs .b8 v))))
          | _, _ => none
        | .pabsWRM w dst f =>
          match sseMemGp (.pabsWRM w dst f)
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f),
            sseMemLade (tsoAnsicht m) c
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f) with
          | false, some v =>
            some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst (vecPabs .b16 v))))
          | _, _ => none
        | .pabsDRM w dst f =>
          match sseMemGp (.pabsDRM w dst f)
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f),
            sseMemLade (tsoAnsicht m) c
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f) with
          | false, some v =>
            some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst (vecPabs .b32 v))))
          | _, _ => none
        | .palignrRM w dst f imm =>
          match sseMemGp (.palignrRM w dst f imm)
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f),
            sseMemLade (tsoAnsicht m) c
              (adrEff (projFp m c).kern
                (ripNach (projFp m c).kern.rip d.laenge) f) with
          | false, some v =>
            some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst
                (vecPalignr ((projFp m c).xmm dst) v imm))))
          | _, _ => none
        | .pshufbRW dst src =>
          some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst
              (vecPshufb ((projFp m c).xmm dst) ((projFp m c).xmm src)))))
        | .pabsBRW dst src =>
          some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst
              (vecPabs .b8 ((projFp m c).xmm src)))))
        | .pabsWRW dst src =>
          some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst
              (vecPabs .b16 ((projFp m c).xmm src)))))
        | .pabsDRW dst src =>
          some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst
              (vecPabs .b32 ((projFp m c).xmm src)))))
        | .palignrRW dst src imm =>
          some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge (xmmSet (projFp m c).xmm dst
              (vecPalignr ((projFp m c).xmm dst)
                ((projFp m c).xmm src) imm))))
        | _ => none⟩

/-- Re-embedding any successor core view preserves
    well-formedness (profiles untouched). -/
theorem setKernVonFp_wf (m : HwMaschine) (c : Nat) (t' : FpZustand)
    (hwf : HwWf m) : HwWf (setKernVonFp m c t') := by
  unfold setKernVonFp
  exact setKernDaten_wf _ _ _ hwf

/-- Every successful adapter step re-embeds one successor core
    view: only core data moves. -/
theorem adapterSseMem_form (m : HwMaschine) (c : Nat)
    (d : SseMemDec) (m' : HwMaschine)
    (h : (adapterSseMem).schritt m c d = some m') :
    ∃ t' : FpZustand, m' = setKernVonFp m c t' := by
  unfold adapterSseMem at h
  simp only at h
  cases hlen : laengeOk d.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hfp : vecEintritt (m.bereit c) with
    | false => simp [hfp] at h
    | true =>
      simp only [hfp] at h
      cases hop : d.op with
      | pshufbRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pshufbRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pabsBRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pabsBRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pabsWRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pabsWRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pabsDRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pabsDRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | palignrRM w dst f imm =>
        simp [hop] at h
        cases hg : sseMemGp (.palignrRM w dst f imm)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pshufbRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pabsBRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pabsWRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pabsDRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | palignrRW dst src imm =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pshufbMM dst src =>
        simp [hop] at h
      | pabsBMM dst src =>
        simp [hop] at h
      | pabsWMM dst src =>
        simp [hop] at h
      | pabsDMM dst src =>
        simp [hop] at h
      | palignrMM dst src imm =>
        simp [hop] at h
      | pshufbMN dst f =>
        simp [hop] at h
      | pabsBMN dst f =>
        simp [hop] at h
      | pabsWMN dst f =>
        simp [hop] at h
      | pabsDMN dst f =>
        simp [hop] at h
      | palignrMN dst f imm =>
        simp [hop] at h

/-- Every adapter step preserves well-formedness. -/
theorem adapterSseMem_wf (m : HwMaschine) (c : Nat)
    (d : SseMemDec) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterSseMem).schritt m c d = some m') :
    HwWf m' := by
  obtain ⟨t', rfl⟩ := adapterSseMem_form m c d m' h
  exact setKernVonFp_wf m c t' hwf

/-- The successor keeps the shared memory and every buffer. -/
theorem adapterSseMem_mem (m : HwMaschine) (c : Nat)
    (d : SseMemDec) (m' : HwMaschine)
    (h : (adapterSseMem).schritt m c d = some m') :
    m'.mem = m.mem ∧ ∀ e : Nat, m'.puffer e = m.puffer e := by
  obtain ⟨t', rfl⟩ := adapterSseMem_form m c d m' h
  exact ⟨setKernVonFp_speicher _ _ _,
    fun e => setKernVonFp_puffer _ _ _ e⟩

/-- A bad decode length admits no adapter step. -/
theorem adapterSseMem_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (h : laengeOk d.laenge = false) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp only [h]

/-- Refused OS vector state admits no adapter step. -/
theorem adapterSseMem_verweigert_bei_profil (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (hok : laengeOk d.laenge = true)
    (h : vecEintritt (m.bereit c) = false) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp only [hok, h]

/-- MMX forms admit no adapter step: no MMX file on the machine. -/
theorem adapterSseMem_verweigert_mmx (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (h : sseMemDstX d.op = none) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp only
  cases hlen : laengeOk d.laenge with
  | false => rfl
  | true =>
    simp only
    cases hfp : vecEintritt (m.bereit c) with
    | false => rfl
    | true =>
      simp only
      cases hop : d.op with
      | pshufbRM w dst f => simp [hop, sseMemDstX] at h
      | pabsBRM w dst f => simp [hop, sseMemDstX] at h
      | pabsWRM w dst f => simp [hop, sseMemDstX] at h
      | pabsDRM w dst f => simp [hop, sseMemDstX] at h
      | palignrRM w dst f imm => simp [hop, sseMemDstX] at h
      | pshufbRW dst src => simp [hop, sseMemDstX] at h
      | pabsBRW dst src => simp [hop, sseMemDstX] at h
      | pabsWRW dst src => simp [hop, sseMemDstX] at h
      | pabsDRW dst src => simp [hop, sseMemDstX] at h
      | palignrRW dst src imm => simp [hop, sseMemDstX] at h
      | pshufbMM dst src =>
        simp only [hop]
      | pabsBMM dst src =>
        simp only [hop]
      | pabsWMM dst src =>
        simp only [hop]
      | pabsDMM dst src =>
        simp only [hop]
      | palignrMM dst src imm =>
        simp only [hop]
      | pshufbMN dst f =>
        simp only [hop]
      | pabsBMN dst f =>
        simp only [hop]
      | pabsWMN dst f =>
        simp only [hop]
      | pabsDMN dst f =>
        simp only [hop]
      | palignrMN dst f imm =>
        simp only [hop]

/-! ## 5b. Successor shape with the written value.

  Every successful step embeds `sseMemNach` with the decoded
  length: RIP advances past it, flags and GPRs are kept, exactly
  one XMM register is written. The shape theorem below carries the
  written value, so the frame theorems never re-case the decoder. -/

/-- The successor advances RIP past the decoded length. -/
theorem sseMemNach_rip (t : FpZustand) (l : Nat) (x : XmmDatei) :
    (sseMemNach t l x).kern.rip = ripNach t.kern.rip l := rfl

/-- The successor keeps the flags. -/
theorem sseMemNach_flags (t : FpZustand) (l : Nat) (x : XmmDatei) :
    (sseMemNach t l x).kern.flags = t.kern.flags := rfl

/-- The successor installs the given XMM file. -/
theorem sseMemNach_xmm (t : FpZustand) (l : Nat) (x : XmmDatei) :
    (sseMemNach t l x).xmm = x := rfl

/-- The successor keeps every GPR. -/
theorem sseMemNach_gpr (t : FpZustand) (l : Nat) (x : XmmDatei)
    (q : Register) :
    (sseMemNach t l x).kern.register q = t.kern.register q := rfl

/-- Every successful adapter step embeds `sseMemNach` with the
    decoded length and some written XMM value. -/
theorem adapterSseMem_formNach (m : HwMaschine) (c : Nat)
    (d : SseMemDec) (m' : HwMaschine)
    (h : (adapterSseMem).schritt m c d = some m') :
    ∃ x : XmmDatei,
      m' = setKernVonFp m c (sseMemNach (projFp m c) d.laenge x) := by
  unfold adapterSseMem at h
  simp only at h
  cases hlen : laengeOk d.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hfp : vecEintritt (m.bereit c) with
    | false => simp [hfp] at h
    | true =>
      simp only [hfp] at h
      cases hop : d.op with
      | pshufbRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pshufbRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pabsBRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pabsBRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pabsWRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pabsWRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pabsDRM w dst f =>
        simp [hop] at h
        cases hg : sseMemGp (.pabsDRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | palignrRM w dst f imm =>
        simp [hop] at h
        cases hg : sseMemGp (.palignrRM w dst f imm)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at h
        | false =>
          simp only [hg] at h
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at h
          | some v =>
            simp only [hld] at h
            cases h
            exact ⟨_, rfl⟩
      | pshufbRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pabsBRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pabsWRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pabsDRW dst src =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | palignrRW dst src imm =>
        simp [hop] at h
        cases h
        exact ⟨_, rfl⟩
      | pshufbMM dst src => simp [hop] at h
      | pabsBMM dst src => simp [hop] at h
      | pabsWMM dst src => simp [hop] at h
      | pabsDMM dst src => simp [hop] at h
      | palignrMM dst src imm => simp [hop] at h
      | pshufbMN dst f => simp [hop] at h
      | pabsBMN dst f => simp [hop] at h
      | pabsWMN dst f => simp [hop] at h
      | pabsDMN dst f => simp [hop] at h
      | palignrMN dst f imm => simp [hop] at h

/-! ## 5c. Step frames: RIP, flags, GPRs, other XMM registers.

  Every successful step advances RIP past the decoded length,
  preserves flags and GPRs, and keeps every non-destination XMM
  register whole -- via the `formNach` shape, without re-casing
  the decoder (only `fremd` names destinations). -/

/-- Every step advances RIP past the decoded length. -/
theorem stepSseMem_rip (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (m' : HwMaschine)
    (hstep : (adapterSseMem).schritt m c d = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip d.laenge := by
  obtain ⟨x, rfl⟩ := adapterSseMem_formNach m c d m' hstep
  simp [setKernVonFp, setKernDaten, sseMemNach, sseMemNachKern,
    projFp, projZustand, sseMemNach_rip]

/-- Every step preserves the flags. -/
theorem stepSseMem_flags (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (m' : HwMaschine)
    (hstep : (adapterSseMem).schritt m c d = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  obtain ⟨x, rfl⟩ := adapterSseMem_formNach m c d m' hstep
  simp [setKernVonFp, setKernDaten, sseMemNach, sseMemNachKern,
    projFp, projZustand, sseMemNach_flags]

/-- Every step keeps every GPR. -/
theorem stepSseMem_gpr (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (m' : HwMaschine) (q : Register)
    (hstep : (adapterSseMem).schritt m c d = some m') :
    (m'.kerne c).register q = (m.kerne c).register q := by
  obtain ⟨x, rfl⟩ := adapterSseMem_formNach m c d m' hstep
  simp [setKernVonFp, setKernDaten, sseMemNach, sseMemNachKern,
    projFp, projZustand, sseMemNach_gpr]

/-- Every step keeps every non-destination XMM register whole. -/
theorem stepSseMem_fremd (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (m' : HwMaschine) (q : XmmReg)
    (hstep : (adapterSseMem).schritt m c d = some m')
    (hq : ∀ r : XmmReg, sseMemDstX d.op = some r → q ≠ r) :
    (m'.kerne c).xmm q = (m.kerne c).xmm q := by
  unfold adapterSseMem at hstep
  simp only at hstep
  cases hlen : laengeOk d.laenge with
  | false => simp [hlen] at hstep
  | true =>
    simp only [hlen] at hstep
    cases hfp : vecEintritt (m.bereit c) with
    | false => simp [hfp] at hstep
    | true =>
      simp only [hfp] at hstep
      cases hop : d.op with
      | pshufbRM w dst f =>
        simp [hop] at hstep
        cases hg : sseMemGp (.pshufbRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at hstep
        | false =>
          simp only [hg] at hstep
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at hstep
          | some v =>
            simp only [hld] at hstep
            cases hstep
            have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
            simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
              projZustand]
            exact xmmSet_fremd _ _ _ _ hqd
      | pabsBRM w dst f =>
        simp [hop] at hstep
        cases hg : sseMemGp (.pabsBRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at hstep
        | false =>
          simp only [hg] at hstep
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at hstep
          | some v =>
            simp only [hld] at hstep
            cases hstep
            have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
            simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
              projZustand]
            exact xmmSet_fremd _ _ _ _ hqd
      | pabsWRM w dst f =>
        simp [hop] at hstep
        cases hg : sseMemGp (.pabsWRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at hstep
        | false =>
          simp only [hg] at hstep
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at hstep
          | some v =>
            simp only [hld] at hstep
            cases hstep
            have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
            simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
              projZustand]
            exact xmmSet_fremd _ _ _ _ hqd
      | pabsDRM w dst f =>
        simp [hop] at hstep
        cases hg : sseMemGp (.pabsDRM w dst f)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at hstep
        | false =>
          simp only [hg] at hstep
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at hstep
          | some v =>
            simp only [hld] at hstep
            cases hstep
            have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
            simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
              projZustand]
            exact xmmSet_fremd _ _ _ _ hqd
      | palignrRM w dst f imm =>
        simp [hop] at hstep
        cases hg : sseMemGp (.palignrRM w dst f imm)
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
        | true => simp [hg] at hstep
        | false =>
          simp only [hg] at hstep
          cases hld : sseMemLade (tsoAnsicht m) c
            (adrEff (projFp m c).kern
              (ripNach (projFp m c).kern.rip d.laenge) f) with
          | none => simp [hld] at hstep
          | some v =>
            simp only [hld] at hstep
            cases hstep
            have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
            simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
              projZustand]
            exact xmmSet_fremd _ _ _ _ hqd
      | pshufbRW dst src =>
        simp [hop] at hstep
        cases hstep
        have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
        simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
          projZustand]
        exact xmmSet_fremd _ _ _ _ hqd
      | pabsBRW dst src =>
        simp [hop] at hstep
        cases hstep
        have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
        simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
          projZustand]
        exact xmmSet_fremd _ _ _ _ hqd
      | pabsWRW dst src =>
        simp [hop] at hstep
        cases hstep
        have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
        simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
          projZustand]
        exact xmmSet_fremd _ _ _ _ hqd
      | pabsDRW dst src =>
        simp [hop] at hstep
        cases hstep
        have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
        simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
          projZustand]
        exact xmmSet_fremd _ _ _ _ hqd
      | palignrRW dst src imm =>
        simp [hop] at hstep
        cases hstep
        have hqd : q ≠ dst := hq dst (by simp [sseMemDstX, hop])
        simp [setKernVonFp, setKernDaten, sseMemNach, projFp,
          projZustand]
        exact xmmSet_fremd _ _ _ _ hqd
      | pshufbMM dst src =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | pabsBMM dst src =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | pabsWMM dst src =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | pabsDMM dst src =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | palignrMM dst src imm =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | pshufbMN dst f =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | pabsBMN dst f =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | pabsWMN dst f =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | pabsDMN dst f =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep
      | palignrMN dst f imm =>
        simp [adapterSseMem, hlen, hfp, hop] at hstep

/-! ## 5d. Agreement: the adapter runs the accepted lane values.

  Each equation states the successor XMM value exactly as the
  accepted `vecPshufb`/`vecPabs`/`vecPalignr` applied to the
  pre-state destination and the forwarded source (memory) or the
  pre-state source register (REX.W); the #GP gate and the load
  gate stand beside the run as planted refusals. -/

/-- `pshufb` with a memory source shuffles by the loaded mask. -/
theorem okSseMem_pshufbRM (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm) (v : Vektor)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pshufbRM w dst f)
    (hgp : sseMemGp (.pshufbRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = some v) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst
          (vecPshufb ((projFp m c).xmm dst) v)))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- `pabsb` with a memory source takes the loaded absolute value. -/
theorem okSseMem_pabsBRM (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm) (v : Vektor)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsBRM w dst f)
    (hgp : sseMemGp (.pabsBRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = some v) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst (vecPabs .b8 v)))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- `pabsw` with a memory source takes the loaded absolute value. -/
theorem okSseMem_pabsWRM (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm) (v : Vektor)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsWRM w dst f)
    (hgp : sseMemGp (.pabsWRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = some v) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst (vecPabs .b16 v)))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- `pabsd` with a memory source takes the loaded absolute value. -/
theorem okSseMem_pabsDRM (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm) (v : Vektor)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsDRM w dst f)
    (hgp : sseMemGp (.pabsDRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = some v) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst (vecPabs .b32 v)))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- `palignr` with a memory source aligns the loaded composite. -/
theorem okSseMem_palignrRM (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm) (imm : Byte)
    (v : Vektor)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .palignrRM w dst f imm)
    (hgp : sseMemGp (.palignrRM w dst f imm)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = some v) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst
          (vecPalignr ((projFp m c).xmm dst) v imm)))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- REX.W `pshufb` shuffles by the source register. -/
theorem okSseMem_pshufbRW (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pshufbRW dst src) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst
          (vecPshufb ((projFp m c).xmm dst)
            ((projFp m c).xmm src))))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop]

/-- REX.W `pabsb` takes the source absolute value. -/
theorem okSseMem_pabsBRW (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsBRW dst src) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst
          (vecPabs .b8 ((projFp m c).xmm src))))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop]

/-- REX.W `pabsw` takes the source absolute value. -/
theorem okSseMem_pabsWRW (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsWRW dst src) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst
          (vecPabs .b16 ((projFp m c).xmm src))))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop]

/-- REX.W `pabsd` takes the source absolute value. -/
theorem okSseMem_pabsDRW (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsDRW dst src) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst
          (vecPabs .b32 ((projFp m c).xmm src))))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop]

/-- REX.W `palignr` aligns the register composite. -/
theorem okSseMem_palignrRW (m : HwMaschine) (c : Nat) (d : SseMemDec)
    (dst src : XmmReg) (imm : Byte)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .palignrRW dst src imm) :
    (adapterSseMem).schritt m c d =
      some (setKernVonFp m c (sseMemNach (projFp m c) d.laenge
        (xmmSet (projFp m c).xmm dst
          (vecPalignr ((projFp m c).xmm dst)
            ((projFp m c).xmm src) imm)))) := by
  unfold adapterSseMem
  simp [hok, hfp, hop]

/-- A misaligned `pshufb` source admits no step (#GP). -/
theorem adapterSseMem_verweigert_bei_gp_pshufbRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pshufbRM w dst f)
    (hgp : sseMemGp (.pshufbRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = true) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp]

/-- A misaligned `pabsb` source admits no step (#GP). -/
theorem adapterSseMem_verweigert_bei_gp_pabsBRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsBRM w dst f)
    (hgp : sseMemGp (.pabsBRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = true) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp]

/-- A misaligned `pabsw` source admits no step (#GP). -/
theorem adapterSseMem_verweigert_bei_gp_pabsWRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsWRM w dst f)
    (hgp : sseMemGp (.pabsWRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = true) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp]

/-- A misaligned `pabsd` source admits no step (#GP). -/
theorem adapterSseMem_verweigert_bei_gp_pabsDRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsDRM w dst f)
    (hgp : sseMemGp (.pabsDRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = true) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp]

/-- A misaligned `palignr` source admits no step (#GP). -/
theorem adapterSseMem_verweigert_bei_gp_palignrRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm) (imm : Byte)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .palignrRM w dst f imm)
    (hgp : sseMemGp (.palignrRM w dst f imm)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = true) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp]

/-- A refused source load admits no `pshufb` step. -/
theorem adapterSseMem_verweigert_bei_lade_pshufbRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pshufbRM w dst f)
    (hgp : sseMemGp (.pshufbRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = none) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- A refused source load admits no `pabsb` step. -/
theorem adapterSseMem_verweigert_bei_lade_pabsBRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsBRM w dst f)
    (hgp : sseMemGp (.pabsBRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = none) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- A refused source load admits no `pabsw` step. -/
theorem adapterSseMem_verweigert_bei_lade_pabsWRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsWRM w dst f)
    (hgp : sseMemGp (.pabsWRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = none) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- A refused source load admits no `pabsd` step. -/
theorem adapterSseMem_verweigert_bei_lade_pabsDRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .pabsDRM w dst f)
    (hgp : sseMemGp (.pabsDRM w dst f)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = none) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

/-- A refused source load admits no `palignr` step. -/
theorem adapterSseMem_verweigert_bei_lade_palignrRM (m : HwMaschine)
    (c : Nat) (d : SseMemDec)
    (w : Bool) (dst : XmmReg) (f : AdrForm) (imm : Byte)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt (m.bereit c) = true)
    (hop : d.op = .palignrRM w dst f imm)
    (hgp : sseMemGp (.palignrRM w dst f imm)
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = false)
    (hld : sseMemLade (tsoAnsicht m) c
      (adrEff (projFp m c).kern
        (ripNach (projFp m c).kern.rip d.laenge) f) = none) :
    (adapterSseMem).schritt m c d = none := by
  unfold adapterSseMem
  simp [hok, hfp, hop, hgp, hld]

end Gabbro.Grammatik.X86
