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

end Gabbro.Grammatik.X86
