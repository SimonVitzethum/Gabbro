/-
  File:      Grammatik/X86/IntBitScan.lean
  Subject:   Bit scan and count connected to the coherent machine and the
             unified byte dispatcher: BSF/BSR, POPCNT, BSWAP.

  Lane 1279: lifts the accepted value helpers (`bsfIdx`/`bsrIdx` from
  `BitScan`, `popCount`/`popWort`/`popNull` from `BitCount`,
  `bswap32`/`bswap64` from `ByteSwap`) unchanged into a canonical
  byte codec (0F BC/BD, F3 0F B8, 0F C8+r) and into a `HwAdapter` over
  `HwMaschine` (`HardwareExecution`), following `HwMulDivWidth` as the
  structural model. TZCNT/LZCNT are BMI/ABM and DEFERRED: their
  encodings are refused with a named reason. No silicon proof beyond
  self-consistency (see CUTS).
-/
import Grammatik.X86.BitScan
import Grammatik.X86.BitCount
import Grammatik.X86.ByteSwap
import Grammatik.X86.NarrowOps
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Scan/count widths with a canonical row in this file: 16/32/64.
    No 8-bit BSF/BSR/POPCNT form exists in the architecture. -/
inductive BsBreite where
  | b16 | b32 | b64
  deriving DecidableEq, Repr

/-- The canonical pilot width behind a scan/count width. -/
def BsBreite.breite : BsBreite → Breite
  | .b16 => .b16 | .b32 => .b32 | .b64 => .b64

/-- Every scan/count width fits the 1..15 instruction bound domain. -/
theorem bsBreite_bits_pos (b : BsBreite) : 0 < b.breite.bits := by
  cases b <;> decide

/-! ## 1. Instruction vocabulary and canonical encoding.

  BSF/BSR/POPCNT address `ModRM:reg` (destination) over `ModRM:r/m`
  (source, register or memory); BSWAP carries its register in the
  opcode (`0F C8+rd`). Memory sources carry the raw ModRM byte plus
  the raw displacement bytes: address computation is OPEN, so the
  register step refuses them with a named reason (never the register
  plug). SIB (`rm = 100`) is refused at decode. -/

/-- BSWAP widths: 32/64 only. No 16-bit (or 8-bit) BSWAP exists. -/
inductive BswapBreite where
  | b32 | b64
  deriving DecidableEq, Repr

/-- The canonical pilot width behind a BSWAP width. -/
def BswapBreite.breite : BswapBreite → Breite
  | .b32 => .b32 | .b64 => .b64

/-- A scan/count source: a register, or a memory operand described by
    its raw ModRM byte and raw displacement bytes. -/
inductive BsQuelle where
  | reg : Register → BsQuelle
  | mem : (modrm : Nat) → (disp : List Byte) → BsQuelle
  deriving DecidableEq, Repr

/-- The family: BSF/BSR/POPCNT over a width, destination and source;
    BSWAP over a width and a register. -/
inductive BsBefehl where
  | bsf : BsBreite → Register → BsQuelle → BsBefehl
  | bsr : BsBreite → Register → BsQuelle → BsBefehl
  | popcnt : BsBreite → Register → BsQuelle → BsBefehl
  | bswap : BswapBreite → Register → BsBefehl
  deriving DecidableEq, Repr

/-- Decoded family instruction: the form plus its checked byte length. -/
structure BsDecodiert where
  befehl : BsBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- Canonical REX byte: W=W, R=R, X=0 (no SIB), B=B. Emitted exactly
    when W, R or B is set. -/
def bsRexByte (w r b : Nat) : Byte := natByte (64 + 8 * w + 4 * r + b)

/-- Canonical REX prefix, if any: 64-bit forms always carry W; shorter
    forms carry REX only for the high registers. -/
def bsRex (w r b : Nat) : List Byte :=
  if w == 1 || r == 1 || b == 1 then [bsRexByte w r b] else []

/-- Canonical legacy prefix: 16-bit forms carry 66H; POPCNT carries F3;
    BSWAP carries none. -/
def bsLeg (b : BsBreite) (istPopcnt : Bool) : List Byte :=
  match b with
  | .b16 => [natByte 102]
  | _ => if istPopcnt then [natByte 243] else []

/-- Canonical REX prefix for a scan/count register form. -/
def bsRexReg (b : BsBreite) (dst src : Register) : List Byte :=
  let w := match b with | .b64 => 1 | _ => 0
  bsRex w (regHigh dst) (regHigh src)

/-- Canonical encoding of one register-source family instruction. -/
def encodeBsReg (op : Nat) (b : BsBreite) (istPopcnt : Bool)
    (dst src : Register) : List Byte :=
  bsLeg b istPopcnt ++ bsRexReg b dst src ++
    [natByte 15, natByte op, modrmReg (regLow dst) (regLow src)]

/-- Canonical encoding of one memory-source family instruction: the
    stored ModRM byte plus the stored displacement bytes. -/
def encodeBsMem (op : Nat) (b : BsBreite) (istPopcnt : Bool)
    (dst : Register) (modrm : Nat) (disp : List Byte) : List Byte :=
  bsLeg b istPopcnt ++
    bsRex (match b with | .b64 => 1 | _ => 0) (regHigh dst) 0 ++
    [natByte 15, natByte op, natByte modrm] ++ disp

/-- Canonical encoding of one BSWAP instruction. -/
def encodeBswap (b : BswapBreite) (rd : Register) : List Byte :=
  let w := match b with | .b64 => 1 | .b32 => 0
  bsRex w 0 (regHigh rd) ++
    [natByte 15, natByte (200 + regLow rd)]

/-- Canonical byte encoding of one family instruction. -/
def encodeBs : BsBefehl → List Byte
  | .bsf b dst (.reg src) => encodeBsReg 188 b false dst src
  | .bsf b dst (.mem modrm disp) => encodeBsMem 188 b false dst modrm disp
  | .bsr b dst (.reg src) => encodeBsReg 189 b false dst src
  | .bsr b dst (.mem modrm disp) => encodeBsMem 189 b false dst modrm disp
  | .popcnt b dst (.reg src) => encodeBsReg 184 b true dst src
  | .popcnt b dst (.mem modrm disp) => encodeBsMem 184 b true dst modrm disp
  | .bswap b rd => encodeBswap b rd

/-! ## 2. Canonical decoder.

  Bytes are parsed, never encode-compared. Admitted rows: optional
  66H (16-bit) or F3 (POPCNT), optional REX (W promotes to 64 and wins
  over 66H; R extends the destination, B the register source), 0F,
  BC/BD (scan, F3 refused: TZCNT/LZCNT), B8 (POPCNT, F3 required),
  C8+rd (BSWAP, no legacy prefix). Register ModRM (mod=3) decodes to a
  register source; other modes (except SIB, refused) decode to a raw
  memory source whose address computation stays OPEN. LOCK (F0) has no
  rule, so it refuses (SDM: #UD). -/

/-- Legacy prefix parse: 66H, F3, or none. F2 and empty input refuse. -/
def bsParseLeg : List Byte → Option (Bool × Bool × List Byte)
  | b :: rest =>
    if byteNat b == 102 then some (true, false, rest)
    else if byteNat b == 243 then some (false, true, rest)
    else if byteNat b == 242 then none
    else some (false, false, b :: rest)
  | [] => none

/-- REX parse: 40H..4FH yields (W, R, B); anything else means no REX.
    X is ignored (no SIB row is admitted). -/
def bsParseRex : List Byte → (Nat × Nat × Nat × List Byte)
  | b :: rest =>
    let n := byteNat b
    if 64 ≤ n ∧ n < 80 then (n / 8 % 2, n / 4 % 2, n % 2, rest)
    else (0, 0, 0, b :: rest)
  | [] => (0, 0, 0, [])

/-- Take `k` displacement bytes. -/
def nimmBytes : Nat → List Byte → Option (List Byte × List Byte)
  | 0, bs => some ([], bs)
  | k + 1, b :: rest =>
    match nimmBytes k rest with
    | some (ds, rest') => some (b :: ds, rest')
    | none => none
  | _ + 1, [] => none

/-- ModRM parse for scan/count: register-direct yields a register
    source; other modes (except SIB) yield a raw memory source with
    the exact displacement bytes the mode demands. Returns the reg
    field (destination) alongside. -/
def bsParseModrm (bBit : Nat) : List Byte →
    Option (Nat × BsQuelle × List Byte)
  | m :: rest =>
    let n := byteNat m
    if n / 64 == 3 then
      match codeReg (bBit * 8 + n % 8) with
      | some src => some (n / 8 % 8, .reg src, rest)
      | none => none
    else
      let rm := n % 8
      if rm == 4 then none
      else
        let need :=
          if n / 64 == 0 then (if rm == 5 then 4 else 0)
          else if n / 64 == 1 then 1 else 4
        match nimmBytes need rest with
        | some (disp, rest') => some (n / 8 % 8, .mem n disp, rest')
        | none => none
  | [] => none

/-- Scan/count width from prefix state: REX.W wins over 66H. -/
def bsBreiteVon (w : Nat) (p66 : Bool) : BsBreite :=
  if w == 1 then .b64 else if p66 then .b16 else .b32

/-- Build a scan/count instruction from its parts: the destination
    comes from the ModRM reg field under REX.R. -/
def bsBaueMit (mk : BsBreite → Register → BsQuelle → BsBefehl)
    (b : BsBreite) (r feld : Nat) (q : BsQuelle) : Option BsBefehl :=
  match codeReg (r * 8 + feld) with
  | some dst => some (mk b dst q)
  | none => none

/-- Opcode dispatch after 0F: BC/BD scan (F3 refused: deferred
    TZCNT/LZCNT), B8 POPCNT (F3 required), C8+rd BSWAP (no legacy). -/
def bsParseOp (p66 pF3 : Bool) (w r b : Nat) : List Byte →
    Option (BsBefehl × List Byte)
  | op :: rest =>
    let n := byteNat op
    if n == 188 || n == 189 then
      if pF3 then none
      else
        match bsParseModrm b rest with
        | some (feld, q, rest') =>
          match bsBaueMit (fun bw dst qq =>
              if n == 189 then BsBefehl.bsr bw dst qq
              else BsBefehl.bsf bw dst qq)
              (bsBreiteVon w p66) r feld q with
          | some befehl => some (befehl, rest')
          | none => none
        | none => none
    else if n == 184 then
      if !pF3 then none
      else
        match bsParseModrm b rest with
        | some (feld, q, rest') =>
          match bsBaueMit BsBefehl.popcnt (bsBreiteVon w p66) r feld q with
          | some befehl => some (befehl, rest')
          | none => none
        | none => none
    else if 200 ≤ n ∧ n < 208 then
      if pF3 || p66 then none
      else
        match codeReg (b * 8 + (n - 200)) with
        | some rd =>
          some (.bswap (if w == 1 then .b64 else .b32) rd, rest)
        | none => none
    else none
  | [] => none

/-- Decode one family instruction: legacy prefix, REX, 0F, opcode,
    ModRM. The checked length is the consumed byte count. -/
def decodeBs (bs : List Byte) : Option (BsDecodiert × List Byte) :=
  match bsParseLeg bs with
  | none => none
  | some (p66, pF3, rest1) =>
    let (w, r, b, rest2) := bsParseRex rest1
    match rest2 with
    | f :: rest3 =>
      if byteNat f == 15 then
        match bsParseOp p66 pF3 w r b rest3 with
        | some (befehl, rest') =>
          some (⟨befehl, bs.length - rest'.length⟩, rest')
        | none => none
      else none
    | [] => none

end Gabbro.Grammatik.X86
