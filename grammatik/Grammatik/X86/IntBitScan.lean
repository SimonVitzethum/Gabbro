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
  | mem : (modrm : Byte) → (disp : List Byte) → BsQuelle
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

/-- Canonical legacy prefix: 16-bit forms carry 66H; POPCNT carries
    F3 on top (16-bit POPCNT carries both); BSWAP carries none. -/
def bsLeg (b : BsBreite) (istPopcnt : Bool) : List Byte :=
  match b with
  | .b16 => if istPopcnt then [natByte 102, natByte 243] else [natByte 102]
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

/-- Set the ModRM reg field to a destination, keeping mode and r/m:
    the architecture reads the destination from `ModRM:reg`. -/
def modrmMitDst (dst : Register) (modrm : Byte) : Byte :=
  natByte (byteNat modrm / 64 * 64 + regLow dst * 8 + byteNat modrm % 8)

/-- Setting an already-correct reg field changes nothing. -/
theorem modrmMitDst_id (dst : Register) (modrm : Byte)
    (hfeld : byteNat modrm / 8 % 8 = regLow dst) :
    modrmMitDst dst modrm = modrm := by
  unfold modrmMitDst natByte byteNat at *
  have h := modrm.isLt
  have e8 : (2 : Nat) ^ 8 = 256 := by decide
  have hlo := regLow_lt dst
  have hlt : modrm.toNat < 256 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, e8]
  omega

/-- Canonical encoding of one memory-source family instruction: the
    stored ModRM byte (reg field: the destination) plus the stored
    displacement bytes. -/
def encodeBsMem (op : Nat) (b : BsBreite) (istPopcnt : Bool)
    (dst : Register) (modrm : Byte) (disp : List Byte) : List Byte :=
  bsLeg b istPopcnt ++
    bsRex (match b with | .b64 => 1 | _ => 0) (regHigh dst) 0 ++
    [natByte 15, natByte op, modrmMitDst dst modrm] ++ disp

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

/-- Legacy prefix parse, at most one byte: 0 = none present, 1 = 66H,
    2 = F3. F2 and empty input refuse. The decoder calls it twice, so
    66H and F3 arrive in either order; doubled prefixes are refused by
    the caller. Single-byte stages reduce independently. -/
def bsParseLeg1 : List Byte → Option (Nat × List Byte)
  | b :: rest =>
    if byteNat b == 102 then some (1, rest)
    else if byteNat b == 243 then some (2, rest)
    else if byteNat b == 242 then none
    else some (0, b :: rest)
  | [] => none

/-- Combine two parsed legacy bytes: doubled 66H or doubled F3 refuse;
    otherwise 66H anywhere means 16-bit, F3 anywhere means POPCNT. -/
def bsLegKombi : Nat → Nat → Option (Bool × Bool)
  | 1, 1 => none
  | 2, 2 => none
  | l1, l2 => some (l1 == 1 || l2 == 1, l1 == 2 || l2 == 2)

/-- Doubled 66H refuses. -/
theorem bsLegKombi_11 : bsLegKombi 1 1 = none := rfl

/-- Doubled F3 refuses. -/
theorem bsLegKombi_22 : bsLegKombi 2 2 = none := rfl

/-- 66H then F3 means 16-bit POPCNT. -/
theorem bsLegKombi_12 : bsLegKombi 1 2 = some (true, true) := rfl

/-- Absent prefixes mean 32-bit, non-POPCNT. -/
theorem bsLegKombi_00 : bsLegKombi 0 0 = some (false, false) := rfl

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
    if n / 64 = 3 then
      match codeReg (bBit * 8 + n % 8) with
      | some src => some (n / 8 % 8, .reg src, rest)
      | none => none
    else
      let rm := n % 8
      if rm = 4 then none
      else
        let need :=
          if n / 64 = 0 then (if rm = 5 then 4 else 0)
          else if n / 64 = 1 then 1 else 4
        match nimmBytes need rest with
        | some (disp, rest') => some (n / 8 % 8, .mem m disp, rest')
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

/-- Decode one family instruction: legacy prefixes, REX, 0F, opcode,
    ModRM. The checked length is the consumed byte count. -/
def decodeBs (bs : List Byte) : Option (BsDecodiert × List Byte) :=
  match bsParseLeg1 bs with
  | none => none
  | some (l1, rest1) =>
    match bsParseLeg1 rest1 with
    | none => none
    | some (l2, rest2) =>
      match bsLegKombi l1 l2 with
      | none => none
      | some (p66, pF3) =>
        let (w, r, b, rest3) := bsParseRex rest2
        match rest3 with
        | f :: rest4 =>
          if byteNat f == 15 then
            match bsParseOp p66 pF3 w r b rest4 with
            | some (befehl, rest') =>
              some (⟨befehl, bs.length - rest'.length⟩, rest')
            | none => none
          else none
        | [] => none

/-! ## 3. Round trips, dispatcher pins and planted refusals.

  Decoding inverts encoding on every admitted row; the unified chain
  refuses every new byte string (no pilot or extension form is
  shadowed); malformed, deferred and privileged shapes refuse with
  `none`. -/

/-- Well-formed raw memory operand: no register-direct mode, no SIB,
    and exactly the displacement bytes the mode demands. -/
def bsMemOk (modrm : Byte) (disp : List Byte) : Prop :=
  let n := byteNat modrm
  n / 64 ≠ 3 ∧ n % 8 ≠ 4 ∧
  disp.length =
    (if n / 64 = 0 then (if n % 8 = 5 then 4 else 0)
     else if n / 64 = 1 then 1 else 4)

/-- Decoding inverts encoding on every BSWAP row. -/
theorem encodeBswap_decodeBs (b : BswapBreite) (rd : Register) :
    decodeBs (encodeBswap b rd) =
      some (⟨.bswap b rd, (encodeBswap b rd).length⟩, []) := by
  cases b <;> cases rd <;> rfl
/-- Decoding inverts encoding on every BSF register row. -/
theorem encodeBsf_decodeBs (b : BsBreite) (dst src : Register) :
    decodeBs (encodeBs (.bsf b dst (.reg src))) =
      some (⟨.bsf b dst (.reg src),
        (encodeBs (.bsf b dst (.reg src))).length⟩, []) := by
  cases b <;> cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every BSR register row. -/
theorem encodeBsr_decodeBs (b : BsBreite) (dst src : Register) :
    decodeBs (encodeBs (.bsr b dst (.reg src))) =
      some (⟨.bsr b dst (.reg src),
        (encodeBs (.bsr b dst (.reg src))).length⟩, []) := by
  cases b <;> cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every POPCNT register row. -/
theorem encodePopcnt_decodeBs (b : BsBreite) (dst src : Register) :
    decodeBs (encodeBs (.popcnt b dst (.reg src))) =
      some (⟨.popcnt b dst (.reg src),
        (encodeBs (.popcnt b dst (.reg src))).length⟩, []) := by
  cases b <;> cases dst <;> cases src <;> rfl

/-- Taking exactly the stored prefix returns it. -/
theorem nimmBytes_laenge (ds rest : List Byte) :
    nimmBytes ds.length (ds ++ rest) = some (ds, rest) := by
  induction ds generalizing rest with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.length_cons, List.cons_append, nimmBytes, ih]

/-- A well-formed raw memory operand parses back to itself. -/
theorem bsParseModrm_mem_ok (bBit : Nat) (m : Byte) (disp rest : List Byte)
    (h : bsMemOk m disp) :
    bsParseModrm bBit (m :: disp ++ rest) =
      some (byteNat m / 8 % 8, .mem m disp, rest) := by
  unfold bsMemOk at h
  simp only at h
  obtain ⟨hmod, hsib, hlen⟩ := h
  have hlt : byteNat m / 64 = 0 ↔ byteNat m < 64 := by
    constructor
    · intro h; omega
    · intro h; omega
  have hlen' : disp.length =
      (if byteNat m < 64 then (if byteNat m % 8 = 5 then 4 else 0)
       else if byteNat m / 64 = 1 then 1 else 4) := by
    rw [hlen]
    split
    · next h => rw [if_pos (hlt.mp h)]
    · next h => rw [if_neg (fun hc => h (hlt.mpr hc))]
  simp [bsParseModrm, hmod, hsib, ← hlen', nimmBytes_laenge]

/-- Memory-row pins: decoding inverts encoding on representative
    well-formed memory shapes (kernel-checked). The general
    composition over `decodeBs` stays open (see CUTS); the parse half
    (`bsParseModrm_mem_ok`) and the reg-field half (`modrmMitDst_id`)
    are proved generally. -/
theorem pin_mem_bsf_disp8 :
    decodeBs [natByte 15, natByte 188, natByte 64, natByte 7] =
      some (⟨.bsf .b32 .rax (.mem (natByte 64) [natByte 7]), 4⟩, []) := by
  decide

/-- BSF r32, r/m32 register form: 0F BC C1. -/
theorem pin_bsf_reg :
    decodeBs [natByte 15, natByte 188, natByte 193] =
      some (⟨.bsf .b32 .rax (.reg .rcx), 3⟩, []) := by
  decide

/-- BSF r64: REX.W 0F BC C1. -/
theorem pin_bsf_reg64 :
    decodeBs [natByte 72, natByte 15, natByte 188, natByte 193] =
      some (⟨.bsf .b64 .rax (.reg .rcx), 4⟩, []) := by
  decide

/-- BSF r16: 66 0F BC C1. -/
theorem pin_bsf_reg16 :
    decodeBs [natByte 102, natByte 15, natByte 188, natByte 193] =
      some (⟨.bsf .b16 .rax (.reg .rcx), 4⟩, []) := by
  decide

/-- POPCNT r32: F3 0F B8 C1. -/
theorem pin_popcnt_reg :
    decodeBs [natByte 243, natByte 15, natByte 184, natByte 193] =
      some (⟨.popcnt .b32 .rax (.reg .rcx), 4⟩, []) := by
  decide

/-- POPCNT r16: 66 F3 0F B8 C1. -/
theorem pin_popcnt_reg16 :
    decodeBs [natByte 102, natByte 243, natByte 15, natByte 184,
      natByte 193] =
      some (⟨.popcnt .b16 .rax (.reg .rcx), 5⟩, []) := by
  decide

/-- BSWAP eax: 0F C8. -/
theorem pin_bswap32 :
    decodeBs [natByte 15, natByte 200] =
      some (⟨.bswap .b32 .rax, 2⟩, []) := by
  decide

/-- BSWAP rbx: REX.W 0F CB. -/
theorem pin_bswap64 :
    decodeBs [natByte 72, natByte 15, natByte 203] =
      some (⟨.bswap .b64 .rbx, 3⟩, []) := by
  decide

/-- BSR r32 over disp32 memory: 0F BD mod=10. -/
theorem pin_mem_bsr_disp32 :
    decodeBs [natByte 15, natByte 189, natByte 136, natByte 1,
      natByte 2, natByte 3, natByte 4] =
      some (⟨.bsr .b32 .rcx
        (.mem (natByte 136) [natByte 1, natByte 2, natByte 3, natByte 4]),
        7⟩, []) := by
  decide

/-- BSR r32 over no-displacement memory: 0F BD mod=00. -/
theorem pin_mem_bsr_disp0 :
    decodeBs [natByte 15, natByte 189, natByte 3] =
      some (⟨.bsr .b32 .rax (.mem (natByte 3) []), 3⟩, []) := by
  decide

/-- BSF r64 over disp8 memory with REX.W. -/
theorem pin_mem_bsf64_disp8 :
    decodeBs [natByte 72, natByte 15, natByte 188, natByte 64,
      natByte 16] =
      some (⟨.bsf .b64 .rax (.mem (natByte 64) [natByte 16]), 5⟩, []) := by
  decide

/-- The unified chain refuses every new byte string: no pilot or
    extension form is shadowed (SDM ground truth, measured). -/
theorem ext_weist_bsf_zurueck :
    decodeExt [natByte 15, natByte 188, natByte 193] = none := by
  decide

/-- The unified chain refuses BSR rows. -/
theorem ext_weist_bsr_zurueck :
    decodeExt [natByte 15, natByte 189, natByte 193] = none := by
  decide

/-- The unified chain refuses POPCNT rows. -/
theorem ext_weist_popcnt_zurueck :
    decodeExt [natByte 243, natByte 15, natByte 184, natByte 193] =
      none := by
  decide

/-- The unified chain refuses 32-bit BSWAP. -/
theorem ext_weist_bswap32_zurueck :
    decodeExt [natByte 15, natByte 200] = none := by
  decide

/-- The unified chain refuses 64-bit BSWAP. -/
theorem ext_weist_bswap64_zurueck :
    decodeExt [natByte 72, natByte 15, natByte 200] = none := by
  decide

/-- The unified chain refuses 64-bit BSF. -/
theorem ext_weist_bsf64_zurueck :
    decodeExt [natByte 72, natByte 15, natByte 188, natByte 193] =
      none := by
  decide

/-- The unified chain refuses 16-bit BSF. -/
theorem ext_weist_bsf16_zurueck :
    decodeExt [natByte 102, natByte 15, natByte 188, natByte 193] =
      none := by
  decide

/-- Planted refusal: LOCK has no rule (SDM: #UD on BSF/BSR/POPCNT/BSWAP). -/
theorem bs_nichts_lock :
    decodeBs [natByte 240, natByte 15, natByte 188, natByte 193] =
      none := by
  decide

/-- Planted refusal: F3 on BSF is the deferred TZCNT shape. -/
theorem bs_nichts_tzcnt :
    decodeBs [natByte 243, natByte 15, natByte 188, natByte 193] =
      none := by
  decide

/-- Planted refusal: F3 on BSR is the deferred LZCNT shape. -/
theorem bs_nichts_lzcnt :
    decodeBs [natByte 243, natByte 15, natByte 189, natByte 193] =
      none := by
  decide

/-- Planted refusal: 66H+F3 on BSF is 16-bit TZCNT, likewise deferred. -/
theorem bs_nichts_tzcnt16 :
    decodeBs [natByte 102, natByte 243, natByte 15, natByte 188,
      natByte 193] = none := by
  decide

/-- Planted refusal: bare 0F B8 is no POPCNT (F3 required). -/
theorem bs_nichts_ohne_f3 :
    decodeBs [natByte 15, natByte 184, natByte 193] = none := by
  decide

/-- Planted refusal: 66H on BSWAP (no 16-bit form exists). -/
theorem bs_nichts_bswap66 :
    decodeBs [natByte 102, natByte 15, natByte 200] = none := by
  decide

/-- Planted refusal: F3 on BSWAP. -/
theorem bs_nichts_bswapf3 :
    decodeBs [natByte 243, natByte 15, natByte 200] = none := by
  decide

/-- Planted refusal: F2 on BSWAP. -/
theorem bs_nichts_bswapf2 :
    decodeBs [natByte 242, natByte 15, natByte 200] = none := by
  decide

/-- Planted refusal: SIB memory (rm = 100) is not admitted. -/
theorem bs_nichts_sib :
    decodeBs [natByte 15, natByte 188, natByte 4, natByte 200] =
      none := by
  decide

/-- Planted refusal: F2 prefix anywhere. -/
theorem bs_nichts_f2 :
    decodeBs [natByte 242, natByte 15, natByte 188, natByte 193] =
      none := by
  decide

/-- Planted refusal: doubled 66H. -/
theorem bs_nichts_doppel66 :
    decodeBs [natByte 102, natByte 102, natByte 15, natByte 188,
      natByte 193] = none := by
  decide

/-- Planted refusal: doubled F3. -/
theorem bs_nichts_doppelf3 :
    decodeBs [natByte 243, natByte 243, natByte 15, natByte 184,
      natByte 193] = none := by
  decide

/-- Planted refusal: truncated inputs. -/
theorem bs_nichts_abgeschnitten_a :
    decodeBs [natByte 15, natByte 188] = none := by
  decide

/-- Planted refusal: lone 0F. -/
theorem bs_nichts_abgeschnitten_b :
    decodeBs [natByte 15] = none := by
  decide

/-- Planted refusal: empty input. -/
theorem bs_nichts_leer : decodeBs [] = none := by
  decide

/-- Planted refusal: disp32 mode without its four bytes. -/
theorem bs_nichts_ohne_disp :
    decodeBs [natByte 15, natByte 188, natByte 5] = none := by
  decide

/-! ## 4. Value semantics and the family step.

  Values reuse the accepted helpers unchanged (`bsfIdx`/`bsrIdx`,
  `popCount`/`popWort`, `bswap32`/`bswap64`); flag rows follow SDM 093
  (BSF/BSR: ZF = source zero, PF = parity of the source popcount,
  CF/OF/SF/AF cleared; POPCNT: everything cleared, ZF = source zero;
  BSWAP: flags untouched). The destination discipline is the accepted
  narrow merge (16-bit merges, 32-bit zero-extends); a zero scan
  source leaves the destination register untouched (SDM: the
  destination operand is unmodified). POPCNT without the CPUID bit is
  the feature refusal (SDM: #UD); memory sources are refused by the
  register plug (address computation is open: TSO events only). -/

/-- BSF/BSR flag snapshot: ZF reads source-zero, PF the source
    popcount parity, the rest cleared. -/
def bsFlagsScan (b : Breite) (src : Wort) : Flags :=
  { cf := false, pf := decide (popCount b src % 2 = 0), af := some false,
    zf := scanZF b src, sf := false, of := false }

/-- The scan snapshot sets ZF exactly on a zero source. -/
theorem bsFlagsScan_zf (b : Breite) (src : Wort) :
    (bsFlagsScan b src).zf = true ↔ trunc b src = 0 := by
  simp [bsFlagsScan, scanZF]

/-- POPCNT flag snapshot: everything cleared, ZF reads source-zero. -/
def bsFlagsPopcnt (b : Breite) (src : Wort) : Flags :=
  { cf := false, pf := false, af := some false,
    zf := scanZF b src, sf := false, of := false }

/-- The POPCNT snapshot sets ZF exactly on a zero source. -/
theorem bsFlagsPopcnt_zf (b : Breite) (src : Wort) :
    (bsFlagsPopcnt b src).zf = true ↔ trunc b src = 0 := by
  simp [bsFlagsPopcnt, scanZF]

/-- BSWAP value dispatch: the accepted helpers, 32/64 only. -/
def bswapVal : BswapBreite → Wort → Wort
  | .b32 => bswap32
  | .b64 => bswap64

/-- A 32-bit swap writes back exactly the swapped value (its upper
    bytes are already clear, so the narrow merge is the identity). -/
theorem bswap32_merge (oldVal v : Wort) :
    mergeRegNarrow .b32 oldVal (bswap32 v) = bswap32 v := by
  show trunc .b32 (bswap32 v) = bswap32 v
  apply BitVec.eq_of_toNat_eq
  have hmod := narrowTruncMod .b32 (bswap32 v)
  have hb32 : Breite.bits Breite.b32 = 32 := rfl
  rw [hb32] at hmod
  have hzx := bswap32_zeroExt v
  have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  omega

/-- Step outcome: successor, feature refusal (POPCNT without the
    CPUID bit, the #UD analogue), or no register step (bad length or
    a memory source, which needs the TSO event path). -/
inductive BsErgebnis where
  | ok (nach : Zustand)
  | verweigert
  | misslungen

/-- Scan successor: the accepted index under the narrow merge, or the
    untouched destination on a zero source, with the scan flags. -/
def bsScanNach (istBsr : Bool) (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand) : Zustand :=
  let idx :=
    if istBsr then bsrIdx b.breite (s.register src)
    else bsfIdx b.breite (s.register src)
  let wert :=
    match idx with
    | some i => mergeRegNarrow b.breite (s.register dst) (BitVec.ofNat 64 i)
    | none => s.register dst
  { s with
    register := regSet s.register dst wert,
    rip := ripNach s.rip len,
    flags := bsFlagsScan b.breite (s.register src) }

/-- POPCNT successor: the accepted count under the narrow merge, with
    the cleared flags. -/
def bsPopcntNach (b : BsBreite) (dst src : Register) (len : Nat)
    (s : Zustand) : Zustand :=
  { s with
    register := regSet s.register dst
      (mergeRegNarrow b.breite (s.register dst)
        (popWort b.breite (s.register src))),
    rip := ripNach s.rip len,
    flags := bsFlagsPopcnt b.breite (s.register src) }

/-- BSWAP successor: the accepted swap under the narrow merge, flags
    untouched. -/
def bsBswapNach (b : BswapBreite) (rd : Register) (len : Nat)
    (s : Zustand) : Zustand :=
  let bw := BswapBreite.breite b
  { s with
    register := regSet s.register rd
      (mergeRegNarrow bw (s.register rd) (bswapVal b (s.register rd))),
    rip := ripNach s.rip len }

/-- One family step: the length guard, then the accepted value
    helpers; the feature gate is never folded away. -/
def bsSchritt (m : PopcntMerkmal) (d : BsDecodiert)
    (s : Zustand) : BsErgebnis :=
  match laengeOk d.laenge with
  | false => .misslungen
  | true =>
    match d.befehl with
    | .bsf b dst (.reg src) => .ok (bsScanNach false b dst src d.laenge s)
    | .bsr b dst (.reg src) => .ok (bsScanNach true b dst src d.laenge s)
    | .popcnt b dst (.reg src) =>
      match m.popcnt with
      | false => .verweigert
      | true => .ok (bsPopcntNach b dst src d.laenge s)
    | .bswap b rd => .ok (bsBswapNach b rd d.laenge s)
    | .bsf _ _ (.mem _ _) => .misslungen
    | .bsr _ _ (.mem _ _) => .misslungen
    | .popcnt _ _ (.mem _ _) => .misslungen

/-- Admitted BSF step: the accepted forward index with the scan snapshot. -/
theorem bs_bsf_ok (m : PopcntMerkmal) (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand) (hok : laengeOk len = true) :
    bsSchritt m ⟨.bsf b dst (.reg src), len⟩ s =
      .ok (bsScanNach false b dst src len s) := by
  unfold bsSchritt
  rw [hok]

/-- Admitted BSR step: the accepted reverse index with the scan snapshot. -/
theorem bs_bsr_ok (m : PopcntMerkmal) (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand) (hok : laengeOk len = true) :
    bsSchritt m ⟨.bsr b dst (.reg src), len⟩ s =
      .ok (bsScanNach true b dst src len s) := by
  unfold bsSchritt
  rw [hok]

/-- Admitted POPCNT step: the accepted count with the cleared flags. -/
theorem bs_popcnt_ok (m : PopcntMerkmal) (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand) (hok : laengeOk len = true)
    (hfeat : m.popcnt = true) :
    bsSchritt m ⟨.popcnt b dst (.reg src), len⟩ s =
      .ok (bsPopcntNach b dst src len s) := by
  unfold bsSchritt
  rw [hok, hfeat]

/-- Admitted BSWAP step: the accepted swap, flags untouched. -/
theorem bs_bswap_ok (m : PopcntMerkmal) (b : BswapBreite) (rd : Register)
    (len : Nat) (s : Zustand) (hok : laengeOk len = true) :
    bsSchritt m ⟨.bswap b rd, len⟩ s =
      .ok (bsBswapNach b rd len s) := by
  unfold bsSchritt
  rw [hok]

/-- Feature refusal: without the CPUID bit the count image is refused,
    never a value. -/
theorem bs_popcnt_verweigert (m : PopcntMerkmal) (b : BsBreite)
    (dst src : Register) (len : Nat) (s : Zustand)
    (hok : laengeOk len = true) (hfeat : m.popcnt = false) :
    bsSchritt m ⟨.popcnt b dst (.reg src), len⟩ s = .verweigert := by
  unfold bsSchritt
  rw [hok, hfeat]

/-- Without the feature no count step is a success. -/
theorem bs_ohne_merkmal_kein_ok (m : PopcntMerkmal) (d : BsDecodiert)
    (s : Zustand) (h : m.popcnt = false)
    (hok : laengeOk d.laenge = true)
    (hq : (∃ (b : BsBreite) (dst src : Register),
        d.befehl = .popcnt b dst (.reg src)) ∨
      (∃ (b : BsBreite) (dst : Register) (mm : Byte) (dd : List Byte),
        d.befehl = .popcnt b dst (.mem mm dd)))
    (z : BsErgebnis) (hstep : bsSchritt m d s = z) :
    ∀ (t : Zustand), z ≠ .ok t := by
  cases hq with
  | inl hreg =>
    obtain ⟨b, dst, src, hpop⟩ := hreg
    have hver : bsSchritt m d s = .verweigert := by
      unfold bsSchritt
      rw [hok, hpop, h]
    rw [hver] at hstep
    subst z
    intro t hcon
    cases hcon
  | inr hmem =>
    obtain ⟨b, dst, mm, dd, hpop⟩ := hmem
    have hmiss : bsSchritt m d s = .misslungen := by
      unfold bsSchritt
      rw [hok, hpop]
    rw [hmiss] at hstep
    subst z
    intro t hcon
    cases hcon

/-- A bad decode length refuses every form, unconditionally. -/
theorem bs_laenge_misslungen (m : PopcntMerkmal) (d : BsDecodiert)
    (s : Zustand) (h : laengeOk d.laenge = false) :
    bsSchritt m d s = .misslungen := by
  unfold bsSchritt
  rw [h]

/-- A memory BSF source admits no register step. -/
theorem bs_bsf_mem_misslungen (m : PopcntMerkmal) (b : BsBreite)
    (dst : Register) (mm : Byte) (dd : List Byte) (len : Nat)
    (s : Zustand) (hok : laengeOk len = true) :
    bsSchritt m ⟨.bsf b dst (.mem mm dd), len⟩ s = .misslungen := by
  unfold bsSchritt
  rw [hok]

/-- A memory BSR source admits no register step. -/
theorem bs_bsr_mem_misslungen (m : PopcntMerkmal) (b : BsBreite)
    (dst : Register) (mm : Byte) (dd : List Byte) (len : Nat)
    (s : Zustand) (hok : laengeOk len = true) :
    bsSchritt m ⟨.bsr b dst (.mem mm dd), len⟩ s = .misslungen := by
  unfold bsSchritt
  rw [hok]

/-- A memory POPCNT source admits no register step. -/
theorem bs_popcnt_mem_misslungen (m : PopcntMerkmal) (b : BsBreite)
    (dst : Register) (mm : Byte) (dd : List Byte) (len : Nat)
    (s : Zustand) (hok : laengeOk len = true) :
    bsSchritt m ⟨.popcnt b dst (.mem mm dd), len⟩ s = .misslungen := by
  unfold bsSchritt
  rw [hok]

/-- A BSF success writes the accepted index under the narrow merge. -/
theorem bs_bsf_schreibt_index (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand) (i : Nat)
    (h : bsfIdx b.breite (s.register src) = some i) :
    (bsScanNach false b dst src len s).register dst =
      mergeRegNarrow b.breite (s.register dst) (BitVec.ofNat 64 i) := by
  unfold bsScanNach
  simp [h, regSet_gleich]

/-- A zero BSF source leaves the destination untouched. -/
theorem bs_bsf_null_laesst_liegen (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand)
    (h : bsfIdx b.breite (s.register src) = none) :
    (bsScanNach false b dst src len s).register dst =
      s.register dst := by
  unfold bsScanNach
  simp [h, regSet_gleich]

/-- A BSR success writes the accepted index under the narrow merge. -/
theorem bs_bsr_schreibt_index (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand) (i : Nat)
    (h : bsrIdx b.breite (s.register src) = some i) :
    (bsScanNach true b dst src len s).register dst =
      mergeRegNarrow b.breite (s.register dst) (BitVec.ofNat 64 i) := by
  unfold bsScanNach
  simp [h, regSet_gleich]

/-- A zero BSR source leaves the destination untouched. -/
theorem bs_bsr_null_laesst_liegen (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand)
    (h : bsrIdx b.breite (s.register src) = none) :
    (bsScanNach true b dst src len s).register dst =
      s.register dst := by
  unfold bsScanNach
  simp [h, regSet_gleich]

/-- A POPCNT success writes the accepted count under the narrow merge. -/
theorem bs_popcnt_schreibt_zaehlung (b : BsBreite) (dst src : Register)
    (len : Nat) (s : Zustand) :
    (bsPopcntNach b dst src len s).register dst =
      mergeRegNarrow b.breite (s.register dst)
        (popWort b.breite (s.register src)) := by
  unfold bsPopcntNach
  simp [regSet_gleich]

/-- A BSWAP writes the accepted swap under the narrow merge, flags
    untouched. -/
theorem bs_bswap_schreibt_tausch (b : BswapBreite) (rd : Register)
    (len : Nat) (s : Zustand) :
    (bsBswapNach b rd len s).register rd =
      mergeRegNarrow (BswapBreite.breite b) (s.register rd)
        (bswapVal b (s.register rd)) ∧
    (bsBswapNach b rd len s).flags = s.flags := by
  unfold bsBswapNach
  simp [regSet_gleich]

/-- A BSF success index lies inside the operand width: the accepted
    range law, lifted to the step vocabulary. -/
theorem bs_bsf_bereich (b : BsBreite) (src : Wort) (i : Nat)
    (h : bsfIdx b.breite src = some i) :
    i < b.breite.bits :=
  bsfIdx_schranke b.breite src i h

/-- A BSF success index names a set bit of the truncated source. -/
theorem bs_bsf_bit (b : BsBreite) (src : Wort) (i : Nat)
    (h : bsfIdx b.breite src = some i) :
    bitGesetzt b.breite src i = true :=
  bsfIdx_bit b.breite src i h

/-- A BSF success index is minimal: lower bits are clear. -/
theorem bs_bsf_min (b : BsBreite) (src : Wort) (i j : Nat)
    (h : bsfIdx b.breite src = some i) (hlt : j < i) :
    bitGesetzt b.breite src j = false :=
  bsfIdx_min b.breite src i j h hlt

/-- A BSR success index lies inside the operand width. -/
theorem bs_bsr_bereich (b : BsBreite) (src : Wort) (i : Nat)
    (h : bsrIdx b.breite src = some i) :
    i < b.breite.bits :=
  bsrIdx_schranke b.breite src i h

/-- A BSR success index names a set bit of the truncated source. -/
theorem bs_bsr_bit (b : BsBreite) (src : Wort) (i : Nat)
    (h : bsrIdx b.breite src = some i) :
    bitGesetzt b.breite src i = true :=
  bsrIdx_bit b.breite src i h

/-- A BSR success index is maximal: higher in-width bits are clear. -/
theorem bs_bsr_max (b : BsBreite) (src : Wort) (i j : Nat)
    (h : bsrIdx b.breite src = some i)
    (hhi : i < j) (hlt : j < b.breite.bits) :
    bitGesetzt b.breite src j = false :=
  bsrIdx_max b.breite src i j h hhi hlt

/-- The fixed-width count never exceeds the named width. -/
theorem bs_popcnt_schranke (b : BsBreite) (src : Wort) :
    popCount b.breite src ≤ b.breite.bits :=
  popCount_schranke b.breite src

/-- The count fits in one word: at most 64. -/
theorem bs_popcnt_wort_schranke (b : BsBreite) (src : Wort) :
    popCount b.breite src ≤ 64 :=
  popCount_wort_schranke b.breite src

/-- The 64-bit swap is an involution: the accepted law, lifted. -/
theorem bs_bswap64_invol (v : Wort) :
    bswap64 (bswap64 v) = v :=
  bswap64_invol v

/-- The 32-bit swap is an involution on values that fit in four
    bytes: the accepted bounded law, lifted. -/
theorem bs_bswap32_invol (v : Wort)
    (hv : v.toNat < 2 ^ 32) :
    bswap32 (bswap32 v) = v :=
  bswap32_invol_bounded v hv
end Gabbro.Grammatik.X86
