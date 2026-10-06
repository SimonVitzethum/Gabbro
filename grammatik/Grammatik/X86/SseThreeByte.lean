/-
  File:      Grammatik/X86/SseThreeByte.lean
  Subject:   SSSE3 three-byte forms over the 0F 38 / 0F 3A escapes,
    connected to the coherent machine and the capstone chain.

  Lane 1369: admitted register-direct XMM rows only -- PSHUFB
  (`66 0F 38 00 /r`), PABSB/W/D (`66 0F 38 1C/1D/1E /r`) and PALIGNR
  (`66 0F 3A 0F /r ib`). Canonical REX (`64 + 4*R + B`, W=0/X=0) is
  required, exactly like the accepted `VectorCodec` rows. Semantics
  reuse the accepted lane vocabulary (`laneNat`/`vecMk`, `sVal` for
  the PABS sign); no evaluator is redefined. Memory ModRM forms,
  MMX (NP) forms, REX.W forms and every other third byte stay
  refused (see CUTS). Silicon provenance: Intel SDM 325462-093US
  (Sep 2026), clone-local `.tmp/HARDWARE-REFERENCES/`
  `intel-instruction-reference.txt`.
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Kern.Ganzzahl
import Grammatik.X86.Kern.Gleitprofil
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- Admitted SSSE3 register forms: shuffle, packed absolute value at
    8/16/32 bits, and align-right with an immediate byte count. -/
inductive SseThreeOp where
  | pshufbRR (dst src : XmmReg)
  | pabsBRR (dst src : XmmReg)
  | pabsWRR (dst src : XmmReg)
  | pabsDRR (dst src : XmmReg)
  | palignrRR (dst src : XmmReg) (imm : Byte)
  deriving DecidableEq, Repr

/-- Escape byte after `0F`: `0F 38` for shuffle/abs, `0F 3A`
    for align-right (PALIGNR lives in the `0F 3A` map, SDM Vol. 2B
    4-216: `66 0F 3A 0F /r ib`). -/
def sseThreeEscape : SseThreeOp → Nat
  | .pshufbRR _ _ => 56
  | .pabsBRR _ _ => 56
  | .pabsWRR _ _ => 56
  | .pabsDRR _ _ => 56
  | .palignrRR _ _ _ => 58

/-- Third opcode byte: `00` PSHUFB (SDM 4-422), `1C/1D/1E`
    PABSB/W/D (SDM 4-176), `0F` PALIGNR. -/
def sseThreeThird : SseThreeOp → Nat
  | .pshufbRR _ _ => 0
  | .pabsBRR _ _ => 28
  | .pabsWRR _ _ => 29
  | .pabsDRR _ _ => 30
  | .palignrRR _ _ _ => 15

/-- Canonical REX byte for one form (W=0, X=0, always emitted, exactly
    like the accepted `vectorRex`). -/
def sseThreeRex : SseThreeOp → Byte
  | .pshufbRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pabsBRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pabsWRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pabsDRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .palignrRR dst src _ => natByte (64 + 4 * xmmHigh dst + xmmHigh src)

/-- Canonical byte encoding: REX, `66`, `0F`, escape, third byte,
    register-direct ModRM (mod=3, reg=dst, r/m=src), plus the imm8 of
    PALIGNR. 6 bytes, 7 for PALIGNR. -/
def encodeSseThree : SseThreeOp → List Byte
  | op@(.pshufbRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsBRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsWRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pabsDRR dst src) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.palignrRR dst src imm) =>
    [sseThreeRex op, natByte 102, natByte 15, natByte (sseThreeEscape op),
      natByte (sseThreeThird op), modrmReg (xmmLow dst) (xmmLow src), imm]

/-- Every canonical encoding without an immediate is 6 bytes. -/
theorem encodeSseThree_len6 (dst src : XmmReg) :
    (encodeSseThree (.pshufbRR dst src)).length = 6 := rfl

/-- Every canonical PALIGNR encoding is 7 bytes. -/
theorem encodeSseThree_len7 (dst src : XmmReg) (imm : Byte) :
    (encodeSseThree (.palignrRR dst src imm)).length = 7 := rfl

/-- The old capstone chain refuses the canonical PSHUFB bytes. -/
theorem kap_weist_pshufb_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PABSB bytes. -/
theorem kap_weist_pabsb_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 28, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PABSW bytes. -/
theorem kap_weist_pabsw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 29, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PABSD bytes. -/
theorem kap_weist_pabsd_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 30, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PALIGNR bytes. -/
theorem kap_weist_palignr_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 200, natByte 4] = none := by
  decide

/-! ## 2. Canonical decoder.

  The decoder parses bytes, never encode-equality. Only the canonical
  REX prefix (`64 + 4*R + B`: W=0, X=0), then `66`, `0F`, the escape
  (`38`/`3A`), the third byte, and a register-direct ModRM (mod=3,
  reg=dst, r/m=src) are admitted; PALIGNR takes one trailing imm8.
  Anything else refuses with `none`. -/

/-- A decoded three-byte form: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure SseThreeDec where
  op : SseThreeOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- Decode one register-direct ModRM byte after the admitted prefix,
    escape and third byte. PALIGNR reads its imm8 behind the ModRM. -/
def decodeSseThreeModrm (esc opByte rBit bBit : Nat) :
    List Byte → Option (SseThreeOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src =>
        match esc, opByte with
        | 56, 0 => some ((.pshufbRR dst src), rest)
        | 56, 28 => some ((.pabsBRR dst src), rest)
        | 56, 29 => some ((.pabsWRR dst src), rest)
        | 56, 30 => some ((.pabsDRR dst src), rest)
        | 58, 15 =>
          match rest with
          | [] => none
          | imm :: rest2 => some ((.palignrRR dst src imm), rest2)
        | _, _ => none
      | _, _ => none
    else none

/-- Decode after the canonical REX prefix: `66`, then `0F`, then the
    escape byte (`38`/`3A`), the third byte, then ModRM. -/
def decodeSseThreeNach (rBit bBit : Nat) :
    List Byte → Option (SseThreeOp × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 102 then
      match rest with
      | [] => none
      | p2 :: rest2 =>
        if byteNat p2 == 15 then
          match rest2 with
          | [] => none
          | esc :: rest3 =>
            if byteNat esc == 56 || byteNat esc == 58 then
              match rest3 with
              | [] => none
              | op :: rest4 =>
                decodeSseThreeModrm (byteNat esc) (byteNat op)
                  rBit bBit rest4
            else none
        else none
    else none

/-- Top-level three-byte decode: the REX prefix selects the extension
    bits; anything without a canonical REX refuses. The decoded length
    is the canonical encoding length of the decoded form. -/
def decodeSseThree : List Byte → Option (SseThreeDec × List Byte)
  | [] => none
  | r :: tail =>
    let nach (rBit bBit : Nat) :=
      match decodeSseThreeNach rBit bBit tail with
      | some (op, rest) =>
        some ((⟨op, (encodeSseThree op).length⟩ : SseThreeDec), rest)
      | none => none
    match byteNat r with
    | 64 => nach 0 0
    | 65 => nach 0 1
    | 68 => nach 1 0
    | 69 => nach 1 1
    | _ => none

/-- Round trip for PSHUFB, over any suffix. -/
theorem roundtrip_pshufb (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pshufbRR dst src) ++ suffix) =
      some ((⟨.pshufbRR dst src,
        (encodeSseThree (.pshufbRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PABSB, over any suffix. -/
theorem roundtrip_pabsb (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pabsBRR dst src) ++ suffix) =
      some ((⟨.pabsBRR dst src,
        (encodeSseThree (.pabsBRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PABSW, over any suffix. -/
theorem roundtrip_pabsw (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pabsWRR dst src) ++ suffix) =
      some ((⟨.pabsWRR dst src,
        (encodeSseThree (.pabsWRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PABSD, over any suffix. -/
theorem roundtrip_pabsd (dst src : XmmReg) (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.pabsDRR dst src) ++ suffix) =
      some ((⟨.pabsDRR dst src,
        (encodeSseThree (.pabsDRR dst src)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PALIGNR, over any suffix. -/
theorem roundtrip_palignr (dst src : XmmReg) (imm : Byte)
    (suffix : List Byte) :
    decodeSseThree (encodeSseThree (.palignrRR dst src imm) ++ suffix) =
      some ((⟨.palignrRR dst src imm,
        (encodeSseThree (.palignrRR dst src imm)).length⟩ : SseThreeDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every covered row, over any suffix.
    The decoded length is the canonical encoding length. -/
theorem roundtripSseThree (op : SseThreeOp) (suffix : List Byte) :
    decodeSseThree (encodeSseThree op ++ suffix) =
      some ((⟨op, (encodeSseThree op).length⟩ : SseThreeDec), suffix) := by
  cases op with
  | pshufbRR dst src => exact roundtrip_pshufb dst src suffix
  | pabsBRR dst src => exact roundtrip_pabsb dst src suffix
  | pabsWRR dst src => exact roundtrip_pabsw dst src suffix
  | pabsDRR dst src => exact roundtrip_pabsd dst src suffix
  | palignrRR dst src imm => exact roundtrip_palignr dst src imm suffix

/-- A memory ModRM (mod≠3) is refused: only register forms are covered. -/
theorem sseThree_nichts_speicher :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 8] = none := rfl

/-- A truncated prefix (REX + `66` only) is refused. -/
theorem sseThree_nichts_kurz :
    decodeSseThree [natByte 64, natByte 102] = none := rfl

/-- A wrong escape (`0F 39`) is refused. -/
theorem sseThree_nichts_escape :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 57,
      natByte 0, natByte 200] = none := rfl

/-- MOVBE (`0F 38 F0`) is refused: a different family owns it. -/
theorem sseThree_nichts_movbe :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 240, natByte 200] = none := rfl

/-- An MMX (NP, no `66`) form is refused: only the `66` XMM rows are covered. -/
theorem sseThree_nichts_mmx :
    decodeSseThree [natByte 15, natByte 56, natByte 28,
      natByte 200] = none := rfl

/-- A REX.W form is refused: only the canonical W=0 REX is admitted
    (silicon ignores REX.W here; the canonical subset does not cover it). -/
theorem sseThree_nichts_rexw :
    decodeSseThree [natByte 72, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := rfl

/-- PALIGNR without its imm8 is refused. -/
theorem sseThree_nichts_ohne_imm :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 200] = none := rfl

/-- Another `0F 3A` third byte (BLENDVPS `0F 3A 14`) is refused. -/
theorem sseThree_nichts_blendv :
    decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 20, natByte 200, natByte 0] = none := rfl

/-! ## 3. Semantics from the accepted lane vocabulary.

  No accepted evaluator covers shuffle/abs/align (the accepted
  `Vektor` vocabulary is add/sub/xor/and/or lanes), so the three
  functions below are built from the accepted `laneNat`/`vecMk`
  vocabulary only -- the same construction the accepted `ymmAndn`
  uses where no lane model exists to reuse. Each matches the SDM
  operation pseudocode lane for lane:
  - PSHUFB (Vol. 2B 4-422): zero where the control byte has bit 7,
    else the indexed destination byte (low 4 bits select);
  - PABSB/W/D (Vol. 2B 4-176): ABS per signed element, stored
    UNSIGNED; INT_MIN wraps (`0x80 -> 0x80`: `(256-128)%256=128`);
  - PALIGNR (Vol. 2B 4-216): `((DEST << 128) OR SRC) >> (imm8*8)`,
    low 128 bits; counts above 32 zero the result. -/

/-- Absolute value of one lane value: identity where the lane is
    signed-nonnegative, modular negation elsewhere. -/
def pabsLane (b : Breite) (u : Nat) : Nat :=
  if u < 2 ^ (b.bits - 1) then u else (2 ^ b.bits - u) % 2 ^ b.bits

/-- Packed absolute value at width `b` (PABSB/W/D). -/
def vecPabs (b : Breite) (x : Vektor) : Vektor :=
  vecMk b (fun i => pabsLane b (laneNat b x i))

/-- Packed shuffle bytes (PSHUFB): the control byte selects or zeroes. -/
def vecPshufb (dst src : Vektor) : Vektor :=
  vecMk .b8 (fun i =>
    let c := laneNat .b8 src i
    if c / 128 = 1 then 0 else laneNat .b8 dst (c % 16))

/-- Packed align right (PALIGNR): byte `i` of the shifted
    `DEST:SRC` composite, zero past its 32 bytes. -/
def vecPalignr (dst src : Vektor) (imm : Byte) : Vektor :=
  vecMk .b8 (fun i =>
    let j := i + byteNat imm
    if j < 16 then laneNat .b8 src j
    else if j < 32 then laneNat .b8 dst (j - 16)
    else 0)

/-- Per-lane absolute value is the lane function on the source lane. -/
theorem laneNat_pabs (b : Breite) (x : Vektor) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (vecPabs b x) i =
      pabsLane b (laneNat b x i) % 2 ^ b.bits := by
  unfold vecPabs
  exact laneGet_mk b _ i hi

/-- Per-lane shuffle is the control function on the two sources. -/
theorem laneNat_pshufb (dst src : Vektor) (i : Nat)
    (hi : i < laneCount .b8) :
    laneNat .b8 (vecPshufb dst src) i =
      ((let c := laneNat .b8 src i
        if c / 128 = 1 then 0 else laneNat .b8 dst (c % 16)) %
        2 ^ Breite.b8.bits) := by
  unfold vecPshufb
  exact laneGet_mk .b8 _ i hi

/-- Per-lane align is the composite byte at the shifted position. -/
theorem laneNat_palignr (dst src : Vektor) (imm : Byte) (i : Nat)
    (hi : i < laneCount .b8) :
    laneNat .b8 (vecPalignr dst src imm) i =
      ((let j := i + byteNat imm
        if j < 16 then laneNat .b8 src j
        else if j < 32 then laneNat .b8 dst (j - 16)
        else 0) % 2 ^ Breite.b8.bits) := by
  unfold vecPalignr
  exact laneGet_mk .b8 _ i hi

/-- Silicon spot-check: `0x80` stays `0x80`, `0xFF` becomes `1`. -/
theorem pabsLane_silicon :
    pabsLane .b8 128 = 128 ∧ pabsLane .b8 255 = 1 ∧
      pabsLane .b8 5 = 5 := by
  decide

/-- Silicon spot-check: the 16-bit INT_MIN wraps. -/
theorem pabsLane_silicon16 :
    pabsLane .b16 32768 = 32768 ∧ pabsLane .b16 65535 = 1 := by
  decide

/-- Silicon spot-check: shuffle zeroes on bit 7, selects otherwise. -/
theorem vecPshufb_silicon :
    laneNat .b8 (vecPshufb (vecMk .b8 (fun i => i))
      (vecMk .b8 (fun i => if i = 0 then 128 else 1))) 0 = 0 ∧
    laneNat .b8 (vecPshufb (vecMk .b8 (fun i => i))
      (vecMk .b8 (fun i => if i = 0 then 128 else 1))) 1 = 1 := by
  decide

/-- Silicon spot-check: align shifts the composite, zeroes past 32. -/
theorem vecPalignr_silicon :
    laneNat .b8 (vecPalignr (vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun _ => 3)) (natByte 1)) 0 = 3 ∧
    laneNat .b8 (vecPalignr (vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun _ => 3)) (natByte 16)) 0 = 7 ∧
    laneNat .b8 (vecPalignr (vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun _ => 3)) (natByte 32)) 0 = 0 := by
  decide

/-! ## 4. Step semantics on the shared XMM state.

  `stepSseThree` steps ONLY the §1 forms on the SAME `FpZustand` the
  scalar FP and vector steps use (`xmmSet` writes the whole 128-bit
  register, `ripNach` advances RIP, `vecEintritt` gates on OS vector
  state). PABSB/W/D read the SOURCE register (destination is
  write-only, per the SDM operand encoding); PSHUFB and PALIGNR read
  both. Flags, memory, GPRs and every other XMM register are
  untouched -- these forms have no flag, fault or memory effect. -/

/-- Single three-byte step; `none` is an explicit refusal (bad length
    or refused OS vector state). -/
def stepSseThree (d : SseThreeDec) (t : FpZustand) (b : BereitProfil) :
    Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match vecEintritt b with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.op with
      | .pshufbRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPshufb (t.xmm dst) (t.xmm src)) }
      | .pabsBRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPabs .b8 (t.xmm src)) }
      | .pabsWRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPabs .b16 (t.xmm src)) }
      | .pabsDRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPabs .b32 (t.xmm src)) }
      | .palignrRR dst src imm =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPalignr (t.xmm dst) (t.xmm src) imm) }

/-- A bad decode length refuses every three-byte form. -/
theorem stepSseThree_laenge_verweigert (d : SseThreeDec)
    (t : FpZustand) (b : BereitProfil)
    (h : laengeOk d.laenge = false) : stepSseThree d t b = none := by
  unfold stepSseThree
  simp [h]

/-- Refused OS vector state refuses every three-byte form (validator
    admission, not a hardware fault). -/
theorem stepSseThree_profil_verweigert (d : SseThreeDec)
    (t : FpZustand) (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (h : vecEintritt b = false) :
    stepSseThree d t b = none := by
  unfold stepSseThree
  simp [hok, h]

/-- `pshufb`: the destination holds the shuffled word. -/
theorem stepSseThree_pshufb (d : SseThreeDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .pshufbRR dst src) :
    stepSseThree d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPshufb (t.xmm dst) (t.xmm src)) } := by
  unfold stepSseThree
  simp [hok, hfp, h]

/-- `pabsb`: the destination holds the source's absolute value. -/
theorem stepSseThree_pabsb (d : SseThreeDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .pabsBRR dst src) :
    stepSseThree d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPabs .b8 (t.xmm src)) } := by
  unfold stepSseThree
  simp [hok, hfp, h]

/-- `pabsw`: the destination holds the source's absolute value. -/
theorem stepSseThree_pabsw (d : SseThreeDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .pabsWRR dst src) :
    stepSseThree d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPabs .b16 (t.xmm src)) } := by
  unfold stepSseThree
  simp [hok, hfp, h]

/-- `pabsd`: the destination holds the source's absolute value. -/
theorem stepSseThree_pabsd (d : SseThreeDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .pabsDRR dst src) :
    stepSseThree d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPabs .b32 (t.xmm src)) } := by
  unfold stepSseThree
  simp [hok, hfp, h]

/-- `palignr`: the destination holds the shifted composite. -/
theorem stepSseThree_palignr (d : SseThreeDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (imm : Byte)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .palignrRR dst src imm) :
    stepSseThree d t b = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecPalignr (t.xmm dst) (t.xmm src) imm) } := by
  unfold stepSseThree
  simp [hok, hfp, h]

/-! ## 5. Step frames: flags, memory, GPRs, other registers, RIP.

  Every form preserves rFLAGS, changes no memory byte, keeps every
  GPR, keeps every other XMM register whole, and advances RIP past
  the decoded length. -/

/-- The destination register a form writes. -/
def sseThreeDst : SseThreeOp → XmmReg
  | .pshufbRR dst _ => dst
  | .pabsBRR dst _ => dst
  | .pabsWRR dst _ => dst
  | .pabsDRR dst _ => dst
  | .palignrRR dst _ _ => dst

/-- Every three-byte step advances RIP past the decoded length. -/
theorem stepSseThree_rip (d : SseThreeDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseThree d t b = some t') :
    t'.kern.rip = ripNach t.kern.rip d.laenge := by
  revert hstep
  unfold stepSseThree
  rw [hok, hfp]
  cases hop : d.op with
  | pshufbRR dst src => intro hstep; cases hstep; rfl
  | pabsBRR dst src => intro hstep; cases hstep; rfl
  | pabsWRR dst src => intro hstep; cases hstep; rfl
  | pabsDRR dst src => intro hstep; cases hstep; rfl
  | palignrRR dst src imm => intro hstep; cases hstep; rfl

/-- Every three-byte step preserves the flags. -/
theorem stepSseThree_flags (d : SseThreeDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseThree d t b = some t') :
    t'.kern.flags = t.kern.flags := by
  revert hstep
  unfold stepSseThree
  rw [hok, hfp]
  cases hop : d.op with
  | pshufbRR dst src => intro hstep; cases hstep; rfl
  | pabsBRR dst src => intro hstep; cases hstep; rfl
  | pabsWRR dst src => intro hstep; cases hstep; rfl
  | pabsDRR dst src => intro hstep; cases hstep; rfl
  | palignrRR dst src imm => intro hstep; cases hstep; rfl

/-- Every three-byte step changes no memory byte. -/
theorem stepSseThree_speicher (d : SseThreeDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseThree d t b = some t') :
    t'.kern.speicher = t.kern.speicher := by
  revert hstep
  unfold stepSseThree
  rw [hok, hfp]
  cases hop : d.op with
  | pshufbRR dst src => intro hstep; cases hstep; rfl
  | pabsBRR dst src => intro hstep; cases hstep; rfl
  | pabsWRR dst src => intro hstep; cases hstep; rfl
  | pabsDRR dst src => intro hstep; cases hstep; rfl
  | palignrRR dst src imm => intro hstep; cases hstep; rfl

/-- Every three-byte step keeps every GPR. -/
theorem stepSseThree_gpr (d : SseThreeDec) (t t' : FpZustand)
    (b : BereitProfil) (q : Register)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseThree d t b = some t') :
    t'.kern.register q = t.kern.register q := by
  revert hstep
  unfold stepSseThree
  rw [hok, hfp]
  cases hop : d.op with
  | pshufbRR dst src => intro hstep; cases hstep; rfl
  | pabsBRR dst src => intro hstep; cases hstep; rfl
  | pabsWRR dst src => intro hstep; cases hstep; rfl
  | pabsDRR dst src => intro hstep; cases hstep; rfl
  | palignrRR dst src imm => intro hstep; cases hstep; rfl

/-- Every three-byte step keeps every other XMM register whole. -/
theorem stepSseThree_fremd (d : SseThreeDec) (t t' : FpZustand)
    (b : BereitProfil) (q : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseThree d t b = some t') (hq : q ≠ sseThreeDst d.op) :
    t'.xmm q = t.xmm q := by
  revert hstep hq
  unfold stepSseThree
  rw [hok, hfp]
  cases hop : d.op with
  | pshufbRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPshufb (t.xmm dst) (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseThreeDst, hop] using hq)
  | pabsBRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPabs .b8 (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseThreeDst, hop] using hq)
  | pabsWRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPabs .b16 (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseThreeDst, hop] using hq)
  | pabsDRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPabs .b32 (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseThreeDst, hop] using hq)
  | palignrRR dst src imm =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPalignr (t.xmm dst) (t.xmm src) imm)) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseThreeDst, hop] using hq)

/-! ## 6. Extended capstone chain.

  `kapDecodeSse` runs the accepted `kapDecode` first and consults the
  three-byte decoder only where the old chain refuses, so dispatch is
  disjoint by construction. A maintainer wires the family in by adding
  the `decodeSseThree` arm behind every earlier arm of
  `HwKapsteinDecoder.kapDecode` (same position as the `avx2` arm:
  last, tried only where all earlier arms refuse). -/

/-- One row of the extended chain: the old chain first, the new
    family only where it refuses. -/
inductive KapSse where
  | alt : KapDekodiert → KapSse
  | neu : SseThreeDec → KapSse
  deriving DecidableEq, Repr

/-- Extended chain: `kapDecode` first, the three-byte decoder only
    where the old chain refuses. No old row is shadowed. -/
def kapDecodeSse : List Byte → Option (KapSse × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.alt k, rest)
    | none =>
      match decodeSseThree bs with
      | some (d, rest) => some (.neu d, rest)
      | none => none

/-- The extended chain agrees with the old chain on every byte string
    the old chain accepts: no existing form is shadowed. -/
theorem kapDecodeSse_alt (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeSse bs = some (.alt k, rest) := by
  unfold kapDecodeSse
  rw [h]

/-- Where the old chain refuses, a covered three-byte row is taken. -/
theorem kapDecodeSse_neu (bs : List Byte) (d : SseThreeDec)
    (rest : List Byte) (h1 : kapDecode bs = none)
    (h2 : decodeSseThree bs = some (d, rest)) :
    kapDecodeSse bs = some (.neu d, rest) := by
  unfold kapDecodeSse
  rw [h1, h2]

/-- Where both chains refuse, the extended chain refuses. -/
theorem kapDecodeSse_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : decodeSseThree bs = none) :
    kapDecodeSse bs = none := by
  unfold kapDecodeSse
  rw [h1, h2]

/-- Extended-chain pin: PSHUFB xmm1, xmm0 decodes through the new arm. -/
theorem kapSse_pin_pshufb :
    kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] =
      some (KapSse.neu (⟨.pshufbRR .xmm1 .xmm0, 6⟩ : SseThreeDec), []) := by
  decide

/-- Extended-chain pin: PABSB xmm2, xmm3 decodes through the new arm. -/
theorem kapSse_pin_pabsb :
    kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 28, natByte 211] =
      some (KapSse.neu (⟨.pabsBRR .xmm2 .xmm3, 6⟩ : SseThreeDec), []) := by
  decide

/-- Extended-chain pin: PABSW xmm3, xmm4 decodes through the new arm. -/
theorem kapSse_pin_pabsw :
    kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 29, natByte 220] =
      some (KapSse.neu (⟨.pabsWRR .xmm3 .xmm4, 6⟩ : SseThreeDec), []) := by
  decide

/-- Extended-chain pin: PABSD xmm4, xmm5 decodes through the new arm. -/
theorem kapSse_pin_pabsd :
    kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 30, natByte 229] =
      some (KapSse.neu (⟨.pabsDRR .xmm4 .xmm5, 6⟩ : SseThreeDec), []) := by
  decide

/-- Extended-chain pin: PALIGNR xmm5, xmm6, 7 decodes through the new arm. -/
theorem kapSse_pin_palignr :
    kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 238, natByte 7] =
      some (KapSse.neu (⟨.palignrRR .xmm5 .xmm6 (natByte 7), 7⟩ :
        SseThreeDec), []) := by
  decide

/-- The old chain refuses the MOVBE bytes beside the new refusal. -/
theorem kap_weist_movbe_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 240, natByte 200] = none := by
  decide

/-- The old chain refuses a BLENDVPS `0F 3A` row beside the new refusal. -/
theorem kap_weist_blendv_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 20, natByte 200, natByte 0] = none := by
  decide

/-- The extended chain refuses MOVBE: neither chain admits it. -/
theorem kapSse_nichts_movbe :
    kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 240, natByte 200] = none :=
  kapDecodeSse_nichts _ kap_weist_movbe_zurueck sseThree_nichts_movbe

/-- The extended chain refuses BLENDVPS: neither chain admits it. -/
theorem kapSse_nichts_blendv :
    kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 20, natByte 200, natByte 0] = none :=
  kapDecodeSse_nichts _ kap_weist_blendv_zurueck sseThree_nichts_blendv

/-! ## 7. Machine adapter: the family on the coherent machine.

  The producer plug instantiates `HwAdapter SseThreeDec`: a
  successful family step re-embeds XMM/core data over the shared
  memory; refusals admit no successor state. -/

/-- The three-byte plug: one checked family event step on the coherent
    machine. `none` = refusal, never a silent successor. -/
def adapterSseThree : HwAdapter SseThreeDec :=
  ⟨fun m c d =>
    match stepSseThree d (projFp m c) (m.bereit c) with
    | some t' => some (setKernVonFp m c t')
    | none => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterSseThree_wf (m : HwMaschine) (c : Nat)
    (d : SseThreeDec) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterSseThree).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterSseThree at h
  simp only at h
  cases hsch : stepSseThree d (projFp m c) (m.bereit c) with
  | some t' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | none =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the family step
    succeeds, with the successor core data re-embedded. -/
theorem adapterSseThree_ok (m : HwMaschine) (c : Nat)
    (d : SseThreeDec) (t' : FpZustand)
    (h : stepSseThree d (projFp m c) (m.bereit c) = some t') :
    (adapterSseThree).schritt m c d = some (setKernVonFp m c t') := by
  unfold adapterSseThree
  simp only [h]

/-- The successor keeps the shared memory and every buffer. -/
theorem adapterSseThree_mem (m : HwMaschine) (c : Nat)
    (d : SseThreeDec) (m' : HwMaschine)
    (h : (adapterSseThree).schritt m c d = some m') :
    m'.mem = m.mem ∧ ∀ e : Nat, m'.puffer e = m.puffer e := by
  unfold adapterSseThree at h
  simp only at h
  cases hsch : stepSseThree d (projFp m c) (m.bereit c) with
  | some t' =>
    rw [hsch] at h
    simp only at h
    cases h
    exact ⟨setKernVonFp_speicher _ _ _,
      fun e => setKernVonFp_puffer _ _ _ e⟩
  | none =>
    rw [hsch] at h
    simp only at h
    cases h

/-- A bad decode length admits no adapter step. -/
theorem adapterSseThree_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : SseThreeDec)
    (h : laengeOk d.laenge = false) :
    (adapterSseThree).schritt m c d = none := by
  have hstep := stepSseThree_laenge_verweigert d (projFp m c)
    (m.bereit c) h
  unfold adapterSseThree
  simp only [hstep]

/-- Refused OS vector state admits no adapter step. -/
theorem adapterSseThree_verweigert_bei_profil (m : HwMaschine)
    (c : Nat) (d : SseThreeDec)
    (hok : laengeOk d.laenge = true)
    (h : vecEintritt (m.bereit c) = false) :
    (adapterSseThree).schritt m c d = none := by
  have hstep := stepSseThree_profil_verweigert d (projFp m c)
    (m.bereit c) hok h
  unfold adapterSseThree
  simp only [hstep]

/-! ## 8. Joint witness: two cores, family steps, buffered store.

  Core 0 shuffles (PSHUFB over an identity destination with control
  index 1, so every byte becomes 1), core 1 takes an absolute value
  (PABSB over `[255, 5, ...]`, so the first lanes become 1 and 5);
  beside the run core 0 issues a buffered byte store that only the
  owner observes by forwarding, and the drain changes actual shared
  memory from 0 to 99. The family itself is register-only by silicon
  (no admitted memory operand), so the memory half reuses the
  accepted TSO equations, exactly like every other family witness.
  Non-degenerate: XMM bytes change and shared memory changes. -/

/-- Witness XMM file of core 0: shuffle destination (identity bytes)
    in xmm0, shuffle control (constant index 1) in xmm1. -/
def sseWitXmm0 : XmmDatei := fun r =>
  if r = XmmReg.xmm0 then vecMk .b8 (fun i => i)
  else if r = XmmReg.xmm1 then vecMk .b8 (fun _ => 1)
  else BitVec.ofNat 128 0

/-- Witness XMM file of core 1: absolute-value source `[255, 5, ...]`
    in xmm3, destination xmm2 starts zeroed. -/
def sseWitXmm1 : XmmDatei := fun r =>
  if r = XmmReg.xmm3 then vecMk .b8 (fun i => if i = 0 then 255 else 5)
  else BitVec.ofNat 128 0

/-- Witness cores: core 0 shuffles, core 1 takes the absolute value. -/
def sseWitKern : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, sseWitXmm0, kontextReset⟩
  | 1 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, sseWitXmm1, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two family cores, empty
    buffers, full silicon. -/
def sseWitStart : HwMaschine :=
  ⟨zeugeSpeicher, sseWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem sseWitStart_wf : HwWf sseWitStart := by
  intro c f _
  cases f <;> rfl

/-- Core 0 shuffle step through the adapter. -/
def sseWitOut0 : Option HwMaschine :=
  (adapterSseThree).schritt sseWitStart 0
    (⟨.pshufbRR .xmm0 .xmm1, 6⟩ : SseThreeDec)

/-- Core 1 absolute-value step through the adapter. -/
def sseWitOut1 : Option HwMaschine :=
  (adapterSseThree).schritt sseWitStart 1
    (⟨.pabsBRR .xmm2 .xmm3, 6⟩ : SseThreeDec)

/-- Read one byte lane out of an adapter outcome. -/
def sseWitLane (o : Option HwMaschine) (c : Nat) (r : XmmReg)
    (i : Nat) : Option Nat :=
  match o with
  | some m => some (laneNat .b8 ((m.kerne c).xmm r) i)
  | none => none

/-- Core 0 shuffle: every destination byte becomes the indexed
    source byte 1. -/
theorem sseWit_shufb_lane0 :
    sseWitLane sseWitOut0 0 XmmReg.xmm0 0 = some 1 := by
  decide

/-- The shuffle destination started at byte 0: the step changes XMM. -/
theorem sseWit_shufb_vorher :
    laneNat .b8 (sseWitXmm0 XmmReg.xmm0) 0 = 0 := by
  decide

/-- Core 1 absolute value: `0xFF` becomes 1. -/
theorem sseWit_pabs_lane0 :
    sseWitLane sseWitOut1 1 XmmReg.xmm2 0 = some 1 := by
  decide

/-- Core 1 absolute value: `5` stays 5. -/
theorem sseWit_pabs_lane1 :
    sseWitLane sseWitOut1 1 XmmReg.xmm2 1 = some 5 := by
  decide

/-- Witness data address. -/
def sseWitAdr : Adresse := BitVec.ofNat 64 12288

/-- Witness TSO start: canonical memory, empty buffers. -/
def sseWitTso0 : TSOZustand := ⟨zeugeSpeicher, fun _ => []⟩

/-- Core 0 issues byte 99 at the data cell. -/
def sseWitTso1 : Option TSOZustand :=
  issueByte sseWitTso0 0 sseWitAdr (BitVec.ofNat 8 99)

/-- Core 0 observes its own byte (forwarding). -/
def sseWitEigen : Option (Option Byte) :=
  match sseWitTso1 with
  | some s => some (loadByte s 0 sseWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def sseWitFremd : Option (Option Byte) :=
  match sseWitTso1 with
  | some s => some (loadByte s 1 sseWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def sseWitTso2 : Option TSOZustand :=
  match sseWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def sseWitNachFlush : Option (Option Byte) :=
  match sseWitTso2 with
  | some s => some (some (s.mem.bytes sseWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def sseWitFremdNach : Option (Option Byte) :=
  match sseWitTso2 with
  | some s => some (loadByte s 1 sseWitAdr)
  | none => none

/-- The data cell starts zeroed. -/
theorem sseWit_anfang_null :
    zeugeSpeicher.bytes sseWitAdr = BitVec.ofNat 8 0 := by
  rfl

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem sseWit_weiterleitung :
    sseWitEigen = some (some (BitVec.ofNat 8 99)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem sseWit_fremd_alt :
    sseWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 99. -/
theorem sseWit_spuelung_aendert_speicher :
    sseWitNachFlush = some (some (BitVec.ofNat 8 99)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem sseWit_fremd_neu :
    sseWitFremdNach = some (some (BitVec.ofNat 8 99)) := by
  decide

/-- A bad decode length refuses the adapter step beside the run. -/
theorem sseWit_schlechte_laenge_verweigert :
    (adapterSseThree).schritt sseWitStart 0
      (⟨.pshufbRR .xmm0 .xmm1, 0⟩ : SseThreeDec) = none :=
  adapterSseThree_verweigert_bei_laenge _ _ _ (by decide)

/-- The joint witness: a reached two-core family run (shuffle on core
    0, absolute value on core 1) beside a buffered store that only
    the owner forwards and a drain that changes actual shared memory
    from 0 to 99 -- with the refusal and decode refusals beside it.
    Non-degenerate: XMM bytes change and shared memory changes. -/
theorem sseWit_zeuge :
    sseWitLane sseWitOut0 0 XmmReg.xmm0 0 = some 1 ∧
      laneNat .b8 (sseWitXmm0 XmmReg.xmm0) 0 = 0 ∧
      sseWitLane sseWitOut1 1 XmmReg.xmm2 0 = some 1 ∧
      sseWitLane sseWitOut1 1 XmmReg.xmm2 1 = some 5 ∧
      sseWitEigen = some (some (BitVec.ofNat 8 99)) ∧
      sseWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      sseWitNachFlush = some (some (BitVec.ofNat 8 99)) ∧
      sseWitFremdNach = some (some (BitVec.ofNat 8 99)) ∧
      zeugeSpeicher.bytes sseWitAdr = BitVec.ofNat 8 0 ∧
      HwWf sseWitStart ∧
      (adapterSseThree).schritt sseWitStart 0
        (⟨.pshufbRR .xmm0 .xmm1, 0⟩ : SseThreeDec) = none ∧
      decodeSseThree [natByte 64, natByte 102, natByte 15, natByte 56,
        natByte 240, natByte 200] = none ∧
      kapDecodeSse [natByte 64, natByte 102, natByte 15, natByte 58,
        natByte 20, natByte 200, natByte 0] = none := by
  refine ⟨sseWit_shufb_lane0, sseWit_shufb_vorher, sseWit_pabs_lane0,
    sseWit_pabs_lane1, sseWit_weiterleitung, sseWit_fremd_alt,
    sseWit_spuelung_aendert_speicher, sseWit_fremd_neu,
    sseWit_anfang_null, sseWitStart_wf,
    sseWit_schlechte_laenge_verweigert, sseThree_nichts_movbe,
    kapSse_nichts_blendv⟩

/- CUTS:
   Proved here: five admitted SSSE3 register-direct XMM rows (PSHUFB
   `66 0F 38 00`, PABSB/W/D `66 0F 38 1C/1D/1E`, PALIGNR
   `66 0F 3A 0F + imm8`) with canonical encoding, a canonical
   decoder, per-row round trips, planted decoder refusals, five
   decide-pins that the old capstone chain refuses the new bytes,
   semantics from the accepted lane vocabulary with per-lane
   equations and silicon spot-checks, a family step with frame
   theorems, the extended chain `kapDecodeSse` with exact agreement
   and extended-chain pins, the `HwAdapter SseThreeDec` plug with
   well-formedness preservation and planted refusals, and a reached
   two-core run with owner-only forwarding and a memory-changing
   drain.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the canonical subset
     with self-consistency only, not x86 truth. Silicon assumptions
     named: the five opcode rows (SDM Vol. 2B 4-176/4-216/4-422),
     PSHUFB zero-on-bit-7, PABS UNSIGNED result with INT_MIN wrap,
     PALIGNR `((DEST << 128) OR SRC) >> (imm8*8)` with zero past 32,
     legacy-SSE whole-register XMM writes (upper YMM unmodified),
     no flag/memory/GPR effect. The map transcription is a NAMED
     assumption.
   - No MMX (NP) forms, no memory ModRM forms, no REX.W forms, no
     other third byte in either escape (SSE4.1/SSE4.2/AES/MOVBE/
     CRC32 stay refused: MOVBE/BLENDVPS pins beside the run).
   - PHADD/PHSUB saturation, PSIGN, PMULHRSW and the whole SSE4
     remainder are not modelled.
   - No VEX/EVEX, no SIB/addressed operands, no LOCK path, no
     source/IR/ABI/loader/entry/budget link, no per-access
     target-to-W/GX simulation, no timing/power behaviour.
   - A maintainer wires the family in by adding the
     `decodeSseThree` arm behind every earlier arm of
     `HwKapsteinDecoder.kapDecode`.
-/

#print axioms encodeSseThree
#print axioms decodeSseThree
#print axioms roundtripSseThree
#print axioms vecPabs
#print axioms vecPshufb
#print axioms vecPalignr
#print axioms stepSseThree
#print axioms kapDecodeSse
#print axioms adapterSseThree
#print axioms adapterSseThree_wf
#print axioms sseWitStart_wf
#print axioms sseWit_zeuge

end Gabbro.Grammatik.X86
