/-
  File:      Grammatik/X86/SseFourOne.lean
  Subject:   SSE4.1/SSE4.2 register-direct XMM rows over the 0F 38 escape,
    connected to the coherent machine and the capstone chain.

  Lane 1371: admitted register-direct XMM rows only -- PMOVSXBW
  (`66 0F 38 20 /r`), PMOVZXBW (`66 0F 38 30 /r`), PMINSD
  (`66 0F 38 39 /r`), PMAXSD (`66 0F 38 3D /r`), PMULLD
  (`66 0F 38 40 /r`) and PCMPEQQ (`66 0F 38 29 /r`). Canonical REX
  (`64 + 4*R + B`, W=0/X=0) is required, exactly like the accepted
  `SseThreeByte` rows. Semantics reuse the accepted lane vocabulary
  (`laneNat`/`vecMk`); no evaluator is redefined. Memory ModRM forms,
  REX.W forms and every other third byte stay refused (see CUTS).
  Silicon provenance: Intel SDM 325462-093US (Sep 2026), clone-local
  `.tmp/HARDWARE-REFERENCES/` `intel-instruction-reference.txt`.
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Kern.Ganzzahl
import Grammatik.X86.Kern.Gleitprofil
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- Admitted SSE4.1 register forms: sign/zero extend, signed min/max,
    32-bit multiply, 64-bit equality compare. -/
inductive SseFourOp where
  | pmovsxbwRR (dst src : XmmReg)
  | pmovzxbwRR (dst src : XmmReg)
  | pminsdRR (dst src : XmmReg)
  | pmaxsdRR (dst src : XmmReg)
  | pmulldRR (dst src : XmmReg)
  | pcmpeqqRR (dst src : XmmReg)
  deriving DecidableEq, Repr

/-- Escape byte after `0F`: all six rows live in the `0F 38` map. -/
def sseFourEscape : SseFourOp → Nat
  | _ => 56

/-- Third opcode byte: `20/30/39/3D/40/29` (SDM Vol. 2B). -/
def sseFourThird : SseFourOp → Nat
  | .pmovsxbwRR _ _ => 32
  | .pmovzxbwRR _ _ => 48
  | .pminsdRR _ _ => 57
  | .pmaxsdRR _ _ => 61
  | .pmulldRR _ _ => 64
  | .pcmpeqqRR _ _ => 41

/-- Canonical REX byte for one form (W=0, X=0, always emitted, exactly
    like the accepted `vectorRex` and `sseThreeRex`). -/
def sseFourRex : SseFourOp → Byte
  | .pmovsxbwRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pmovzxbwRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pminsdRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pmaxsdRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pmulldRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .pcmpeqqRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)

/-- Canonical byte encoding: REX, `66`, `0F`, escape `38`, third byte,
    register-direct ModRM (mod=3, reg=dst, r/m=src). 6 bytes. -/
def encodeSseFour : SseFourOp → List Byte
  | op@(.pmovsxbwRR dst src) =>
    [sseFourRex op, natByte 102, natByte 15, natByte (sseFourEscape op),
      natByte (sseFourThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pmovzxbwRR dst src) =>
    [sseFourRex op, natByte 102, natByte 15, natByte (sseFourEscape op),
      natByte (sseFourThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pminsdRR dst src) =>
    [sseFourRex op, natByte 102, natByte 15, natByte (sseFourEscape op),
      natByte (sseFourThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pmaxsdRR dst src) =>
    [sseFourRex op, natByte 102, natByte 15, natByte (sseFourEscape op),
      natByte (sseFourThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pmulldRR dst src) =>
    [sseFourRex op, natByte 102, natByte 15, natByte (sseFourEscape op),
      natByte (sseFourThird op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pcmpeqqRR dst src) =>
    [sseFourRex op, natByte 102, natByte 15, natByte (sseFourEscape op),
      natByte (sseFourThird op), modrmReg (xmmLow dst) (xmmLow src)]

/-- Every canonical encoding is 6 bytes. -/
theorem encodeSseFour_len6 (op : SseFourOp) :
    (encodeSseFour op).length = 6 := by
  cases op <;> rfl

/-- The old capstone chain refuses the canonical PMOVSXBW bytes. -/
theorem kap_weist_pmovsxbw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 32, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PMOVZXBW bytes. -/
theorem kap_weist_pmovzxbw_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 48, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PMINSD bytes. -/
theorem kap_weist_pminsd_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 57, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PMAXSD bytes. -/
theorem kap_weist_pmaxsd_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 61, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PMULLD bytes. -/
theorem kap_weist_pmulld_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 64, natByte 200] = none := by
  decide

/-- The old capstone chain refuses the canonical PCMPEQQ bytes. -/
theorem kap_weist_pcmpeqq_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 41, natByte 200] = none := by
  decide

/-! ## 2. Canonical decoder.

  The decoder parses bytes, never encode-equality. Only the canonical
  REX prefix (`64 + 4*R + B`: W=0, X=0), then `66`, `0F`, the escape
  `38`, the third byte, and a register-direct ModRM (mod=3,
  reg=dst, r/m=src) are admitted. Anything else refuses with `none`. -/

/-- A decoded SSE4.1 form: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure SseFourDec where
  op : SseFourOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- Decode one register-direct ModRM byte after the admitted prefix,
    escape and third byte. -/
def decodeSseFourModrm (esc opByte rBit bBit : Nat) :
    List Byte → Option (SseFourOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src =>
        match esc, opByte with
        | 56, 32 => some ((.pmovsxbwRR dst src), rest)
        | 56, 48 => some ((.pmovzxbwRR dst src), rest)
        | 56, 57 => some ((.pminsdRR dst src), rest)
        | 56, 61 => some ((.pmaxsdRR dst src), rest)
        | 56, 64 => some ((.pmulldRR dst src), rest)
        | 56, 41 => some ((.pcmpeqqRR dst src), rest)
        | _, _ => none
      | _, _ => none
    else none

/-- Decode after the canonical REX prefix: `66`, then `0F`, then the
    escape byte `38`, the third byte, then ModRM. -/
def decodeSseFourNach (rBit bBit : Nat) :
    List Byte → Option (SseFourOp × List Byte)
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
            if byteNat esc == 56 then
              match rest3 with
              | [] => none
              | op :: rest4 =>
                decodeSseFourModrm (byteNat esc) (byteNat op)
                  rBit bBit rest4
            else none
        else none
    else none

/-- Top-level SSE4.1 decode: the REX prefix selects the extension
    bits; anything without a canonical REX refuses. The decoded length
    is the canonical encoding length of the decoded form. -/
def decodeSseFour : List Byte → Option (SseFourDec × List Byte)
  | [] => none
  | r :: tail =>
    let nach (rBit bBit : Nat) :=
      match decodeSseFourNach rBit bBit tail with
      | some (op, rest) =>
        some ((⟨op, (encodeSseFour op).length⟩ : SseFourDec), rest)
      | none => none
    match byteNat r with
    | 64 => nach 0 0
    | 65 => nach 0 1
    | 68 => nach 1 0
    | 69 => nach 1 1
    | _ => none

/-- Round trip for PMOVSXBW, over any suffix. -/
theorem roundtrip_pmovsxbw (dst src : XmmReg) (suffix : List Byte) :
    decodeSseFour (encodeSseFour (.pmovsxbwRR dst src) ++ suffix) =
      some ((⟨.pmovsxbwRR dst src,
        (encodeSseFour (.pmovsxbwRR dst src)).length⟩ : SseFourDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PMOVZXBW, over any suffix. -/
theorem roundtrip_pmovzxbw (dst src : XmmReg) (suffix : List Byte) :
    decodeSseFour (encodeSseFour (.pmovzxbwRR dst src) ++ suffix) =
      some ((⟨.pmovzxbwRR dst src,
        (encodeSseFour (.pmovzxbwRR dst src)).length⟩ : SseFourDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PMINSD, over any suffix. -/
theorem roundtrip_pminsd (dst src : XmmReg) (suffix : List Byte) :
    decodeSseFour (encodeSseFour (.pminsdRR dst src) ++ suffix) =
      some ((⟨.pminsdRR dst src,
        (encodeSseFour (.pminsdRR dst src)).length⟩ : SseFourDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PMAXSD, over any suffix. -/
theorem roundtrip_pmaxsd (dst src : XmmReg) (suffix : List Byte) :
    decodeSseFour (encodeSseFour (.pmaxsdRR dst src) ++ suffix) =
      some ((⟨.pmaxsdRR dst src,
        (encodeSseFour (.pmaxsdRR dst src)).length⟩ : SseFourDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PMULLD, over any suffix. -/
theorem roundtrip_pmulld (dst src : XmmReg) (suffix : List Byte) :
    decodeSseFour (encodeSseFour (.pmulldRR dst src) ++ suffix) =
      some ((⟨.pmulldRR dst src,
        (encodeSseFour (.pmulldRR dst src)).length⟩ : SseFourDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PCMPEQQ, over any suffix. -/
theorem roundtrip_pcmpeqq (dst src : XmmReg) (suffix : List Byte) :
    decodeSseFour (encodeSseFour (.pcmpeqqRR dst src) ++ suffix) =
      some ((⟨.pcmpeqqRR dst src,
        (encodeSseFour (.pcmpeqqRR dst src)).length⟩ : SseFourDec),
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every covered row, over any suffix.
    The decoded length is the canonical encoding length. -/
theorem roundtripSseFour (op : SseFourOp) (suffix : List Byte) :
    decodeSseFour (encodeSseFour op ++ suffix) =
      some ((⟨op, (encodeSseFour op).length⟩ : SseFourDec), suffix) := by
  cases op with
  | pmovsxbwRR dst src => exact roundtrip_pmovsxbw dst src suffix
  | pmovzxbwRR dst src => exact roundtrip_pmovzxbw dst src suffix
  | pminsdRR dst src => exact roundtrip_pminsd dst src suffix
  | pmaxsdRR dst src => exact roundtrip_pmaxsd dst src suffix
  | pmulldRR dst src => exact roundtrip_pmulld dst src suffix
  | pcmpeqqRR dst src => exact roundtrip_pcmpeqq dst src suffix

/-- A memory ModRM (mod≠3) is refused: only register forms are covered. -/
theorem sseFour_nichts_speicher :
    decodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 32, natByte 8] = none := rfl

/-- A truncated prefix (REX + `66` only) is refused. -/
theorem sseFour_nichts_kurz :
    decodeSseFour [natByte 64, natByte 102] = none := rfl

/-- A wrong escape (`0F 39`) is refused. -/
theorem sseFour_nichts_escape :
    decodeSseFour [natByte 64, natByte 102, natByte 15, natByte 57,
      natByte 32, natByte 200] = none := rfl

/-- A REX.W form is refused: only the canonical W=0 REX is admitted. -/
theorem sseFour_nichts_rexw :
    decodeSseFour [natByte 72, natByte 102, natByte 15, natByte 56,
      natByte 32, natByte 200] = none := rfl

/-- An uncovered `0F 38` third byte (PSHUFB `00`) is refused here:
    the SSSE3 family owns it. -/
theorem sseFour_nichts_pshufb :
    decodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := rfl

/-- An `0F 3A` row (PALIGNR) is refused here: the SSSE3 family owns it. -/
theorem sseFour_nichts_palignr :
    decodeSseFour [natByte 64, natByte 102, natByte 15, natByte 58,
      natByte 15, natByte 200, natByte 4] = none := rfl

/-! ## 3. Semantics from the accepted lane vocabulary.

  Built from the accepted `laneNat`/`vecMk` vocabulary only, matching
  the SDM operation pseudocode lane for lane:
  - PMOVSXBW (Vol. 2B 4-299): sign-extend the low eight bytes to
    eight words; PMOVZXBW (4-314): zero-extend them;
  - PMINSD/PMAXSD (4-183/4-205): signed 32-bit lane min/max;
  - PMULLD (4-274): low 32 bits of the signed 32-bit lane product;
  - PCMPEQQ (4-219): 64-bit lanes compare equal to all-ones else zero.
  Only the low eight source bytes feed the extend forms; upper source
  bytes are ignored (destination is write-only). -/

/-- Signed value of a 32-bit lane: `u` below 2^31, else `u - 2^32`. -/
def sVal32 (u : Nat) : Int :=
  if u < 2 ^ 31 then (u : Int) else (u : Int) - 2 ^ 32

/-- Sign-extend the low eight bytes to eight words (PMOVSXBW):
    bytes below 128 keep their value, bytes at/above 128 gain the
    high byte `0xFF` (pure Nat arithmetic: `u + 65280`). -/
def vecPmovsxbw (x : Vektor) : Vektor :=
  vecMk .b16 (fun i =>
    let u := laneNat .b8 x i
    if u < 128 then u else u + 65280)

/-- Zero-extend the low eight bytes to eight words (PMOVZXBW). -/
def vecPmovzxbw (x : Vektor) : Vektor :=
  vecMk .b16 (fun i => laneNat .b8 x i % 2 ^ 16)

/-- Signed 32-bit lane minimum (PMINSD). -/
def vecPminsd (dst src : Vektor) : Vektor :=
  vecMk .b32 (fun i =>
    if sVal32 (laneNat .b32 src i) < sVal32 (laneNat .b32 dst i) then
      laneNat .b32 src i
    else laneNat .b32 dst i)

/-- Signed 32-bit lane maximum (PMAXSD). -/
def vecPmaxsd (dst src : Vektor) : Vektor :=
  vecMk .b32 (fun i =>
    if sVal32 (laneNat .b32 src i) < sVal32 (laneNat .b32 dst i) then
      laneNat .b32 dst i
    else laneNat .b32 src i)

/-- Low 32 bits of the lane product (PMULLD). -/
def vecPmulld (dst src : Vektor) : Vektor :=
  vecMk .b32 (fun i => laneNat .b32 dst i * laneNat .b32 src i)

/-- 64-bit lane equality to all-ones or zero (PCMPEQQ). -/
def vecPcmpeqq (dst src : Vektor) : Vektor :=
  vecMk .b64 (fun i =>
    if laneNat .b64 dst i == laneNat .b64 src i then 2 ^ 64 - 1 else 0)

/-- Per-lane sign extension is the lane function on the source byte. -/
theorem laneNat_pmovsxbw (x : Vektor) (i : Nat)
    (hi : i < laneCount .b16) :
    laneNat .b16 (vecPmovsxbw x) i =
      ((let u := laneNat .b8 x i
        if u < 128 then u else u + 65280) % 2 ^ Breite.b16.bits) := by
  unfold vecPmovsxbw
  exact laneGet_mk .b16 _ i hi

/-- Per-lane zero extension is the lane function on the source byte. -/
theorem laneNat_pmovzxbw (x : Vektor) (i : Nat)
    (hi : i < laneCount .b16) :
    laneNat .b16 (vecPmovzxbw x) i =
      (laneNat .b8 x i % 2 ^ 16) % 2 ^ Breite.b16.bits := by
  unfold vecPmovzxbw
  exact laneGet_mk .b16 _ i hi

/-- Per-lane multiply is the product function on the two lanes. -/
theorem laneNat_pmulld (dst src : Vektor) (i : Nat)
    (hi : i < laneCount .b32) :
    laneNat .b32 (vecPmulld dst src) i =
      (laneNat .b32 dst i * laneNat .b32 src i) %
        2 ^ Breite.b32.bits := by
  unfold vecPmulld
  exact laneGet_mk .b32 _ i hi

/-- Per-lane quad compare is the equality function on the two lanes. -/
theorem laneNat_pcmpeqq (dst src : Vektor) (i : Nat)
    (hi : i < laneCount .b64) :
    laneNat .b64 (vecPcmpeqq dst src) i =
      ((if laneNat .b64 dst i == laneNat .b64 src i then 2 ^ 64 - 1
        else 0) % 2 ^ Breite.b64.bits) := by
  unfold vecPcmpeqq
  exact laneGet_mk .b64 _ i hi

/-- Silicon spot-check: sign extension wraps the top bit. -/
theorem vecPmovsx_silicon :
    laneNat .b16 (vecPmovsxbw (vecMk .b8 (fun i => if i = 0 then 255 else 5))) 0 = 65535 ∧
    laneNat .b16 (vecPmovsxbw (vecMk .b8 (fun i => if i = 0 then 255 else 5))) 1 = 5 ∧
    laneNat .b16 (vecPmovzxbw (vecMk .b8 (fun i => if i = 0 then 255 else 5))) 0 = 255 := by
  decide

/-- Silicon spot-check: signed min/max pick the signed extreme. -/
theorem vecPminmax_silicon :
    laneNat .b32 (vecPminsd (vecMk .b32 (fun _ => 5))
      (vecMk .b32 (fun _ => 4294967295))) 0 = 4294967295 ∧
    laneNat .b32 (vecPmaxsd (vecMk .b32 (fun _ => 5))
      (vecMk .b32 (fun _ => 4294967295))) 0 = 5 := by
  decide

/-- Silicon spot-check: multiply keeps the low 32 bits, compare is
    all-ones on equality and zero elsewhere. -/
theorem vecPmullcmp_silicon :
    laneNat .b32 (vecPmulld (vecMk .b32 (fun _ => 70000))
      (vecMk .b32 (fun _ => 70000))) 0 = 605032704 ∧
    laneNat .b64 (vecPcmpeqq (vecMk .b64 (fun _ => 7))
      (vecMk .b64 (fun _ => 7))) 0 = 18446744073709551615 ∧
    laneNat .b64 (vecPcmpeqq (vecMk .b64 (fun _ => 7))
      (vecMk .b64 (fun _ => 8))) 0 = 0 := by
  decide

/-! ## 4. Step semantics on the shared XMM state.

  `stepSseFour` steps ONLY the §1 forms on the SAME `FpZustand` the
  scalar FP and vector steps use (`xmmSet` writes the whole 128-bit
  register, `ripNach` advances RIP, `vecEintritt` gates on OS vector
  state). The extend forms read the SOURCE register (destination is
  write-only); the other four read both. Flags, memory, GPRs and every
  other XMM register are untouched -- these forms have no flag, fault
  or memory effect. -/

/-- Single SSE4.1 step; `none` is an explicit refusal (bad length
    or refused OS vector state). -/
def stepSseFour (d : SseFourDec) (t : FpZustand) (b : BereitProfil) :
    Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match vecEintritt b with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.op with
      | .pmovsxbwRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPmovsxbw (t.xmm src)) }
      | .pmovzxbwRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPmovzxbw (t.xmm src)) }
      | .pminsdRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPminsd (t.xmm dst) (t.xmm src)) }
      | .pmaxsdRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPmaxsd (t.xmm dst) (t.xmm src)) }
      | .pmulldRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPmulld (t.xmm dst) (t.xmm src)) }
      | .pcmpeqqRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecPcmpeqq (t.xmm dst) (t.xmm src)) }

/-- A bad decode length refuses every SSE4.1 form. -/
theorem stepSseFour_laenge_verweigert (d : SseFourDec)
    (t : FpZustand) (b : BereitProfil)
    (h : laengeOk d.laenge = false) : stepSseFour d t b = none := by
  unfold stepSseFour
  simp [h]

/-- Refused OS vector state refuses every SSE4.1 form (validator
    admission, not a hardware fault). -/
theorem stepSseFour_profil_verweigert (d : SseFourDec)
    (t : FpZustand) (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (h : vecEintritt b = false) :
    stepSseFour d t b = none := by
  unfold stepSseFour
  simp [hok, h]

/-- The destination register a form writes. -/
def sseFourDst : SseFourOp → XmmReg
  | .pmovsxbwRR dst _ => dst
  | .pmovzxbwRR dst _ => dst
  | .pminsdRR dst _ => dst
  | .pmaxsdRR dst _ => dst
  | .pmulldRR dst _ => dst
  | .pcmpeqqRR dst _ => dst

/-- Every SSE4.1 step advances RIP past the decoded length. -/
theorem stepSseFour_rip (d : SseFourDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseFour d t b = some t') :
    t'.kern.rip = ripNach t.kern.rip d.laenge := by
  revert hstep
  unfold stepSseFour
  rw [hok, hfp]
  cases hop : d.op with
  | pmovsxbwRR dst src => intro hstep; cases hstep; rfl
  | pmovzxbwRR dst src => intro hstep; cases hstep; rfl
  | pminsdRR dst src => intro hstep; cases hstep; rfl
  | pmaxsdRR dst src => intro hstep; cases hstep; rfl
  | pmulldRR dst src => intro hstep; cases hstep; rfl
  | pcmpeqqRR dst src => intro hstep; cases hstep; rfl

/-- Every SSE4.1 step preserves the flags. -/
theorem stepSseFour_flags (d : SseFourDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseFour d t b = some t') :
    t'.kern.flags = t.kern.flags := by
  revert hstep
  unfold stepSseFour
  rw [hok, hfp]
  cases hop : d.op with
  | pmovsxbwRR dst src => intro hstep; cases hstep; rfl
  | pmovzxbwRR dst src => intro hstep; cases hstep; rfl
  | pminsdRR dst src => intro hstep; cases hstep; rfl
  | pmaxsdRR dst src => intro hstep; cases hstep; rfl
  | pmulldRR dst src => intro hstep; cases hstep; rfl
  | pcmpeqqRR dst src => intro hstep; cases hstep; rfl

/-- Every SSE4.1 step changes no memory byte. -/
theorem stepSseFour_speicher (d : SseFourDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseFour d t b = some t') :
    t'.kern.speicher = t.kern.speicher := by
  revert hstep
  unfold stepSseFour
  rw [hok, hfp]
  cases hop : d.op with
  | pmovsxbwRR dst src => intro hstep; cases hstep; rfl
  | pmovzxbwRR dst src => intro hstep; cases hstep; rfl
  | pminsdRR dst src => intro hstep; cases hstep; rfl
  | pmaxsdRR dst src => intro hstep; cases hstep; rfl
  | pmulldRR dst src => intro hstep; cases hstep; rfl
  | pcmpeqqRR dst src => intro hstep; cases hstep; rfl

/-- Every SSE4.1 step keeps every GPR. -/
theorem stepSseFour_gpr (d : SseFourDec) (t t' : FpZustand)
    (b : BereitProfil) (q : Register)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseFour d t b = some t') :
    t'.kern.register q = t.kern.register q := by
  revert hstep
  unfold stepSseFour
  rw [hok, hfp]
  cases hop : d.op with
  | pmovsxbwRR dst src => intro hstep; cases hstep; rfl
  | pmovzxbwRR dst src => intro hstep; cases hstep; rfl
  | pminsdRR dst src => intro hstep; cases hstep; rfl
  | pmaxsdRR dst src => intro hstep; cases hstep; rfl
  | pmulldRR dst src => intro hstep; cases hstep; rfl
  | pcmpeqqRR dst src => intro hstep; cases hstep; rfl

/-- Every SSE4.1 step keeps every other XMM register whole. -/
theorem stepSseFour_fremd (d : SseFourDec) (t t' : FpZustand)
    (b : BereitProfil) (q : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepSseFour d t b = some t') (hq : q ≠ sseFourDst d.op) :
    t'.xmm q = t.xmm q := by
  revert hstep hq
  unfold stepSseFour
  rw [hok, hfp]
  cases hop : d.op with
  | pmovsxbwRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPmovsxbw (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseFourDst, hop] using hq)
  | pmovzxbwRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPmovzxbw (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseFourDst, hop] using hq)
  | pminsdRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPminsd (t.xmm dst) (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseFourDst, hop] using hq)
  | pmaxsdRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPmaxsd (t.xmm dst) (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseFourDst, hop] using hq)
  | pmulldRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPmulld (t.xmm dst) (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseFourDst, hop] using hq)
  | pcmpeqqRR dst src =>
    intro hstep hq; cases hstep
    show (xmmSet t.xmm dst (vecPcmpeqq (t.xmm dst) (t.xmm src))) q = _
    exact xmmSet_fremd _ _ _ _ (by simpa [sseFourDst, hop] using hq)

/-! ## 5. Extended capstone chain.

  `kapDecodeSseFour` runs the accepted `kapDecode` first and consults
  the SSE4.1 decoder only where the old chain refuses, so dispatch is
  disjoint by construction. A maintainer wires the family in by adding
  the `decodeSseFour` arm behind every earlier arm of
  `HwKapsteinDecoder.kapDecode` (same position as the `avx2` arm:
  last, tried only where all earlier arms refuse). -/

/-- One row of the extended chain: the old chain first, the new
    family only where it refuses. -/
inductive KapSseFour where
  | alt : KapDekodiert → KapSseFour
  | neu : SseFourDec → KapSseFour
  deriving DecidableEq, Repr

/-- Extended chain: `kapDecode` first, the SSE4.1 decoder only
    where the old chain refuses. No old row is shadowed. -/
def kapDecodeSseFour : List Byte → Option (KapSseFour × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.alt k, rest)
    | none =>
      match decodeSseFour bs with
      | some (d, rest) => some (.neu d, rest)
      | none => none

/-- The extended chain agrees with the old chain on every byte string
    the old chain accepts: no existing form is shadowed. -/
theorem kapDecodeSseFour_alt (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeSseFour bs = some (.alt k, rest) := by
  unfold kapDecodeSseFour
  rw [h]

/-- Where the old chain refuses, a covered SSE4.1 row is taken. -/
theorem kapDecodeSseFour_neu (bs : List Byte) (d : SseFourDec)
    (rest : List Byte) (h1 : kapDecode bs = none)
    (h2 : decodeSseFour bs = some (d, rest)) :
    kapDecodeSseFour bs = some (.neu d, rest) := by
  unfold kapDecodeSseFour
  rw [h1, h2]

/-- Where both chains refuse, the extended chain refuses. -/
theorem kapDecodeSseFour_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : decodeSseFour bs = none) :
    kapDecodeSseFour bs = none := by
  unfold kapDecodeSseFour
  rw [h1, h2]

/-- Extended-chain pin: PMOVSXBW xmm1, xmm0 decodes through the new arm. -/
theorem kapSseFour_pin_pmovsxbw :
    kapDecodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 32, natByte 200] =
      some (KapSseFour.neu (⟨.pmovsxbwRR .xmm1 .xmm0, 6⟩ : SseFourDec), []) := by
  decide

/-- Extended-chain pin: PMOVZXBW xmm1, xmm0 decodes through the new arm. -/
theorem kapSseFour_pin_pmovzxbw :
    kapDecodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 48, natByte 200] =
      some (KapSseFour.neu (⟨.pmovzxbwRR .xmm1 .xmm0, 6⟩ : SseFourDec), []) := by
  decide

/-- Extended-chain pin: PMINSD xmm1, xmm0 decodes through the new arm. -/
theorem kapSseFour_pin_pminsd :
    kapDecodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 57, natByte 200] =
      some (KapSseFour.neu (⟨.pminsdRR .xmm1 .xmm0, 6⟩ : SseFourDec), []) := by
  decide

/-- Extended-chain pin: PMULLD xmm1, xmm0 decodes through the new arm. -/
theorem kapSseFour_pin_pmulld :
    kapDecodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 64, natByte 200] =
      some (KapSseFour.neu (⟨.pmulldRR .xmm1 .xmm0, 6⟩ : SseFourDec), []) := by
  decide

/-- Extended-chain pin: PCMPEQQ xmm1, xmm0 decodes through the new arm. -/
theorem kapSseFour_pin_pcmpeqq :
    kapDecodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 41, natByte 200] =
      some (KapSseFour.neu (⟨.pcmpeqqRR .xmm1 .xmm0, 6⟩ : SseFourDec), []) := by
  decide

/-- The old chain refuses the PSHUFB bytes beside the new refusal. -/
theorem kapAlt_weist_pshufb_zurueck :
    kapDecode [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none := by
  decide

/-- The extended chain refuses PSHUFB: neither chain admits it here
    (the SSSE3 family owns it; this decoder refuses it). -/
theorem kapSseFour_nichts_pshufb :
    kapDecodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
      natByte 0, natByte 200] = none :=
  kapDecodeSseFour_nichts _ kapAlt_weist_pshufb_zurueck sseFour_nichts_pshufb

/-! ## 6. Machine adapter: the family on the coherent machine.

  The producer plug instantiates `HwAdapter SseFourDec`: a
  successful family step re-embeds XMM/core data over the shared
  memory; refusals admit no successor state. -/

/-- The SSE4.1 plug: one checked family event step on the coherent
    machine. `none` = refusal, never a silent successor. -/
def adapterSseFour : HwAdapter SseFourDec :=
  ⟨fun m c d =>
    match stepSseFour d (projFp m c) (m.bereit c) with
    | some t' => some (setKernVonFp m c t')
    | none => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterSseFour_wf (m : HwMaschine) (c : Nat)
    (d : SseFourDec) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterSseFour).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterSseFour at h
  simp only at h
  cases hsch : stepSseFour d (projFp m c) (m.bereit c) with
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
theorem adapterSseFour_ok (m : HwMaschine) (c : Nat)
    (d : SseFourDec) (t' : FpZustand)
    (h : stepSseFour d (projFp m c) (m.bereit c) = some t') :
    (adapterSseFour).schritt m c d = some (setKernVonFp m c t') := by
  unfold adapterSseFour
  simp only [h]

/-- The successor keeps the shared memory and every buffer. -/
theorem adapterSseFour_mem (m : HwMaschine) (c : Nat)
    (d : SseFourDec) (m' : HwMaschine)
    (h : (adapterSseFour).schritt m c d = some m') :
    m'.mem = m.mem ∧ ∀ e : Nat, m'.puffer e = m.puffer e := by
  unfold adapterSseFour at h
  simp only at h
  cases hsch : stepSseFour d (projFp m c) (m.bereit c) with
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
theorem adapterSseFour_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : SseFourDec)
    (h : laengeOk d.laenge = false) :
    (adapterSseFour).schritt m c d = none := by
  have hstep := stepSseFour_laenge_verweigert d (projFp m c)
    (m.bereit c) h
  unfold adapterSseFour
  simp only [hstep]

/-- Refused OS vector state admits no adapter step. -/
theorem adapterSseFour_verweigert_bei_profil (m : HwMaschine)
    (c : Nat) (d : SseFourDec)
    (hok : laengeOk d.laenge = true)
    (h : vecEintritt (m.bereit c) = false) :
    (adapterSseFour).schritt m c d = none := by
  have hstep := stepSseFour_profil_verweigert d (projFp m c)
    (m.bereit c) hok h
  unfold adapterSseFour
  simp only [hstep]

/-! ## 7. Joint witness: two cores, family steps, buffered store.

  Core 0 sign-extends (PMOVSXBW over `[255, 5, ...]`, so lanes become
  65535 and 5), core 1 multiplies (PMULLD over `[70000] x [70000]`,
  so the lane becomes 605032704); beside the run core 0 issues a
  buffered byte store that only the owner observes by forwarding, and
  the drain changes actual shared memory from 0 to 77. The family
  itself is register-only by silicon (no admitted memory operand), so
  the memory half reuses the accepted TSO equations, exactly like
  every other family witness. Non-degenerate: XMM lanes change and
  shared memory changes. -/

/-- Witness XMM file of core 0: extend source `[255, 5, ...]` in xmm1,
    destination xmm0 starts zeroed. -/
def sseFourWitXmm0 : XmmDatei := fun r =>
  if r = XmmReg.xmm1 then vecMk .b8 (fun i => if i = 0 then 255 else 5)
  else BitVec.ofNat 128 0

/-- Witness XMM file of core 1: multiply sources `[70000]` in xmm2
    and xmm3. -/
def sseFourWitXmm1 : XmmDatei := fun r =>
  if r = XmmReg.xmm2 then vecMk .b32 (fun _ => 70000)
  else if r = XmmReg.xmm3 then vecMk .b32 (fun _ => 70000)
  else BitVec.ofNat 128 0

/-- Witness cores: core 0 extends, core 1 multiplies. -/
def sseFourWitKern : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, sseFourWitXmm0, kontextReset⟩
  | 1 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096, sseFourWitXmm1, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two family cores, empty
    buffers, full silicon. -/
def sseFourWitStart : HwMaschine :=
  ⟨zeugeSpeicher, sseFourWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem sseFourWitStart_wf : HwWf sseFourWitStart := by
  intro c f _
  cases f <;> rfl

/-- Core 0 sign-extend step through the adapter. -/
def sseFourWitOut0 : Option HwMaschine :=
  (adapterSseFour).schritt sseFourWitStart 0
    (⟨.pmovsxbwRR .xmm0 .xmm1, 6⟩ : SseFourDec)

/-- Core 1 multiply step through the adapter. -/
def sseFourWitOut1 : Option HwMaschine :=
  (adapterSseFour).schritt sseFourWitStart 1
    (⟨.pmulldRR .xmm2 .xmm3, 6⟩ : SseFourDec)

/-- Read one 16-bit lane out of an adapter outcome. -/
def sseFourWitLane16 (o : Option HwMaschine) (c : Nat) (r : XmmReg)
    (i : Nat) : Option Nat :=
  match o with
  | some m => some (laneNat .b16 ((m.kerne c).xmm r) i)
  | none => none

/-- Read one 32-bit lane out of an adapter outcome. -/
def sseFourWitLane32 (o : Option HwMaschine) (c : Nat) (r : XmmReg)
    (i : Nat) : Option Nat :=
  match o with
  | some m => some (laneNat .b32 ((m.kerne c).xmm r) i)
  | none => none

/-- Core 0 sign extension: `0xFF` becomes 65535. -/
theorem sseFourWit_sx_lane0 :
    sseFourWitLane16 sseFourWitOut0 0 XmmReg.xmm0 0 = some 65535 := by
  decide

/-- Core 0 sign extension: `5` stays 5. -/
theorem sseFourWit_sx_lane1 :
    sseFourWitLane16 sseFourWitOut0 0 XmmReg.xmm0 1 = some 5 := by
  decide

/-- Core 1 multiply: `70000 * 70000` keeps the low 32 bits. -/
theorem sseFourWit_mul_lane0 :
    sseFourWitLane32 sseFourWitOut1 1 XmmReg.xmm2 0 = some 605032704 := by
  decide

/-- Witness data address. -/
def sseFourWitAdr : Adresse := BitVec.ofNat 64 12288

/-- Witness TSO start: canonical memory, empty buffers. -/
def sseFourWitTso0 : TSOZustand := ⟨zeugeSpeicher, fun _ => []⟩

/-- Core 0 issues byte 77 at the data cell. -/
def sseFourWitTso1 : Option TSOZustand :=
  issueByte sseFourWitTso0 0 sseFourWitAdr (BitVec.ofNat 8 77)

/-- Core 0 observes its own byte (forwarding). -/
def sseFourWitEigen : Option (Option Byte) :=
  match sseFourWitTso1 with
  | some s => some (loadByte s 0 sseFourWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def sseFourWitFremd : Option (Option Byte) :=
  match sseFourWitTso1 with
  | some s => some (loadByte s 1 sseFourWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def sseFourWitTso2 : Option TSOZustand :=
  match sseFourWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def sseFourWitNachFlush : Option (Option Byte) :=
  match sseFourWitTso2 with
  | some s => some (some (s.mem.bytes sseFourWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def sseFourWitFremdNach : Option (Option Byte) :=
  match sseFourWitTso2 with
  | some s => some (loadByte s 1 sseFourWitAdr)
  | none => none

/-- The data cell starts zeroed. -/
theorem sseFourWit_anfang_null :
    zeugeSpeicher.bytes sseFourWitAdr = BitVec.ofNat 8 0 := by
  rfl

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem sseFourWit_weiterleitung :
    sseFourWitEigen = some (some (BitVec.ofNat 8 77)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem sseFourWit_fremd_alt :
    sseFourWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 77. -/
theorem sseFourWit_spuelung_aendert_speicher :
    sseFourWitNachFlush = some (some (BitVec.ofNat 8 77)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem sseFourWit_fremd_neu :
    sseFourWitFremdNach = some (some (BitVec.ofNat 8 77)) := by
  decide

/-- A bad decode length refuses the adapter step beside the run. -/
theorem sseFourWit_schlechte_laenge_verweigert :
    (adapterSseFour).schritt sseFourWitStart 0
      (⟨.pmovsxbwRR .xmm0 .xmm1, 0⟩ : SseFourDec) = none :=
  adapterSseFour_verweigert_bei_laenge _ _ _ (by decide)

/-- The joint witness: a reached two-core family run (sign extension
    on core 0, multiply on core 1) beside a buffered store that only
    the owner forwards and a drain that changes actual shared memory
    from 0 to 77 -- with the refusal and decode refusals beside it.
    Non-degenerate: XMM lanes change and shared memory changes. -/
theorem sseFourWit_zeuge :
    sseFourWitLane16 sseFourWitOut0 0 XmmReg.xmm0 0 = some 65535 ∧
      sseFourWitLane16 sseFourWitOut0 0 XmmReg.xmm0 1 = some 5 ∧
      sseFourWitLane32 sseFourWitOut1 1 XmmReg.xmm2 0 = some 605032704 ∧
      sseFourWitEigen = some (some (BitVec.ofNat 8 77)) ∧
      sseFourWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      sseFourWitNachFlush = some (some (BitVec.ofNat 8 77)) ∧
      sseFourWitFremdNach = some (some (BitVec.ofNat 8 77)) ∧
      zeugeSpeicher.bytes sseFourWitAdr = BitVec.ofNat 8 0 ∧
      HwWf sseFourWitStart ∧
      (adapterSseFour).schritt sseFourWitStart 0
        (⟨.pmovsxbwRR .xmm0 .xmm1, 0⟩ : SseFourDec) = none ∧
      decodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
        natByte 0, natByte 200] = none ∧
      kapDecodeSseFour [natByte 64, natByte 102, natByte 15, natByte 56,
        natByte 0, natByte 200] = none := by
  refine ⟨sseFourWit_sx_lane0, sseFourWit_sx_lane1, sseFourWit_mul_lane0,
    sseFourWit_weiterleitung, sseFourWit_fremd_alt,
    sseFourWit_spuelung_aendert_speicher, sseFourWit_fremd_neu,
    sseFourWit_anfang_null, sseFourWitStart_wf,
    sseFourWit_schlechte_laenge_verweigert, sseFour_nichts_pshufb,
    kapSseFour_nichts_pshufb⟩

/- CUTS:
   Proved here: six admitted SSE4.1 register-direct XMM rows (PMOVSXBW
   `66 0F 38 20`, PMOVZXBW `66 0F 38 30`, PMINSD `66 0F 38 39`,
   PMAXSD `66 0F 38 3D`, PMULLD `66 0F 38 40`, PCMPEQQ `66 0F 38 29`)
   with canonical encoding, a canonical decoder, per-row round trips,
   planted decoder refusals, six decide-pins that the old capstone
   chain refuses the new bytes, semantics from the accepted lane
   vocabulary with per-lane equations and silicon spot-checks, a
   family step with frame theorems, the extended chain
   `kapDecodeSseFour` with exact agreement and extended-chain pins,
   the `HwAdapter SseFourDec` plug with well-formedness preservation
   and planted refusals, and a reached two-core run with owner-only
   forwarding and a memory-changing drain.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the canonical subset
     with self-consistency only, not x86 truth. Silicon assumptions
     named: the six opcode rows (SDM Vol. 2B), PMOVSX sign rule,
     PMIN/MAX signed comparison, PMULLD low-32-bit result, PCMPEQQ
     all-ones-on-equal, legacy-SSE whole-register XMM writes (upper
     YMM unmodified), no flag/memory/GPR effect. The map
     transcription is a NAMED assumption.
   - No SSE4.1 remainder (PBLENDW, BLENDPS/PD, BLENDVPS/PD/PBLENDVB,
     PTEST, ROUNDSS/SD/PS/PD, PINSRB/D/Q, PEXTRB/D/Q, INSERTPS,
     EXTRACTPS, DPPS/DPPD, MPSADBW, PHMINPOSUW, PACKUSDW), no SSE4.2
     (PCMPESTRI/PCMPESTRM/PCMPISTRI/PCMPISTRM with ECX/EAX, CRC32),
     no MMX (NP) forms, no memory ModRM forms, no REX.W forms, no
     other third byte in the `0F 38` escape, no `0F 3A` row here
     (PALIGNR/BLENDVPS pins beside the run).
   - No VEX/EVEX, no SIB/addressed operands, no LOCK path, no
     source/IR/ABI/loader/entry/budget link, no per-access
     target-to-W/GX simulation, no timing/power behaviour.
   - A maintainer wires the family in by adding the `decodeSseFour`
     arm behind every earlier arm of `HwKapsteinDecoder.kapDecode`.
   - File placement: the task fixes
     `grammatik/Grammatik/X86/SseFourOne.lean`, but
     `instrumente/lean-layout-rules.py` assigns `^Sse\w+$` to
     `Befehle/Sse`; a maintainer runs
     `python3 instrumente/lean-layout.py --apply` after integration.
-/

#print axioms encodeSseFour
#print axioms decodeSseFour
#print axioms roundtripSseFour
#print axioms vecPmovsxbw
#print axioms vecPmovzxbw
#print axioms vecPminsd
#print axioms vecPmaxsd
#print axioms vecPmulld
#print axioms vecPcmpeqq
#print axioms stepSseFour
#print axioms kapDecodeSseFour
#print axioms adapterSseFour
#print axioms adapterSseFour_wf
#print axioms sseFourWitStart_wf
#print axioms sseFourWit_zeuge

end Gabbro.Grammatik.X86
