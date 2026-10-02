/-
  File:      Grammatik/X86/ScalarFloatCodec.lean
  Subject:   Canonical scalar SSE2 DOUBLE bytes to accepted FP execution.

  Lane 565: byte connection for `ScalarFloat.fpSchritt`, beginning MOVSD
  (register, load, store) and one arithmetic register form (ADDSD). The
  canonical subset is stated from the Intel SDM opcode map (F2 prefix,
  0F escape, opcodes 10/11/58, ModRM mod=11 register / mod=10 disp32),
  exactly like BYTE-PILOT.md states the integer pilot: an implementation
  contract, never a hardware correspondence claim. The decoder parses
  actual bytes (prefix/opcode/ModRM/disp32) and never accepts a
  caller-supplied `FpDecodiert` as fetched evidence. Execution, upper-half
  and profile facts are derived from `fpSchritt`, never redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86

/-- Architectural XMM code: xmm0=0 through xmm15=15. The canonical subset
    below encodes the low eight only (no REX prefix); high registers are
    refused by absence (see CUTS). -/
def fpXmmCode : XmmReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

/-- Inverse check: low 3-bit code back to a low XMM register. -/
def codeXmmLow : Nat → Option XmmReg
  | 0 => some .xmm0 | 1 => some .xmm1 | 2 => some .xmm2 | 3 => some .xmm3
  | 4 => some .xmm4 | 5 => some .xmm5 | 6 => some .xmm6 | 7 => some .xmm7
  | _ => none

/-- Decoding inverts encoding on every low XMM register. -/
theorem codeXmmLow_xmmCode (r : XmmReg) (h : fpXmmCode r < 8) :
    codeXmmLow (fpXmmCode r) = some r := by
  cases r <;> simp_all [fpXmmCode, codeXmmLow] <;> omega

/-- Every XMM code fits in four bits. -/
theorem fpXmmCode_lt (r : XmmReg) : fpXmmCode r < 16 := by
  cases r <;> decide

/-! ## 1. Canonical byte encodings (stated from the Intel SDM opcode map).

  F2 prefix (242), 0F escape (15), then the opcode: 10 (16) for MOVSD
  load/register-copy, 11 (17) for MOVSD store, 58 (88) for ADDSD. ModRM
  mod=11 is register-direct (reg=destination, r/m=source, exactly the
  0F 10/58 convention); mod=10 is base-plus-disp32 with the pilot SIB
  rule (SIB 36 iff the low base code is 4). The encoder is total over
  `XmmReg`/`Register` via the low three code bits (like `modrmReg`'s
  `% 8`); only low operands are canonical -- high operands alias their
  low bits here and await the REX extension (see CUTS). -/

/-- Canonical MOVSD register-copy bytes: F2 0F 10 /r, mod=11. -/
def fpEncodeMovsdRR (dst src : XmmReg) : List Byte :=
  [natByte 242, natByte 15, natByte 16,
    modrmReg (fpXmmCode dst) (fpXmmCode src)]

/-- Canonical ADDSD register bytes: F2 0F 58 /r, mod=11. -/
def fpEncodeAddsdRR (dst src : XmmReg) : List Byte :=
  [natByte 242, natByte 15, natByte 88,
    modrmReg (fpXmmCode dst) (fpXmmCode src)]

/-- Canonical MOVSD load bytes: F2 0F 10 /r, mod=10, disp32. -/
def fpEncodeMovsdLade (dst : XmmReg) (base : Register) (d : BitVec 32) : List Byte :=
  let head := [natByte 242, natByte 15, natByte 16,
    modrmMem (fpXmmCode dst) (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Canonical MOVSD store bytes: F2 0F 11 /r, mod=10, disp32. -/
def fpEncodeMovsdSpeichere (base : Register) (src : XmmReg) (d : BitVec 32) : List Byte :=
  let head := [natByte 242, natByte 15, natByte 17,
    modrmMem (fpXmmCode src) (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-! ## 2. Independent decoder over actual bytes.

  The decoder reads the prefix, escape, opcode, ModRM and displacement
  from the byte list itself and rebuilds the register values and the
  consumed length from those bytes. A caller-supplied `FpDecodiert`
  never becomes fetched evidence: there is no decoder input of that
  type. Only the four §1 forms decode; every other opcode, ModRM mode,
  prefix (including F3/66/REX) or truncation refuses with `none`. -/

/-- Decode ModRM and the optional disp32 after the F2 0F opcode byte.
    Length 4 for register forms, 7/8 for memory forms; truncated
    inputs refuse. -/
def fpDecodeRest (op : Nat) : List Byte → Option (FpDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 =>
      match op, codeXmmLow reg, codeXmmLow rm with
      | 16, some dst, some src => some (⟨.movsdRR dst src, 4⟩, rest)
      | 88, some dst, some src => some (⟨.addsdRR dst src, 4⟩, rest)
      | _, _, _ => none
    | 2 =>
      if rm == 4 then
        match rest with
        | [] => none
        | sib :: rest2 =>
          if byteNat sib == 36 then
            match parseLe32 rest2 with
            | none => none
            | some (d, rest3) =>
              match op, codeXmmLow reg, codeReg rm with
              | 16, some dst, some base =>
                some (⟨.movsdLade dst base d, 9⟩, rest3)
              | 17, some src, some base =>
                some (⟨.movsdSpeichere base src d, 9⟩, rest3)
              | _, _, _ => none
          else none
      else
        match parseLe32 rest with
        | none => none
        | some (d, rest3) =>
          match op, codeXmmLow reg, codeReg rm with
          | 16, some dst, some base =>
            some (⟨.movsdLade dst base d, 8⟩, rest3)
          | 17, some src, some base =>
            some (⟨.movsdSpeichere base src d, 8⟩, rest3)
          | _, _, _ => none
    | _ => none

/-- Decode the first canonical scalar-SSE2 instruction, returning it
    with its consumed length and the remaining bytes. -/
def fpDecode : List Byte → Option (FpDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    if byteNat b == 242 then
      match rest with
      | [] => none
      | b2 :: rest2 =>
        if byteNat b2 == 15 then
          match rest2 with
          | [] => none
          | b3 :: rest3 => fpDecodeRest (byteNat b3) rest3
        else none
    else none

/-! ## 3. Encode/decode round trips over the canonical subset.

  Decoding inverts encoding on low operands over any suffix; the
  decoded length is the consumed prefix length. High operands are
  excluded by the `< 8` premises (the REX extension owns them). -/

/-- Encode/decode round trip for the MOVSD register copy. -/
theorem fpRoundtrip_movsdRR (dst src : XmmReg) (suffix : List Byte)
    (hd : fpXmmCode dst < 8) (hs : fpXmmCode src < 8) :
    fpDecode (fpEncodeMovsdRR dst src ++ suffix) =
      some (⟨.movsdRR dst src, (fpEncodeMovsdRR dst src).length⟩, suffix) := by
  cases dst <;> cases src <;>
    simp_all [fpEncodeMovsdRR, fpDecode, fpDecodeRest, codeXmmLow, fpXmmCode,
      modrmReg, natByte, byteNat]

/-- Encode/decode round trip for the ADDSD register form. -/
theorem fpRoundtrip_addsdRR (dst src : XmmReg) (suffix : List Byte)
    (hd : fpXmmCode dst < 8) (hs : fpXmmCode src < 8) :
    fpDecode (fpEncodeAddsdRR dst src ++ suffix) =
      some (⟨.addsdRR dst src, (fpEncodeAddsdRR dst src).length⟩, suffix) := by
  cases dst <;> cases src <;>
    simp_all [fpEncodeAddsdRR, fpDecode, fpDecodeRest, codeXmmLow, fpXmmCode,
      modrmReg, natByte, byteNat]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for the MOVSD load, both SIB shapes. -/
theorem fpRoundtrip_movsdLade (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte)
    (hd : fpXmmCode dst < 8) (hb : regCode base < 8) :
    fpDecode (fpEncodeMovsdLade dst base d ++ suffix) =
      some (⟨.movsdLade dst base d, (fpEncodeMovsdLade dst base d).length⟩,
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [fpEncodeMovsdLade, fpDecode, fpDecodeRest, codeXmmLow, codeReg,
      fpXmmCode, regCode, regLow, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for the MOVSD store, both SIB shapes. -/
theorem fpRoundtrip_movsdSpeichere (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte)
    (hb : regCode base < 8) (hs : fpXmmCode src < 8) :
    fpDecode (fpEncodeMovsdSpeichere base src d ++ suffix) =
      some (⟨.movsdSpeichere base src d,
        (fpEncodeMovsdSpeichere base src d).length⟩, suffix) := by
  cases base <;> cases src <;>
    simp_all [fpEncodeMovsdSpeichere, fpDecode, fpDecodeRest, codeXmmLow,
      codeReg, fpXmmCode, regCode, regLow, modrmMem, leBytes32, parseLe32_cons]

/-! ## 4. Decoder and admission refusals.

  A wrong prefix, a truncated byte list, an unadmitted opcode or ModRM
  mode, and a refused MXCSR word each refuse explicitly. The memory
  arithmetic opcode (58 with a memory ModRM) is refused although the
  matching `FpBefehl` exists in `fpSchritt`: the subset boundary is
  syntactic, pinned here rather than silently admitted. -/

/-- A wrong leading prefix (F3 instead of F2) refuses. -/
theorem fpDecode_falschesPraefix (suffix : List Byte) :
    fpDecode (natByte 243 :: natByte 15 :: natByte 16 ::
      modrmReg 0 1 :: suffix) = none := by
  simp [fpDecode]

/-- The UCOMISD prefix (66) is outside the subset and refuses. -/
theorem fpDecode_sechsundsechzig_verweigert (suffix : List Byte) :
    fpDecode (natByte 102 :: natByte 15 :: natByte 46 ::
      modrmReg 0 1 :: suffix) = none := by
  simp [fpDecode]

/-- A REX prefix byte is outside the subset and refuses (high XMM
    registers await the REX extension; see CUTS). -/
theorem fpDecode_rex_verweigert (suffix : List Byte) :
    fpDecode (natByte 65 :: natByte 15 :: natByte 16 ::
      modrmReg 0 1 :: suffix) = none := by
  simp [fpDecode]

/-- A lone F2 prefix (truncated before the escape) refuses. -/
theorem fpDecode_abgeschnitten_praefix :
    fpDecode [natByte 242] = none := by
  simp [fpDecode]

/-- F2 0F without opcode and ModRM refuses. -/
theorem fpDecode_abgeschnitten_opcode :
    fpDecode [natByte 242, natByte 15] = none := by
  simp [fpDecode]

/-- F2 0F 10 without ModRM refuses. -/
theorem fpDecode_abgeschnitten_modrm :
    fpDecode [natByte 242, natByte 15, natByte 16] = none := by
  simp [fpDecode, fpDecodeRest]

/-- A truncated displacement refuses: the first seven of eight MOVSD
    store bytes decode to nothing. -/
theorem fpDecode_abgeschnitten_disp :
    fpDecode ((fpEncodeMovsdSpeichere .rax .xmm0 0).take 7) = none := by
  decide

/-- ModRM mod=1 is non-canonical and refuses. -/
theorem fpDecode_modEins_verweigert (suffix : List Byte) :
    fpDecode (natByte 242 :: natByte 15 :: natByte 16 ::
      natByte 64 :: suffix) = none := by
  simp [fpDecode, fpDecodeRest]

/-- Opcode 11 with a register ModRM (the non-canonical MOVSD
    register-store encoding) refuses. -/
theorem fpDecode_speichereRegister_verweigert (suffix : List Byte) :
    fpDecode (natByte 242 :: natByte 15 :: natByte 17 ::
      modrmReg 0 1 :: suffix) = none := by
  simp [fpDecode, fpDecodeRest, modrmReg]

/-- Opcode 58 with a memory ModRM (memory ADDSD: modelled in
    `fpSchritt`, outside this byte subset) refuses. -/
theorem fpDecode_addsdSpeicher_verweigert (d : BitVec 32)
    (suffix : List Byte) :
    fpDecode (natByte 242 :: natByte 15 :: natByte 88 ::
      modrmMem 0 0 :: leBytes32 d ++ suffix) = none := by
  simp [fpDecode, fpDecodeRest, modrmMem, leBytes32, parseLe32_cons]

/-- A refused MXCSR word refuses every decoded scalar FP step: the
    admission check from `fpSchritt`, reached here through actual
    decoder output shape. -/
theorem fpCodec_profil_verweigert (t : FpZustand)
    (h : fpEintritt t.fp = false) :
    fpSchritt ⟨.movsdRR .xmm0 .xmm1, 4⟩ t = none := by
  exact fpSchritt_profil_verweigert _ t (by decide) h

/-! ## 5. Fetch from actual executable memory and byte step.

  Fetch reads the bytes at the core RIP from the state's ACTUAL memory
  (executable prefix only, capped at 15), exactly like `Byteschritt`,
  and decodes them with the independent §2 decoder. The decoded value
  is checked for length consistency, decode-length validity and execute
  permission before it reaches `fpSchritt`. -/

/-- The fetched window of an extended state: actual bytes at the core
    RIP, executable prefix only, capped at 15 (reuses `geholt`). -/
def fpGeholt (t : FpZustand) : List Byte := geholt t.kern

/-- Fetch and decode: decode the ACTUAL fetched bytes with the
    independent decoder, then check consumed-length/remaining-suffix
    consistency, decode-length validity and execute permission of the
    consumed prefix. -/
def fpFetchDekodiert (t : FpZustand) : Option (FpDecodiert × List Byte) :=
  match fpDecode (fpGeholt t) with
  | none => none
  | some (d, rest) =>
    if d.laenge + rest.length == (fpGeholt t).length &&
        laengeOk d.laenge && ausfuehrbarN t.kern.speicher t.kern.rip d.laenge
    then some (d, rest)
    else none

/-- Byte-step outcome over the extended state. -/
inductive FpByteAusgang where
  | weiter : FpZustand → FpByteAusgang
  | verweigert : FpByteAusgang

/-- One byte step from actual memory: fetch, decode, then the existing
    `fpSchritt`. Takes ONLY the state: no caller-supplied `FpDecodiert`
    ever becomes a trusted fetch, so a forged decoded value cannot
    inject an instruction. -/
def fpByteschritt (t : FpZustand) : FpByteAusgang :=
  match fpFetchDekodiert t with
  | none => .verweigert
  | some (d, _) =>
    match fpSchritt d t with
    | none => .verweigert
    | some t' => .weiter t'

/-- Fetch success pins the decoder equation and every guard: length
    consistency, decode-length validity and execute permission. -/
theorem fpFetchDekodiert_erfolg (t : FpZustand) (d : FpDecodiert)
    (rest : List Byte) (h : fpFetchDekodiert t = some (d, rest)) :
    fpDecode (fpGeholt t) = some (d, rest) ∧
      d.laenge + rest.length = (fpGeholt t).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip d.laenge = true := by
  unfold fpFetchDekodiert at h
  cases hd : fpDecode (fpGeholt t) with
  | none =>
    rw [hd] at h
    simp at h
  | some q =>
    obtain ⟨d', rest'⟩ := q
    rw [hd] at h
    simp only at h
    by_cases hc : (d'.laenge + rest'.length == (fpGeholt t).length &&
        laengeOk d'.laenge && ausfuehrbarN t.kern.speicher t.kern.rip d'.laenge)
    · rw [if_pos hc] at h
      obtain ⟨rfl, rfl⟩ := Option.some_inj.mp h
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, hc.1.1, hc.1.2, hc.2⟩
    · rw [if_neg hc] at h
      simp at h

/-- A refused MXCSR word refuses the byte step on every state: fetch
    may succeed, but the accepted `fpSchritt` admission refuses. -/
theorem fpByteschritt_profil_verweigert (t : FpZustand)
    (h : fpEintritt t.fp = false) :
    fpByteschritt t = .verweigert := by
  unfold fpByteschritt
  cases hf : fpFetchDekodiert t with
  | none => rfl
  | some q =>
    obtain ⟨d, rest⟩ := q
    have hok := (fpFetchDekodiert_erfolg t d rest hf).2.2.1
    have hstep : fpSchritt d t = none :=
      fpSchritt_profil_verweigert d t hok h
    simp [hstep]

/-! ## 6. Execution from fetched bytes, derived from `fpSchritt`.

  Nothing is redefined here: each theorem runs the accepted `fpSchritt`
  equation for the fetched form and projects one fact out of it. The
  fetch equation travels as an explicit premise, so every conclusion is
  reached from bytes in actual memory, never from a caller-supplied
  `FpDecodiert`. -/

/-- A successful fetched byte-step runs the accepted `fpSchritt` on
    the fetched form. -/
theorem fpByteschritt_schritt (t t' : FpZustand) (d : FpDecodiert)
    (rest : List Byte)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hout : fpByteschritt t = .weiter t') :
    fpSchritt d t = some t' := by
  unfold fpByteschritt at hout
  rw [hf] at hout
  simp only at hout
  cases hs : fpSchritt d t with
  | none => simp [hs] at hout
  | some u =>
    simp [hs] at hout
    rw [hout]

/-- A fetched ADDSD byte-step computes the model sum into the low half. -/
theorem fpByteschritt_addsdRR_rechnet (t t' : FpZustand) (d : FpDecodiert)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .addsdRR dst src)
    (hfp : fpEintritt t.fp = true)
    (hout : fpByteschritt t = .weiter t') :
    xmmTief t'.xmm dst =
      fpRechne .add (xmmTief t.xmm dst) (xmmTief t.xmm src) := by
  have hok := (fpFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpByteschritt_schritt t t' d rest hf hout
  have heq := fpSchritt_addsdRR d t dst src hok hfp hform
  rw [hstep] at heq
  obtain rfl := Option.some_inj.mp heq
  exact xmmSchreibeTief_tief _ _ _

/-- A fetched ADDSD byte-step agrees with the source model op at the
    class level: NaN payloads are never concluded (the preserved cut
    of `Gleitprofil` §7 and `ScalarFloat` §4). -/
theorem fpByteschritt_addsdRR_klasse (t t' : FpZustand) (d : FpDecodiert)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .addsdRR dst src)
    (hfp : fpEintritt t.fp = true)
    (hout : fpByteschritt t = .weiter t') :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 (xmmTief t'.xmm dst)) =
      Gleitkomma.klasse Gleitkomma.f64
        (Gabbro.Grammatik.gleitRechne .add
          (bites64 (xmmTief t.xmm dst)) (bites64 (xmmTief t.xmm src))) := by
  have hrech := fpByteschritt_addsdRR_rechnet t t' d dst src rest hf hform hfp hout
  rw [hrech]
  exact fpRechne_klasse .add _ _

/-- A fetched ADDSD byte-step keeps the destination upper half
    (legacy SSE preserve semantics, from `fpSchritt`). -/
theorem fpByteschritt_addsdRR_hoch (t t' : FpZustand) (d : FpDecodiert)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .addsdRR dst src)
    (hfp : fpEintritt t.fp = true)
    (hout : fpByteschritt t = .weiter t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  have hok := (fpFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpByteschritt_schritt t t' d rest hf hout
  exact fpSchritt_addsdRR_hoch d t t' dst src hok hfp hform hstep

/-- A fetched MOVSD register copy preserves the pilot flags. -/
theorem fpByteschritt_movsdRR_flags (t t' : FpZustand) (d : FpDecodiert)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .movsdRR dst src)
    (hfp : fpEintritt t.fp = true)
    (hout : fpByteschritt t = .weiter t') :
    t'.kern.flags = t.kern.flags := by
  have hok := (fpFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpByteschritt_schritt t t' d rest hf hout
  exact fpSchritt_movsdRR_flags d t t' dst src hok hfp hform hstep

/-- A fetched MOVSD register copy keeps the FP control word: the
    profile admission is preserved by the step, never consumed. -/
theorem fpByteschritt_movsdRR_fp (t t' : FpZustand) (d : FpDecodiert)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .movsdRR dst src)
    (hfp : fpEintritt t.fp = true)
    (hout : fpByteschritt t = .weiter t') :
    t'.fp = t.fp := by
  have hok := (fpFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpByteschritt_schritt t t' d rest hf hout
  have heq := fpSchritt_movsdRR d t dst src hok hfp hform
  rw [hstep] at heq
  obtain rfl := Option.some_inj.mp heq
  rfl

/-- A fetched MOVSD register copy keeps every GPR: FP moves do not
    disturb the shared pilot register file of the extended state. -/
theorem fpByteschritt_movsdRR_gpr (t t' : FpZustand) (d : FpDecodiert)
    (dst src : XmmReg) (rest : List Byte) (q : Register)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .movsdRR dst src)
    (hfp : fpEintritt t.fp = true)
    (hout : fpByteschritt t = .weiter t') :
    t'.kern.register q = t.kern.register q := by
  have hok := (fpFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpByteschritt_schritt t t' d rest hf hout
  have heq := fpSchritt_movsdRR d t dst src hok hfp hform
  rw [hstep] at heq
  obtain rfl := Option.some_inj.mp heq
  rfl

/-! ## 7. Joint witness: a MOVSD store reached from actual bytes.

  The witness state carries the canonical store bytes at its RIP in
  executable memory; `xmm0` holds `+∞`. The fetched byte-step stores
  `+∞` at `[rax]`: the word reads back and one memory byte observably
  changed, under the admitted profile throughout. -/

/-- Witness instruction bytes: MOVSD `[rax+0]`, xmm0 (8 bytes). -/
def fpCodecInstr : List Byte := fpEncodeMovsdSpeichere .rax .xmm0 0

/-- The witness instruction is eight bytes long. -/
theorem fpCodecInstr_laenge : fpCodecInstr.length = 8 := by
  decide

/-- Witness memory: zeroed bytes with the store bytes at 4096 and
    execute permission exactly on those eight bytes; data access stays
    fully open. -/
def fpCodecSpeicher : Speicher :=
  { zeugenSpeicher with
    bytes := fun a =>
      if a.toNat - 4096 < fpCodecInstr.length then fpCodecInstr.getD (a.toNat - 4096) 0
      else zeugenSpeicher.bytes a
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4104) }

/-- Witness XMM file: `xmm0` holds `+∞`, every other register `+0.0`. -/
def fpCodecXmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 then vecJoin 0x7FF0000000000000 0 else vecJoin 0 0

/-- Witness core: `rax` points at 8192, RIP at the store bytes. -/
def fpCodecKern : Zustand :=
  { register := fun q => if q = Register.rax then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0
    flags := ⟨false, true, some false, false, false, false⟩
    rip := BitVec.ofNat 64 4096
    speicher := fpCodecSpeicher }

/-- Witness extended state: reset FP control word (admitted profile). -/
def fpCodecT : FpZustand := ⟨fpCodecKern, fpCodecXmm, kontextReset⟩

/-- The witness `xmm0` holds `+∞`. -/
theorem fpCodecTief0 :
    xmmTief fpCodecT.xmm XmmReg.xmm0 = 0x7FF0000000000000 := by
  decide

/-- The witness store address: `rax + 0` is 8192. -/
theorem fpCodecEffAddr :
    effAddr fpCodecT.kern Register.rax 0 = BitVec.ofNat 64 8192 := by
  decide

/-- Admitted profile on the witness state. -/
theorem fpCodecFp : fpEintritt fpCodecT.fp = true := by
  decide

/-- The fetch window holds exactly the store bytes. -/
theorem fpCodecGeholt : fpGeholt fpCodecT = fpCodecInstr := by
  decide

/-- The eight store bytes carry execute permission. -/
theorem fpCodecPerm :
    ausfuehrbarN fpCodecT.kern.speicher fpCodecT.kern.rip 8 = true := by
  decide

/-- Witness memory after the store: `+∞` at 8192. -/
def fpCodecSpeicherNach : Speicher :=
  { fpCodecSpeicher with bytes := writeBytes fpCodecSpeicher (BitVec.ofNat 64 8192) 0x7FF0000000000000 }

/-- Witness state after the store. -/
def fpCodecT2 : FpZustand :=
  { fpCodecT with kern := { fpCodecT.kern with speicher := fpCodecSpeicherNach, rip := ripNach fpCodecT.kern.rip 8 } }

/-- The encoded store is eight bytes long. -/
theorem fpCodecSpeichere_laenge :
    (fpEncodeMovsdSpeichere .rax .xmm0 0).length = 8 := by
  decide

/-- Eight bytes decode with a checked length. -/
theorem fpCodecLaengeOk : laengeOk 8 = true := by
  decide

/-- Fetch from the actual store bytes yields the store form. -/
theorem fpCodec_fetch :
    fpFetchDekodiert fpCodecT = some (⟨.movsdSpeichere .rax .xmm0 0, 8⟩, []) := by
  have hbytes : fpGeholt fpCodecT = fpEncodeMovsdSpeichere .rax .xmm0 0 ++ [] := by
    simp only [fpCodecGeholt, fpCodecInstr, List.append_nil]
  have hrt := fpRoundtrip_movsdSpeichere .rax .xmm0 0 [] (by decide) (by decide)
  rw [fpCodecSpeichere_laenge] at hrt
  have hdec : fpDecode (fpGeholt fpCodecT) =
      some (⟨.movsdSpeichere .rax .xmm0 0, 8⟩, []) := by
    rw [hbytes]
    exact hrt
  have hlen : (fpGeholt fpCodecT).length = 8 := by
    have h8 := fpCodecSpeichere_laenge
    rw [hbytes, List.length_append, List.length_nil, Nat.add_zero]
    exact h8
  have hperm : ausfuehrbarN fpCodecT.kern.speicher fpCodecT.kern.rip 8 = true :=
    fpCodecPerm
  unfold fpFetchDekodiert
  rw [hdec]
  simp only
  rw [hlen, fpCodecLaengeOk, hperm]
  decide

/-- The store goes through: `+∞` lands at 8192. -/
theorem fpCodec_schreib :
    write64 fpCodecT.kern.speicher (effAddr fpCodecT.kern Register.rax 0)
      (xmmTief fpCodecT.xmm XmmReg.xmm0) = some fpCodecSpeicherNach := by
  rw [fpCodecEffAddr, fpCodecTief0]
  have hc : schreibbar8 fpCodecT.kern.speicher (BitVec.ofNat 64 8192) = true := by
    decide
  unfold write64
  rw [if_pos hc]
  rfl

/-- The reached byte-step: actual bytes store `xmm0` to `[rax]`. -/
theorem fpCodec_schritt :
    fpByteschritt fpCodecT = .weiter fpCodecT2 := by
  unfold fpByteschritt
  rw [fpCodec_fetch]
  simp only
  have hs := fpSchritt_movsdSpeichere_erfolg ⟨.movsdSpeichere .rax .xmm0 0, 8⟩
    fpCodecT .rax .xmm0 0 fpCodecSpeicherNach
    fpCodecLaengeOk fpCodecFp rfl fpCodec_schreib
  simp only [hs, fpCodecT2]

/-- The stored word reads back: `+∞` at 8192. -/
theorem fpCodec_liest :
    read64 fpCodecT2.kern.speicher (BitVec.ofNat 64 8192) =
      some 0x7FF0000000000000 := by
  have hwr : write64 fpCodecT.kern.speicher (BitVec.ofNat 64 8192)
      0x7FF0000000000000 = some fpCodecSpeicherNach := by
    have h := fpCodec_schreib
    rw [fpCodecEffAddr, fpCodecTief0] at h
    exact h
  have hrd : lesbar8 fpCodecT.kern.speicher (BitVec.ofNat 64 8192) = true := by
    decide
  exact read64_nach_write64 _ _ _ _ hwr hrd

/-- The store observably changed memory (top footprint byte). -/
theorem fpCodec_aendert :
    fpCodecT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
      fpCodecT2.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  decide

/-- Joint witness: actual store bytes fetched, decoded and executed to
    a real memory change -- one reached byte-step under the admitted
    profile, with the word reading back. -/
theorem fpCodec_bytes_zeuge :
    ∃ (t' : FpZustand),
      fpByteschritt fpCodecT = .weiter t' ∧
      read64 t'.kern.speicher (BitVec.ofNat 64 8192) = some 0x7FF0000000000000 ∧
      fpCodecT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
        t'.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ∧
      fpEintritt fpCodecT.fp = true :=
  ⟨fpCodecT2, fpCodec_schritt, fpCodec_liest, fpCodec_aendert, fpCodecFp⟩

/- CUTS: what is not proved here.

   Shared embedding (how the one target semantics grows, not a second
   evaluator): the canonical pilot `Zustand` lives on as
   `FpZustand.kern`. Pilot steps run through `laufAlt`, which keeps
   every XMM register and the MXCSR word untouched (proved in
   `ScalarFloat`: `laufAlt_xmm`, `laufAlt_fp`, `laufAlt_kern`). Scalar
   FP steps run through `fpSchritt` on the same extended state; the
   §6 lemmas pin the non-interference in the FP direction (register
   moves keep the pilot GPR file, flags and control word). No
   interleaving, TSO or concurrency claim is made: everything here is
   sequential over one `Speicher`.
   - Canonical subset only: MOVSD register/load/store and ADDSD
     register, low XMM0-7 and low GPR bases, no REX prefix. The encoder
     is total via the low three code bits, so high operands alias
     their low bits in the ENCODER; the DECODER only ever yields low
     operands, and REX prefix bytes are refused outright. The REX
     extension (high XMM/GPR reachability from bytes) is OPEN.
   - Modelled-but-undecodable: memory arithmetic (ADDSD/SUBSD/MULSD/
     DIVSD with memory ModRM -- pinned refusal for ADDSD), UCOMISD
     (66 prefix refused), CVTSI2SD/CVTTSD2SI, and the non-canonical
     MOVSD register-store encoding (opcode 11 with mod=3, refused).
     x87, FMA, packed/AVX/VEX/EVEX and short/displaced ModRM modes
     (mod=0/1) have no decoder path: syntactically absent, refused.
   - NaN relation is class-level only (`fpByteschritt_addsdRR_klasse`
     via `fpRechne_klasse`): payload equality of computed results is
     never concluded. SNaN trapping/quieting and sticky MXCSR flags
     stay unmodelled (inherited cuts of `Gleitprofil` §7 and
     `ScalarFloat` §6).
   - No hardware correspondence: the byte shapes (F2 prefix, 0F
     escape, opcodes 10/11/58, ModRM mod=11/10 with the pilot SIB
     rule) are STATED from the Intel SDM opcode map as an
     implementation contract in the style of BYTE-PILOT.md, never
     verified against silicon. Encoder round-trip consistency is not
     hardware correspondence.
   - No source-level bridge beyond reuse: the model-op link
     (`fpRechne` IS `gleitRechne` at binary64) is proved in
     `ScalarFloat` §4 and consumed here, never restated; no new claim
     about source `Ty.fl` programs, checking, or emission is made.
   - The `decide` proofs are closed concrete evaluations over
     kernel-computable definitions (never `native_decide`).
-/

#print axioms codeXmmLow_xmmCode
#print axioms fpXmmCode_lt
#print axioms fpRoundtrip_movsdRR
#print axioms fpRoundtrip_addsdRR
#print axioms fpRoundtrip_movsdLade
#print axioms fpRoundtrip_movsdSpeichere
#print axioms fpDecode_falschesPraefix
#print axioms fpDecode_sechsundsechzig_verweigert
#print axioms fpDecode_rex_verweigert
#print axioms fpDecode_abgeschnitten_praefix
#print axioms fpDecode_abgeschnitten_opcode
#print axioms fpDecode_abgeschnitten_modrm
#print axioms fpDecode_abgeschnitten_disp
#print axioms fpDecode_modEins_verweigert
#print axioms fpDecode_speichereRegister_verweigert
#print axioms fpDecode_addsdSpeicher_verweigert
#print axioms fpCodec_profil_verweigert
#print axioms fpFetchDekodiert_erfolg
#print axioms fpByteschritt_profil_verweigert
#print axioms fpByteschritt_schritt
#print axioms fpByteschritt_addsdRR_rechnet
#print axioms fpByteschritt_addsdRR_klasse
#print axioms fpByteschritt_addsdRR_hoch
#print axioms fpByteschritt_movsdRR_flags
#print axioms fpByteschritt_movsdRR_fp
#print axioms fpByteschritt_movsdRR_gpr
#print axioms fpCodecInstr_laenge
#print axioms fpCodecTief0
#print axioms fpCodecEffAddr
#print axioms fpCodecFp
#print axioms fpCodecGeholt
#print axioms fpCodecLaengeOk
#print axioms fpCodecPerm
#print axioms fpCodecSpeichere_laenge
#print axioms fpCodec_fetch
#print axioms fpCodec_schreib
#print axioms fpCodec_schritt
#print axioms fpCodec_liest
#print axioms fpCodec_aendert
#print axioms fpCodec_bytes_zeuge

end Gabbro.Grammatik.X86
