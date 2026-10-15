/-
  File:      Grammatik/X86/VectorCodec.lean
  Subject:   Canonical SSE2 bytes for PXOR / PADDQ over the accepted
    packed-integer Vektor operations and the ScalarFloat XMM state.

  Lane 597 (connection wave): connects the accepted `Vektor.lean` lane
  functions (`vecXor`/`vecAdd` at `.b64`, `laneGet_add`/`laneGet_xor`
  per-lane facts) to actual canonical SSE2 byte decode and the SAME
  `ScalarFloat.lean` XMM register state (`XmmReg`/`XmmDatei`/
  `FpZustand`, `xmmSet`, `vLo`/`vHi`). Two register forms only:
  PXOR (`66 0F EF /r`) and PADDQ (`66 0F D4 /r`), each with a
  canonical REX prefix. New forms extend existing semantics and never
  re-evaluate pilot/FP forms. No vector atomicity, no hardware claim.
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.FeatureProfile
import Grammatik.X86.Codec

namespace Gabbro.Grammatik.X86

/-- Architectural XMM code: xmm0=0 through xmm15=15. -/
def xmmCode : XmmReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

/-- Inverse check: 4-bit code back to an XMM register. -/
def codeXmm : Nat → Option XmmReg
  | 0 => some .xmm0 | 1 => some .xmm1 | 2 => some .xmm2
  | 3 => some .xmm3 | 4 => some .xmm4 | 5 => some .xmm5
  | 6 => some .xmm6 | 7 => some .xmm7 | 8 => some .xmm8
  | 9 => some .xmm9 | 10 => some .xmm10 | 11 => some .xmm11
  | 12 => some .xmm12 | 13 => some .xmm13 | 14 => some .xmm14
  | 15 => some .xmm15
  | _ => none

/-- Decoding inverts encoding on every XMM register. -/
theorem codeXmm_xmmCode (r : XmmReg) : codeXmm (xmmCode r) = some r := by
  cases r <;> rfl

/-- Every XMM code fits in four bits. -/
theorem xmmCode_lt (r : XmmReg) : xmmCode r < 16 := by
  cases r <;> decide

/-- High bit of an XMM code (REX.R/REX.B extension). -/
def xmmHigh (r : XmmReg) : Nat := xmmCode r / 8

/-- Low three bits of an XMM code (ModRM field). -/
def xmmLow (r : XmmReg) : Nat := xmmCode r % 8

/-! ## 1. Covered packed-integer register forms and canonical bytes.

  PXOR is the full 128-bit xor; PADDQ adds the two 64-bit lanes
  (`vecAdd .b64`, modular per lane, no inter-lane carry). Both reuse
  the accepted `Vektor.lean` lane functions, never a new evaluator.
  Canonical bytes: REX (`64 + 4*R + B`, W=0/X=0, always emitted so
  the low/high halves are uniform), `66`, `0F`, opcode (`EF` PXOR /
  `D4` PADDQ), ModRM register-direct (mod=3, reg=dst, r/m=src). -/

/-- The two covered packed-integer register forms. -/
inductive VectorOp where
  | pxorRR (dst src : XmmReg)
  | paddqRR (dst src : XmmReg)
  deriving DecidableEq, Repr

/-- Second opcode byte: `EF` (239) is PXOR, `D4` (212) is PADDQ. -/
def vectorSecond : VectorOp → Nat
  | .pxorRR _ _ => 239
  | .paddqRR _ _ => 212

/-- Canonical REX byte for one vector form (W=0, X=0). -/
def vectorRex : VectorOp → Byte
  | .pxorRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)
  | .paddqRR dst src => natByte (64 + 4 * xmmHigh dst + xmmHigh src)

/-- Canonical byte encoding of one covered vector form (5 bytes). -/
def encodeVector : VectorOp → List Byte
  | op@(.pxorRR dst src) =>
    [vectorRex op, natByte 102, natByte 15, natByte (vectorSecond op),
      modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.paddqRR dst src) =>
    [vectorRex op, natByte 102, natByte 15, natByte (vectorSecond op),
      modrmReg (xmmLow dst) (xmmLow src)]

/-- Every canonical vector encoding is 5 bytes long. -/
theorem encodeVector_len (op : VectorOp) :
    (encodeVector op).length = 5 := by
  cases op with
  | pxorRR dst src => rfl
  | paddqRR dst src => rfl

/-- The vector length passes the decode-length guard. -/
theorem vectorLen_ok (op : VectorOp) :
    laengeOk (encodeVector op).length = true := by
  rw [encodeVector_len op]
  decide

/-! ## 2. Canonical decoder.

  The decoder parses bytes, never encode-equality. Only the canonical
  REX prefix (`64 + 4*R + B`: W=0, X=0), then `66`, `0F`, the opcode
  byte (`EF` PXOR / `D4` PADDQ) and a register-direct ModRM (mod=3,
  reg=dst, r/m=src). Anything else refuses with `none`. -/

/-- A decoded vector instruction: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure VectorDec where
  op : VectorOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- Decode one register-direct ModRM byte after the admitted prefix
    and opcode: mod must be 3, the reg field names the destination
    (REX.R extension), the r/m field the source (REX.B extension). -/
def decodeVectorModrm (rBit bBit opByte : Nat) :
    List Byte → Option (VectorOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src =>
        match opByte with
        | 239 => some ((.pxorRR dst src), rest)
        | 212 => some ((.paddqRR dst src), rest)
        | _ => none
      | _, _ => none
    else none

/-- Decode after the canonical REX prefix: `66`, then the `0F`
    escape, then the opcode byte, then ModRM. -/
def decodeVectorNach (rBit bBit : Nat) :
    List Byte → Option (VectorOp × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 102 then
      match rest with
      | [] => none
      | p2 :: rest2 =>
        if byteNat p2 == 15 then
          match rest2 with
          | [] => none
          | op :: rest3 => decodeVectorModrm rBit bBit (byteNat op) rest3
        else none
    else none

/-- Top-level vector decode: the REX prefix selects the extension
    bits; anything without a canonical REX refuses. -/
def decodeVector : List Byte → Option (VectorDec × List Byte)
  | [] => none
  | r :: tail =>
    match byteNat r with
    | 64 =>
      match decodeVectorNach 0 0 tail with
      | some (op, rest) => some (⟨op, 5⟩, rest)
      | none => none
    | 65 =>
      match decodeVectorNach 0 1 tail with
      | some (op, rest) => some (⟨op, 5⟩, rest)
      | none => none
    | 68 =>
      match decodeVectorNach 1 0 tail with
      | some (op, rest) => some (⟨op, 5⟩, rest)
      | none => none
    | 69 =>
      match decodeVectorNach 1 1 tail with
      | some (op, rest) => some (⟨op, 5⟩, rest)
      | none => none
    | _ => none

/-- Round trip for PXOR, over any suffix. -/
theorem roundtrip_pxor (dst src : XmmReg) (suffix : List Byte) :
    decodeVector (encodeVector (.pxorRR dst src) ++ suffix) =
      some ((⟨.pxorRR dst src, 5⟩ : VectorDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PADDQ, over any suffix. -/
theorem roundtrip_paddq (dst src : XmmReg) (suffix : List Byte) :
    decodeVector (encodeVector (.paddqRR dst src) ++ suffix) =
      some ((⟨.paddqRR dst src, 5⟩ : VectorDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Decoding inverts encoding on every covered row, over any suffix.
    The decoded length is the consumed prefix length. -/
theorem roundtripVector (op : VectorOp) (suffix : List Byte) :
    decodeVector (encodeVector op ++ suffix) =
      some ((⟨op, (encodeVector op).length⟩ : VectorDec), suffix) := by
  cases op with
  | pxorRR dst src =>
    rw [encodeVector_len]
    exact roundtrip_pxor dst src suffix
  | paddqRR dst src =>
    rw [encodeVector_len]
    exact roundtrip_paddq dst src suffix

/-! ## 3. Pilot disjointness and the combined dispatcher.

  The pilot decoder refuses every covered vector encoding, over any
  suffix: the second byte is `66` (102), which no pilot REX/push/pop
  arm accepts, and the bare `64`/`68`/`69` first bytes match no pilot
  arm at all. Dispatch stays canonical-first: the pilot decides every
  byte string it accepts, the vector extension only where it refuses. -/

/-- DISJOINTNESS: the pilot decoder refuses every covered vector
    encoding, over any suffix. -/
theorem vector_pilot_verweigert (op : VectorOp) (suffix : List Byte) :
    decode (encodeVector op ++ suffix) = none := by
  cases op with
  | pxorRR dst src => cases dst <;> cases src <;> rfl
  | paddqRR dst src => cases dst <;> cases src <;> rfl

/-- Combined decode: the pilot first, the vector extension only where
    the pilot refuses. No pilot form is shadowed and no pilot byte
    string is re-decided. -/
def decodeComboV (bs : List Byte) :
    Option ((Decodiert ⊕ VectorDec) × List Byte) :=
  match decode bs with
  | some (d, rest) => some (.inl d, rest)
  | none =>
    match decodeVector bs with
    | some (n, rest) => some (.inr n, rest)
    | none => none

/-- The combined decoder agrees with the pilot on every byte string
    the pilot accepts: no existing form is shadowed. -/
theorem decodeComboV_kanonisch (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    decodeComboV bs = some (.inl d, rest) := by
  unfold decodeComboV
  rw [h]

/-- Where the pilot refuses, a covered vector row is taken. -/
theorem decodeComboV_erweitert (bs : List Byte) (n : VectorDec)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeVector bs = some (n, rest)) :
    decodeComboV bs = some (.inr n, rest) := by
  unfold decodeComboV
  rw [h1, h2]

/-- Where both refuse, the combined decoder refuses. -/
theorem decodeComboV_nichts (bs : List Byte) (h1 : decode bs = none)
    (h2 : decodeVector bs = none) :
    decodeComboV bs = none := by
  unfold decodeComboV
  rw [h1, h2]

/-- A bare `0F` escape without the REX/`66` prefix is refused: the
    vector decoder never re-decides a pilot `0F` conditional jump. -/
theorem vector_nichts_bare0F :
    decodeVector [natByte 15, natByte 131, natByte 0, natByte 0,
      natByte 0, natByte 0] = none := rfl

/-- A memory ModRM (mod≠3) is refused: only register forms are covered. -/
theorem vector_nichts_speicher_modrm (dst src : XmmReg) :
    decodeVector ([vectorRex (.pxorRR dst src), natByte 102, natByte 15,
      natByte 239, natByte 8]) = none := by
  cases dst <;> cases src <;> rfl

/-- A truncated prefix (REX + `66` only) is refused. -/
theorem vector_nichts_kurz :
    decodeVector [natByte 64, natByte 102] = none := rfl

/-! ## 4. Vector step semantics on the shared XMM state.

  `stepVector` steps ONLY the §1 forms on the SAME `FpZustand` the
  scalar FP steps use (`ScalarFloat.lean`: `xmmSet` writes the whole
  128-bit register, `ripNach` advances RIP). Guards, in order: decode
  length (`laengeOk`, checked data), profile admission (`vecEintritt`,
  validator refusal), then the form. PXOR writes the accepted
  `vecXor .b64` word; PADDQ the accepted `vecAdd .b64` word (modular
  per 64-bit lane, no inter-lane carry, by `laneGet_add`). Flags,
  memory, GPRs and every other XMM register are untouched. -/

/-- Profile admission at OS vector state: the checked `osXmm`
    readiness of the `paketInt128` tier (`FeatureProfile.lean`).
    `false` is a VALIDATOR refusal (the image is not admitted without
    OS vector state), never a hardware fault. -/
def vecEintritt (b : BereitProfil) : Bool := b.osXmm

/-- Admission agrees with the finite profile: the covered rows are
    admitted exactly where `paketInt128` is admitted. -/
theorem vecEintritt_merkmal (hw : HwProfil) (b : BereitProfil)
    (h : hat hw .paketInt128 = true) :
    vecEintritt b = merkmalZugelassen hw b .paketInt128 := by
  unfold vecEintritt merkmalZugelassen
  simp only [hat, bereit] at h ⊢
  rw [h]
  cases b.osXmm <;> rfl

/-- Single vector step; `none` is an explicit refusal (bad length or
    refused OS vector state). -/
def stepVector (d : VectorDec) (t : FpZustand) (b : BereitProfil) :
    Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match vecEintritt b with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.op with
      | .pxorRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecXor .b64 (t.xmm dst) (t.xmm src)) }
      | .paddqRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecAdd .b64 (t.xmm dst) (t.xmm src)) }

/-- A bad decode length refuses every vector form. -/
theorem stepVector_laenge_verweigert (d : VectorDec) (t : FpZustand)
    (b : BereitProfil)
    (h : laengeOk d.laenge = false) : stepVector d t b = none := by
  unfold stepVector
  simp [h]

/-- Refused OS vector state refuses every vector form (validator
    admission, not a hardware fault). -/
theorem stepVector_profil_verweigert (d : VectorDec) (t : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (h : vecEintritt b = false) :
    stepVector d t b = none := by
  unfold stepVector
  simp [hok, h]

/-- `pxor`: the destination holds the accepted lane-xor word. -/
theorem stepVector_pxor (d : VectorDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .pxorRR dst src) :
    stepVector d t b =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecXor .b64 (t.xmm dst) (t.xmm src)) } := by
  unfold stepVector
  simp [hok, hfp, h]

/-- `paddq`: the destination holds the accepted lane-add word. -/
theorem stepVector_paddq (d : VectorDec) (t : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : vecEintritt b = true)
    (h : d.op = .paddqRR dst src) :
    stepVector d t b =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecAdd .b64 (t.xmm dst) (t.xmm src)) } := by
  unfold stepVector
  simp [hok, hfp, h]

/-! ## 5. Step frames: flags, memory, GPRs, other registers, lanes.

  Both forms preserve rFLAGS, change no memory byte, keep every GPR,
  keep every other XMM register whole, and advance RIP past the
  decoded length. Per-lane correctness reuses the accepted
  `laneGet_xor`/`laneGet_add`: no inter-lane carry, modular at 64
  bits, no float reassociation (no FP operation is involved). -/

/-- Every vector step advances RIP past the decoded length. -/
theorem stepVector_rip (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (hstep : stepVector d t b = some t') :
    t'.kern.rip = ripNach t.kern.rip d.laenge := by
  revert hstep
  unfold stepVector
  rw [hok, hfp]
  cases hop : d.op with
  | pxorRR dst src => intro hstep; cases hstep; rfl
  | paddqRR dst src => intro hstep; cases hstep; rfl

/-- `pxor` preserves the flags. -/
theorem stepVector_pxor_flags (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .pxorRR dst src) (hstep : stepVector d t b = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [stepVector_pxor d t b dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `pxor` changes no memory byte. -/
theorem stepVector_pxor_speicher (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .pxorRR dst src) (hstep : stepVector d t b = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [stepVector_pxor d t b dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `pxor` keeps every GPR. -/
theorem stepVector_pxor_gpr (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (q : Register)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .pxorRR dst src) (hstep : stepVector d t b = some t') :
    t'.kern.register q = t.kern.register q := by
  rw [stepVector_pxor d t b dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `pxor` keeps every other XMM register whole. -/
theorem stepVector_pxor_fremd (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src q : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .pxorRR dst src) (hstep : stepVector d t b = some t')
    (hq : q ≠ dst) :
    t'.xmm q = t.xmm q := by
  rw [stepVector_pxor d t b dst src hok hfp h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `pxor` reads per lane as the canonical xor: each 64-bit lane
    xors independently, by the accepted `laneGet_xor`. -/
theorem stepVector_pxor_spur (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (i : Nat)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .pxorRR dst src) (hstep : stepVector d t b = some t')
    (hi : i < laneCount .b64) :
    laneGet .b64 (t'.xmm dst) i =
      xorB .b64 (laneGet .b64 (t.xmm dst) i) (laneGet .b64 (t.xmm src) i) := by
  rw [stepVector_pxor d t b dst src hok hfp h] at hstep
  cases hstep
  show laneGet .b64 ((xmmSet t.xmm dst (vecXor .b64 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_xor .b64 _ _ i hi

/-- `paddq` preserves the flags. -/
theorem stepVector_paddq_flags (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .paddqRR dst src) (hstep : stepVector d t b = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [stepVector_paddq d t b dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `paddq` changes no memory byte. -/
theorem stepVector_paddq_speicher (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .paddqRR dst src) (hstep : stepVector d t b = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [stepVector_paddq d t b dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `paddq` keeps every other XMM register whole. -/
theorem stepVector_paddq_fremd (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src q : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .paddqRR dst src) (hstep : stepVector d t b = some t')
    (hq : q ≠ dst) :
    t'.xmm q = t.xmm q := by
  rw [stepVector_paddq d t b dst src hok hfp h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `paddq` reads per lane as the canonical modular add: each 64-bit
    lane adds independently, by the accepted `laneGet_add`. -/
theorem stepVector_paddq_spur (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (i : Nat)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .paddqRR dst src) (hstep : stepVector d t b = some t')
    (hi : i < laneCount .b64) :
    laneGet .b64 (t'.xmm dst) i =
      addB .b64 (laneGet .b64 (t.xmm dst) i) (laneGet .b64 (t.xmm src) i) := by
  rw [stepVector_paddq d t b dst src hok hfp h] at hstep
  cases hstep
  show laneGet .b64 ((xmmSet t.xmm dst (vecAdd .b64 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_add .b64 _ _ i hi

/-- `paddq` overflow behaviour: each lane result is the modular sum,
    wrapping at `2^64` with no carry into the next lane. -/
theorem stepVector_paddq_modular (d : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (dst src : XmmReg) (i : Nat)
    (hok : laengeOk d.laenge = true) (hfp : vecEintritt b = true)
    (h : d.op = .paddqRR dst src) (hstep : stepVector d t b = some t')
    (hi : i < laneCount .b64) :
    laneNat .b64 (t'.xmm dst) i =
      (laneNat .b64 (t.xmm dst) i + laneNat .b64 (t.xmm src) i) % 2 ^ 64 := by
  have hspur := stepVector_paddq_spur d t t' b dst src i hok hfp h hstep hi
  have h2 := congrArg BitVec.toNat hspur
  rwa [laneGet_toNat, addB_nat, laneGet_toNat, laneGet_toNat] at h2

/-! ## 6. Byte-backed witness: decode, vector step, MOVSD store.

  Pinned canonical bytes decode (through `decodeVector`, with the
  consumed length) to PXOR xmm0, xmm1; the decoded step runs on the
  shared XMM state; the existing MOVSD store (`fpSchritt`, never
  re-evaluated here) carries the low half to memory and observably
  changes a byte. This is the producer/consumer joint for lane 575:
  `decodeVector`/`VectorDec`/`stepVector` plug into its unified path
  behind the pilot-first dispatch. -/

/-- Witness operands: distinct nonzero words whose xor is nonzero. -/
def vecZeugeA : Vektor := BitVec.ofNat 128 0xFF

/-- Witness operands: distinct nonzero words whose xor is nonzero. -/
def vecZeugeB : Vektor := BitVec.ofNat 128 0x0F

/-- The witness xor lands `0xF0` in the low byte. -/
theorem vecZeuge_xor_tief :
    wortByte (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 0 = natByte 240 := by
  decide

/-- Witness core state: zeroed registers and RIP over fully
    permissive zeroed memory. -/
def vecZeugeKern : Zustand :=
  { register := fun _ => 0
    flags := ⟨false, false, none, false, false, false⟩
    rip := 0
    speicher := vecZeugenSpeicher }

/-- Witness XMM file: the two operands in xmm0/xmm1, zero elsewhere. -/
def vecZeugeXmm : XmmDatei
  | .xmm0 => vecZeugeA
  | .xmm1 => vecZeugeB
  | _ => 0

/-- Witness initial extended state at the FP reset context. -/
def vecZeugeT0 : FpZustand := ⟨vecZeugeKern, vecZeugeXmm, kontextReset⟩

/-- Witness readiness: OS vector state enabled. -/
def vecZeugeBereit : BereitProfil := ⟨kontextReset.mxcsr, true⟩

/-- Witness admission holds. -/
theorem vecZeuge_bereit : vecEintritt vecZeugeBereit = true := rfl

/-- Witness successor after the decoded PXOR: xmm0 holds the accepted
    xor word, RIP advanced past the 5 consumed bytes. -/
def vecZeugeT1 : FpZustand :=
  { vecZeugeT0 with kern := { vecZeugeKern with rip := ripNach 0 5 }, xmm := xmmSet vecZeugeXmm .xmm0 (vecXor .b64 vecZeugeA vecZeugeB) }

/-- The witness store address is zero: base register zero plus zero
    displacement. -/
theorem vecZeuge_addr :
    effAddr vecZeugeKern .rax (0 : BitVec 32) = 0 := by
  rfl

/-- The pinned bytes decode to PXOR xmm0, xmm1 with no rest. -/
theorem vecZeuge_decode :
    decodeVector (encodeVector (.pxorRR .xmm0 .xmm1)) =
      some ((⟨.pxorRR .xmm0 .xmm1, 5⟩ : VectorDec), []) := by
  simpa using roundtrip_pxor .xmm0 .xmm1 []

/-- The decoded length is the consumed prefix length. -/
theorem vecZeuge_laenge :
    (⟨.pxorRR .xmm0 .xmm1, 5⟩ : VectorDec).laenge +
      ([] : List Byte).length =
      (encodeVector (.pxorRR .xmm0 .xmm1)).length := by
  simp [encodeVector_len]

/-- The decoded PXOR reaches the witness successor. -/
theorem vecZeuge_schritt :
    stepVector (⟨.pxorRR .xmm0 .xmm1, 5⟩ : VectorDec)
      vecZeugeT0 vecZeugeBereit = some vecZeugeT1 := by
  have h := stepVector_pxor (⟨.pxorRR .xmm0 .xmm1, 5⟩ : VectorDec)
    vecZeugeT0 vecZeugeBereit .xmm0 .xmm1 (by decide) rfl rfl
  exact h

/-- Memory after the witness MOVSD store of the xor low half. -/
def vecZeugeM2 : Speicher :=
  { vecZeugenSpeicher with bytes := writeBytes vecZeugenSpeicher 0 (vLo (vecXor .b64 vecZeugeA vecZeugeB)) }

/-- The existing MOVSD store carries the xor low half to memory. -/
theorem vecZeuge_speichere :
    fpSchritt (⟨.movsdSpeichere .rax .xmm0 (0 : BitVec 32), 1⟩ : FpDecodiert)
      vecZeugeT1 =
      some { vecZeugeT1 with kern := { vecZeugeT1.kern with speicher := vecZeugeM2, rip := ripNach vecZeugeT1.kern.rip 1 } } := by
  have hwr : write64 vecZeugeT1.kern.speicher
      (effAddr vecZeugeT1.kern .rax 0)
      (xmmTief vecZeugeT1.xmm .xmm0) = some vecZeugeM2 := by
    have e1 : vecZeugeT1.kern.speicher = vecZeugenSpeicher := rfl
    have e2 : effAddr vecZeugeT1.kern .rax (0 : BitVec 32) = 0 := by rfl
    have e3 : xmmTief vecZeugeT1.xmm .xmm0 =
        vLo (vecXor .b64 vecZeugeA vecZeugeB) := by
      have hx : vecZeugeT1.xmm =
          xmmSet vecZeugeXmm .xmm0 (vecXor .b64 vecZeugeA vecZeugeB) := rfl
      unfold xmmTief
      rw [hx, xmmSet_gleich]
    rw [e1, e2, e3]
    unfold write64
    have hc : schreibbar8 vecZeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
    rfl
  have hfp : fpEintritt vecZeugeT1.fp = true := fpEintritt_reset
  have h := fpSchritt_movsdSpeichere_erfolg
    (⟨.movsdSpeichere .rax .xmm0 (0 : BitVec 32), 1⟩ : FpDecodiert)
    vecZeugeT1 .rax .xmm0 0 vecZeugeM2 (by decide)
    hfp rfl hwr
  exact h

/-- JOINT WITNESS: pinned bytes decode with their consumed length,
    the decoded vector step runs on the shared XMM state, and the
    existing MOVSD store observably changes a memory byte. -/
theorem vectorCodec_zeuge :
    ∃ (bs : List Byte) (dec : VectorDec) (rest : List Byte)
      (t1 t2 : FpZustand),
      decodeVector bs = some (dec, rest) ∧
      dec.laenge + rest.length = bs.length ∧
      1 ≤ dec.laenge ∧ dec.laenge ≤ 15 ∧
      stepVector dec vecZeugeT0 vecZeugeBereit = some t1 ∧
      (∃ m2 : Speicher, ∃ store : FpDecodiert,
        fpSchritt store t1 = some t2 ∧ t2.kern.speicher = m2 ∧
        m2.bytes 0 ≠ vecZeugeT0.kern.speicher.bytes 0) := by
  refine ⟨encodeVector (.pxorRR .xmm0 .xmm1),
    (⟨.pxorRR .xmm0 .xmm1, 5⟩ : VectorDec), [], vecZeugeT1,
    { vecZeugeT1 with kern := { vecZeugeT1.kern with speicher := vecZeugeM2, rip := ripNach vecZeugeT1.kern.rip 1 } },
    vecZeuge_decode, vecZeuge_laenge, by decide, by decide,
    vecZeuge_schritt, ?_⟩
  refine ⟨vecZeugeM2,
    (⟨.movsdSpeichere .rax .xmm0 (0 : BitVec 32), 1⟩ : FpDecodiert),
    vecZeuge_speichere, rfl, ?_⟩
  have hhit : writeBytes vecZeugenSpeicher 0
      (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 0 =
      wortByte (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 0 := by
    have h := writeBytesN_hit vecZeugenSpeicher 0
      (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 8 0 (by decide) (by decide)
    rwa [addrOff_null] at h
  show vecZeugeM2.bytes 0 ≠ vecZeugenSpeicher.bytes 0
  have e1 : vecZeugeM2.bytes 0 =
      writeBytes vecZeugenSpeicher 0
        (vLo (vecXor .b64 vecZeugeA vecZeugeB)) 0 := rfl
  rw [e1, hhit, vecZeuge_xor_tief]
  decide

/- CUTS:
    - Two register forms only: PXOR (`66 0F EF /r`) and PADDQ
      (`66 0F D4 /r`) with a canonical REX prefix (5 bytes). No memory
      vector form is covered (refused by construction); no other SSE2/
      AVX row exists here. Uncovered rows are reported, not connected:
      PADDW/PADDD/PSUBx/PAND/POR/PXOR-memory/MOVDQA/MOVDQU/PSHUFD and
      every FP packed form have no decoder arm and no step.
    - Execution reuses the accepted lane functions on the shared XMM
      state: `vecXor .b64` for PXOR, `vecAdd .b64` for PADDQ (modular
      per 64-bit lane, no inter-lane carry, no float reassociation --
      no FP operation is involved). Pilot and scalar-FP forms are
      never re-evaluated: `laufAlt`/`fpSchritt` are reused, not
      redefined.
    - No vector store atomicity is claimed: the only memory change
      goes through the existing single-word MOVSD store; the torn
      intermediate state proved by `vecWrite_teilt` stands, and lane
      disjointness never implies atomicity or reordering of shared
      operations.
    - Profile admission (`vecEintritt` = OS vector state) is a
      validator refusal, never a hardware fault; it agrees with the
      finite `paketInt128` admission where silicon support holds.
      No silicon correspondence, fault-order, TSO-bridge, source
      correspondence, budget transfer, progress or image claim is
      made here. `simdFreigabe` stays `false`.
    - Producer/consumer joint for lane 575 (unified extended path):
      `decodeVector` (bytes to `VectorDec` + rest), `decodeComboV`
      (pilot-first dispatch: pilot decides first, vector only where
      the pilot refuses), `stepVector` (decoded form on `FpZustand`
      under `BereitProfil`), and `vectorCodec_zeuge` (pinned bytes,
      consumed length, reached step, byte-backed MOVSD store).
-/

#print axioms codeXmm_xmmCode
#print axioms xmmCode_lt
#print axioms encodeVector_len
#print axioms vectorLen_ok
#print axioms roundtrip_pxor
#print axioms roundtrip_paddq
#print axioms roundtripVector
#print axioms vector_pilot_verweigert
#print axioms decodeComboV_kanonisch
#print axioms decodeComboV_erweitert
#print axioms decodeComboV_nichts
#print axioms vector_nichts_bare0F
#print axioms vector_nichts_speicher_modrm
#print axioms vector_nichts_kurz
#print axioms vecEintritt_merkmal
#print axioms stepVector_laenge_verweigert
#print axioms stepVector_profil_verweigert
#print axioms stepVector_pxor
#print axioms stepVector_paddq
#print axioms stepVector_rip
#print axioms stepVector_pxor_flags
#print axioms stepVector_pxor_speicher
#print axioms stepVector_pxor_gpr
#print axioms stepVector_pxor_fremd
#print axioms stepVector_pxor_spur
#print axioms stepVector_paddq_flags
#print axioms stepVector_paddq_speicher
#print axioms stepVector_paddq_fremd
#print axioms stepVector_paddq_spur
#print axioms stepVector_paddq_modular
#print axioms vecZeuge_xor_tief
#print axioms vecZeuge_addr
#print axioms vecZeuge_decode
#print axioms vecZeuge_laenge
#print axioms vecZeuge_schritt
#print axioms vecZeuge_speichere
#print axioms vectorCodec_zeuge

end Gabbro.Grammatik.X86
