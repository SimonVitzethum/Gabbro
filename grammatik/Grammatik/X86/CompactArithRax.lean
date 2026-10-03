/-
  File:      Grammatik/X86/CompactArithRax.lean
  Subject:   Accumulator short ALU forms (ADD/SUB/CMP RAX, imm32).

  Lane 753: the three RAX short opcodes REX.W + 05/2D/3D id over the
  canonical vocabulary, with ModRM-identical flags, a validator-decided
  short-vs-ModRM choice, and byte-facing execution through the accepted
  `ExtendedExecution` dispatcher. Provenance: Intel SDM combined
  volumes 1-4, edition 325462-093US September 2026 (local snapshot
  `.tmp/HARDWARE-REFERENCES/`, sha256 pinned in REFERENCES.json):
  ADD opcode table "REX.W + 05 id  ADD RAX, imm32 ... Add imm32
  sign-extended to 64-bits to RAX"; SUB table "REX.W + 2D id  SUB RAX,
  imm32 ... Subtract imm32 sign-extended to 64-bits"; CMP table
  "REX.W + 3D id  CMP RAX, imm32 ... Compare imm32 sign-extended to
  64-bits". Only the canonical REX byte 0x48 is admitted; the 8-bit
  neighbours (04/2C/3C) and every other REX refuse explicitly.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile
import Grammatik.X86.ScalarFloat
import Grammatik.X86.Gleitprofil
import Grammatik.X86.Vektor

namespace Gabbro.Grammatik.X86

/-- Covered accumulator short rows: ADD, SUB and CMP of sign-extended
    imm32 against RAX. The 8-bit AL neighbours stay open and refuse. -/
inductive RaxOp where
  | addRaxImm (imm : BitVec 32)
  | subRaxImm (imm : BitVec 32)
  | cmpRaxImm (imm : BitVec 32)
  deriving DecidableEq, Repr

/-- A decoded short row with its consumed length. -/
structure RaxDec where
  op : RaxOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- Short opcode byte: 05 ADD, 2D SUB, 3D CMP (Intel SDM Vol.2A
    ADD/CMP tables, Vol.2B SUB table, REX.W rows). -/
def raxOpcode : RaxOp → Nat
  | .addRaxImm _ => 5
  | .subRaxImm _ => 45
  | .cmpRaxImm _ => 61

/-- Canonical byte encoding: REX.W 0x48, the short opcode, imm32 little
    endian. Length 6, the only admitted shape. -/
def encodeRax : RaxOp → List Byte
  | .addRaxImm imm => natByte 72 :: natByte 5 :: leBytes32 imm
  | .subRaxImm imm => natByte 72 :: natByte 45 :: leBytes32 imm
  | .cmpRaxImm imm => natByte 72 :: natByte 61 :: leBytes32 imm

/-- Every short encoding is 6 bytes, inside the 15-byte cap. -/
theorem encodeRax_len (op : RaxOp) : (encodeRax op).length = 6 := by
  cases op <;> rfl

/-- Independent short decoder: canonical REX 0x48 then 05/2D/3D with a
    full imm32 tail. Anything else refuses: no REX, another REX byte,
    another opcode, a truncated tail, or the 8-bit 04/2C/3C forms. -/
def decodeRax : List Byte → Option (RaxDec × List Byte)
  | b0 :: b1 :: rest =>
    if byteNat b0 == 72 then
      match byteNat b1 with
      | 5 =>
        match parseLe32 rest with
        | some (imm, rest') => some (⟨.addRaxImm imm, 6⟩, rest')
        | none => none
      | 45 =>
        match parseLe32 rest with
        | some (imm, rest') => some (⟨.subRaxImm imm, 6⟩, rest')
        | none => none
      | 61 =>
        match parseLe32 rest with
        | some (imm, rest') => some (⟨.cmpRaxImm imm, 6⟩, rest')
        | none => none
      | _ => none
    else none
  | _ => none

/-- Decoding inverts encoding on every short row, over any suffix. -/
theorem roundtripRax (op : RaxOp) (suffix : List Byte) :
    decodeRax (encodeRax op ++ suffix) =
      some (⟨op, 6⟩, suffix) := by
  cases op with
  | addRaxImm imm =>
    simp [encodeRax, decodeRax, parseLe32_leBytes32, byteNat_natByte_any]
  | subRaxImm imm =>
    simp [encodeRax, decodeRax, parseLe32_leBytes32, byteNat_natByte_any]
  | cmpRaxImm imm =>
    simp [encodeRax, decodeRax, parseLe32_leBytes32, byteNat_natByte_any]

/-- Pinned bytes: ADD RAX, 1. -/
theorem pin_add_rax_eins :
    encodeRax (.addRaxImm (BitVec.ofNat 32 1)) =
      [natByte 72, natByte 5, natByte 1, natByte 0, natByte 0,
        natByte 0] := by
  decide

/-- Pinned decode: ADD RAX, 1. -/
theorem pin_add_rax_eins_dekode :
    decodeRax [natByte 72, natByte 5, natByte 1, natByte 0, natByte 0,
      natByte 0] =
      some ((⟨.addRaxImm (BitVec.ofNat 32 1), 6⟩ : RaxDec), []) := by
  decide

/-- Pinned bytes: SUB RAX, 256. -/
theorem pin_sub_rax_bytes :
    encodeRax (.subRaxImm (BitVec.ofNat 32 256)) =
      [natByte 72, natByte 45, natByte 0, natByte 1, natByte 0,
        natByte 0] := by
  decide

/-- Pinned decode: SUB RAX, 256. -/
theorem pin_sub_rax_dekode :
    decodeRax [natByte 72, natByte 45, natByte 0, natByte 1, natByte 0,
      natByte 0] =
      some ((⟨.subRaxImm (BitVec.ofNat 32 256), 6⟩ : RaxDec), []) := by
  decide

/-- Pinned bytes: CMP RAX, -1 (imm32 0xFFFFFFFF). -/
theorem pin_cmp_rax_bytes :
    encodeRax (.cmpRaxImm (BitVec.ofNat 32 4294967295)) =
      [natByte 72, natByte 61, natByte 255, natByte 255, natByte 255,
        natByte 255] := by
  decide

/-- Pinned decode: CMP RAX, -1. -/
theorem pin_cmp_rax_dekode :
    decodeRax [natByte 72, natByte 61, natByte 255, natByte 255,
      natByte 255, natByte 255] =
      some ((⟨.cmpRaxImm (BitVec.ofNat 32 4294967295), 6⟩ : RaxDec),
        []) := by
  decide

/-- Empty input refuses. -/
theorem rax_nichts_leer : decodeRax [] = none := rfl

/-- A truncated tail refuses. -/
theorem rax_nichts_kurz :
    decodeRax [natByte 72, natByte 5, natByte 1] = none := rfl

/-- Without REX the short opcode refuses (05 alone is not covered). -/
theorem rax_nichts_ohne_rex :
    decodeRax [natByte 5, natByte 1, natByte 0, natByte 0,
      natByte 0] = none := rfl

/-- The 8-bit neighbour ADD AL refuses. -/
theorem rax_nichts_achtbit_add :
    decodeRax [natByte 4, natByte 1] = none := rfl

/-- The 8-bit neighbour SUB AL refuses. -/
theorem rax_nichts_achtbit_sub :
    decodeRax [natByte 44, natByte 1] = none := rfl

/-- The 8-bit neighbour CMP AL refuses. -/
theorem rax_nichts_achtbit_cmp :
    decodeRax [natByte 60, natByte 1] = none := rfl

/-- Another REX byte refuses (only 0x48 is canonical). -/
theorem rax_nichts_rex_anders :
    decodeRax [natByte 73, natByte 5, natByte 1, natByte 0, natByte 0,
      natByte 0] = none := rfl

/-- A ModRM opcode after REX refuses (01 is not a short row). -/
theorem rax_nichts_modrm_opcode :
    decodeRax [natByte 72, natByte 1, natByte 192] = none := rfl

/-! ## Execution: the accepted arithmetic with ModRM-identical flags.

  The immediate is sign-extended through the accepted `dispWort`;
  ADD/SUB reuse `add64`/`sub64` (the exact snapshots the ModRM
  register forms produce); CMP mirrors the `cmpReg64` arm (flags only).
  No memory is touched, so no permission is consulted and no TSO
  interaction exists; with a good length the step always succeeds, so
  no hardware fault outcome exists here. -/

/-- Short step over the canonical `Zustand`. -/
def stepRax (r : RaxDec) (s : Zustand) : Option Zustand :=
  match laengeOk r.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip r.laenge
    match r.op with
    | .addRaxImm imm =>
      let z := add64 (s.register .rax) (dispWort imm)
      some (schrittRegister s nach z.2 .rax z.1)
    | .subRaxImm imm =>
      let z := sub64 (s.register .rax) (dispWort imm)
      some (schrittRegister s nach z.2 .rax z.1)
    | .cmpRaxImm imm =>
      let z := sub64 (s.register .rax) (dispWort imm)
      some ({ s with rip := nach, flags := z.2 })

/-- ADD steps through the accepted 64-bit addition. -/
theorem stepRax_add (r : RaxDec) (s : Zustand) (imm : BitVec 32)
    (hok : laengeOk r.laenge = true) (h : r.op = .addRaxImm imm) :
    stepRax r s =
      some (schrittRegister s (ripNach s.rip r.laenge)
        (add64 (s.register .rax) (dispWort imm)).2 .rax
        (add64 (s.register .rax) (dispWort imm)).1) := by
  unfold stepRax
  rw [hok, h]

/-- SUB steps through the accepted 64-bit subtraction. -/
theorem stepRax_sub (r : RaxDec) (s : Zustand) (imm : BitVec 32)
    (hok : laengeOk r.laenge = true) (h : r.op = .subRaxImm imm) :
    stepRax r s =
      some (schrittRegister s (ripNach s.rip r.laenge)
        (sub64 (s.register .rax) (dispWort imm)).2 .rax
        (sub64 (s.register .rax) (dispWort imm)).1) := by
  unfold stepRax
  rw [hok, h]

/-- CMP writes no register; only flags and RIP move. -/
theorem stepRax_cmp (r : RaxDec) (s : Zustand) (imm : BitVec 32)
    (hok : laengeOk r.laenge = true) (h : r.op = .cmpRaxImm imm) :
    stepRax r s = some ({ s with rip := ripNach s.rip r.laenge, flags := (sub64 (s.register .rax) (dispWort imm)).2 }) := by
  unfold stepRax
  rw [hok, h]

/-- A bad decode length refuses every short form. -/
theorem stepRax_laenge_verweigert (r : RaxDec) (s : Zustand)
    (h : laengeOk r.laenge = false) : stepRax r s = none := by
  unfold stepRax
  simp [h]

/-- FLAG IDENTITY (ADD): the short ADD sets exactly the flags and the
    RAX value the ModRM `addReg64` sets when the source holds the
    sign-extended immediate. -/
theorem rax_add_flag_identitaet (s : Zustand) (imm : BitVec 32)
    (s' s2 : Zustand)
    (h1 : stepRax ⟨.addRaxImm imm, 6⟩ s = some s')
    (h2 : schritt ⟨.addReg64 .rax .rcx, 3⟩
      { s with register := regSet s.register .rcx (dispWort imm) } =
      some s2) :
    s'.flags = s2.flags ∧
      s'.register .rax = s2.register .rax := by
  have h6 : laengeOk 6 = true := by decide
  have h3 : laengeOk 3 = true := by decide
  have hrax : (regSet s.register .rcx (dispWort imm)) .rax =
      s.register .rax :=
    regSet_fremd _ _ _ _ (by decide : (.rax : Register) ≠ .rcx)
  have hrcx : (regSet s.register .rcx (dispWort imm)) .rcx =
      dispWort imm :=
    regSet_gleich _ _ _
  rw [stepRax_add _ s imm h6 rfl] at h1
  rw [schritt_addReg64 _ _ .rax .rcx h3 rfl] at h2
  cases h1
  cases h2
  simp only [schrittRegister, hrax, hrcx]
  exact ⟨trivial, rfl⟩

/-- FLAG IDENTITY (SUB): the short SUB matches the ModRM `subReg64`. -/
theorem rax_sub_flag_identitaet (s : Zustand) (imm : BitVec 32)
    (s' s2 : Zustand)
    (h1 : stepRax ⟨.subRaxImm imm, 6⟩ s = some s')
    (h2 : schritt ⟨.subReg64 .rax .rcx, 3⟩
      { s with register := regSet s.register .rcx (dispWort imm) } =
      some s2) :
    s'.flags = s2.flags ∧
      s'.register .rax = s2.register .rax := by
  have h6 : laengeOk 6 = true := by decide
  have h3 : laengeOk 3 = true := by decide
  have hrax : (regSet s.register .rcx (dispWort imm)) .rax =
      s.register .rax :=
    regSet_fremd _ _ _ _ (by decide : (.rax : Register) ≠ .rcx)
  have hrcx : (regSet s.register .rcx (dispWort imm)) .rcx =
      dispWort imm :=
    regSet_gleich _ _ _
  rw [stepRax_sub _ s imm h6 rfl] at h1
  rw [schritt_subReg64 _ _ .rax .rcx h3 rfl] at h2
  cases h1
  cases h2
  simp only [schrittRegister, hrax, hrcx]
  exact ⟨trivial, rfl⟩

/-- FLAG IDENTITY (CMP): the short CMP matches the ModRM `cmpReg64` in
    flags and keeps every register. -/
theorem rax_cmp_flag_identitaet (s : Zustand) (imm : BitVec 32)
    (s' s2 : Zustand) (q : Register)
    (h1 : stepRax ⟨.cmpRaxImm imm, 6⟩ s = some s')
    (h2 : schritt ⟨.cmpReg64 .rax .rcx, 3⟩
      { s with register := regSet s.register .rcx (dispWort imm) } =
      some s2) :
    s'.flags = s2.flags ∧ s'.register q = s.register q := by
  have h6 : laengeOk 6 = true := by decide
  have h3 : laengeOk 3 = true := by decide
  have hrax : (regSet s.register .rcx (dispWort imm)) .rax =
      s.register .rax :=
    regSet_fremd _ _ _ _ (by decide : (.rax : Register) ≠ .rcx)
  have hrcx : (regSet s.register .rcx (dispWort imm)) .rcx =
      dispWort imm :=
    regSet_gleich _ _ _
  rw [stepRax_cmp _ s imm h6 rfl] at h1
  rw [schritt_cmpReg64 _ _ .rax .rcx h3 rfl] at h2
  cases h1
  cases h2
  exact ⟨by simp only [hrax, hrcx], rfl⟩

/-- A successful short step passed the length gate. -/
theorem stepRax_braucht_laenge (r : RaxDec) (s s' : Zustand)
    (h : stepRax r s = some s') : laengeOk r.laenge = true := by
  by_cases hlen : laengeOk r.laenge = true
  · exact hlen
  · exfalso
    have h2 : laengeOk r.laenge = false := by
      cases hb : laengeOk r.laenge
      · rfl
      · exact absurd hb hlen
    unfold stepRax at h
    rw [h2] at h
    cases h

/-- Every short step keeps memory byte-for-byte: no load, no store, no
    permission consulted, no TSO footprint. -/
theorem stepRax_speicher_bleibt (r : RaxDec) (s s' : Zustand)
    (h : stepRax r s = some s') : s'.speicher = s.speicher := by
  have hok := stepRax_braucht_laenge r s s' h
  cases hop : r.op with
  | addRaxImm imm =>
    rw [stepRax_add r s imm hok hop] at h
    cases h
    rfl
  | subRaxImm imm =>
    rw [stepRax_sub r s imm hok hop] at h
    cases h
    rfl
  | cmpRaxImm imm =>
    rw [stepRax_cmp r s imm hok hop] at h
    cases h
    rfl

/-! ## Dispatch: the accepted dispatcher first, short rows after.

  `decodeRaxCombo` tries the accepted `decodeExt` chain first and
  consults the short decoder only where it refuses, mirroring the
  accepted `decodeCombo` discipline: no accepted form is shadowed and
  no accepted byte string is re-decided. -/

/-- The pilot refuses every short encoding, over any suffix: REX.W +
    05/2D/3D is none of the 14 pilot shapes. -/
theorem pilot_weist_raxkurz_zurueck (op : RaxOp) (suffix : List Byte) :
    decode (encodeRax op ++ suffix) = none := by
  cases op with
  | addRaxImm imm =>
    simp [encodeRax, decode, decodeRex, byteNat_natByte_any]
  | subRaxImm imm =>
    simp [encodeRax, decode, decodeRex, byteNat_natByte_any]
  | cmpRaxImm imm =>
    simp [encodeRax, decode, decodeRex, byteNat_natByte_any]

/-- The narrow extension refuses every short encoding: its REX set is
    40/41/44/45 (W=0), never the short 0x48. -/
theorem narrow_weist_raxkurz_zurueck (op : RaxOp)
    (suffix : List Byte) :
    decodeNarrow (encodeRax op ++ suffix) = none := by
  cases op with
  | addRaxImm imm =>
    simp [encodeRax, decodeNarrow, rexNarrowBits, byteNat_natByte_any]
  | subRaxImm imm =>
    simp [encodeRax, decodeNarrow, rexNarrowBits, byteNat_natByte_any]
  | cmpRaxImm imm =>
    simp [encodeRax, decodeNarrow, rexNarrowBits, byteNat_natByte_any]

/-- Without the canonical REX first byte the short decoder refuses,
    however the tail continues. -/
theorem decodeRax_ohne_rex (b0 : Byte) (bs : List Byte)
    (h : byteNat b0 ≠ 72) : decodeRax (b0 :: bs) = none := by
  cases bs with
  | nil => rfl
  | cons b1 rest =>
    simp only [decodeRax]
    rw [if_neg (by simpa using h)]

/-- The short decoder refuses every pilot encoding, over any suffix:
    no pilot byte string collides with a short row. -/
theorem decodeRax_verweigert_pilot (b : Befehl) (suffix : List Byte) :
    decodeRax (encode b ++ suffix) = none := by
  cases b with
  | movImm64 dst v => cases dst <;> rfl
  | movReg64 dst src => cases dst <;> cases src <;> rfl
  | addReg64 dst src => cases dst <;> cases src <;> rfl
  | subReg64 dst src => cases dst <;> cases src <;> rfl
  | xorReg64 dst src => cases dst <;> cases src <;> rfl
  | cmpReg64 lhs rhs => cases lhs <;> cases rhs <;> rfl
  | load64 dst base d => cases dst <;> cases base <;> rfl
  | store64 base src d => cases base <;> cases src <;> rfl
  | jump32 d => rfl
  | jumpIf32 c d => cases c <;> rfl
  | call32 d => rfl
  | push64 src => cases src <;> exact decodeRax_ohne_rex _ _ (by decide)
  | pop64 dst => cases dst <;> exact decodeRax_ohne_rex _ _ (by decide)
  | ret => exact decodeRax_ohne_rex _ _ (by decide)

/-- Combined decode: the accepted extended dispatcher first, the short
    rows only where it refuses. -/
def decodeRaxCombo : List Byte → Option ((ExtInstr ⊕ RaxDec) × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.inl i, rest)
    | none =>
      match decodeRax bs with
      | some (r, rest) => some (.inr r, rest)
      | none => none

/-- The combined decoder agrees with the accepted dispatcher wherever
    it accepts: no existing form is shadowed. -/
theorem decodeRaxCombo_kanonisch (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeRaxCombo bs = some (.inl i, rest) := by
  unfold decodeRaxCombo
  rw [h]

/-- Where the accepted dispatcher refuses, a short row is taken. -/
theorem decodeRaxCombo_erweitert (bs : List Byte) (r : RaxDec)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeRax bs = some (r, rest)) :
    decodeRaxCombo bs = some (.inr r, rest) := by
  unfold decodeRaxCombo
  rw [h1, h2]

/-- Where both refuse, the combined decoder refuses. -/
theorem decodeRaxCombo_nichts (bs : List Byte)
    (h1 : decodeExt bs = none) (h2 : decodeRax bs = none) :
    decodeRaxCombo bs = none := by
  unfold decodeRaxCombo
  rw [h1, h2]

/-- Pin: the whole accepted chain refuses the closed ADD short bytes. -/
theorem ext_weist_add_zurueck :
    decodeExt (encodeRax (.addRaxImm (BitVec.ofNat 32 1))) = none := by
  decide

/-- Pin: the whole accepted chain refuses the closed SUB short bytes. -/
theorem ext_weist_sub_zurueck :
    decodeExt (encodeRax (.subRaxImm (BitVec.ofNat 32 256))) = none := by
  decide

/-- Pin: the whole accepted chain refuses the closed CMP short bytes. -/
theorem ext_weist_cmp_zurueck :
    decodeExt (encodeRax (.cmpRaxImm (BitVec.ofNat 32 4294967295))) =
      none := by
  decide

/-- Pin: the combined decoder takes the closed ADD short row whole. -/
theorem pin_combo_add :
    decodeRaxCombo (encodeRax (.addRaxImm (BitVec.ofNat 32 1))) =
      some (.inr (⟨.addRaxImm (BitVec.ofNat 32 1), 6⟩ : RaxDec), []) := by
  have h1 := ext_weist_add_zurueck
  have h2 := roundtripRax (.addRaxImm (BitVec.ofNat 32 1)) []
  exact decodeRaxCombo_erweitert _ _ _ h1 h2

/-- Pin: the combined decoder takes the closed SUB short row whole. -/
theorem pin_combo_sub :
    decodeRaxCombo (encodeRax (.subRaxImm (BitVec.ofNat 32 256))) =
      some (.inr (⟨.subRaxImm (BitVec.ofNat 32 256), 6⟩ : RaxDec),
        []) := by
  have h1 := ext_weist_sub_zurueck
  have h2 := roundtripRax (.subRaxImm (BitVec.ofNat 32 256)) []
  exact decodeRaxCombo_erweitert _ _ _ h1 h2

/-- Pin: the combined decoder takes the closed CMP short row whole. -/
theorem pin_combo_cmp :
    decodeRaxCombo
      (encodeRax (.cmpRaxImm (BitVec.ofNat 32 4294967295))) =
      some (.inr (⟨.cmpRaxImm (BitVec.ofNat 32 4294967295), 6⟩ : RaxDec),
        []) := by
  have h1 := ext_weist_cmp_zurueck
  have h2 := roundtripRax (.cmpRaxImm (BitVec.ofNat 32 4294967295)) []
  exact decodeRaxCombo_erweitert _ _ _ h1 h2

/-- Pin: the pilot row still decodes through the combined decoder
    unchanged (no accepted form is shadowed). -/
theorem pin_combo_pilot_ret :
    decodeRaxCombo (encode .ret) = some (.inl (.pilot ⟨.ret, 1⟩), []) := by
  have h := roundtrip_ret ([] : List Byte)
  simp [encode] at h
  exact decodeRaxCombo_kanonisch _ _ _ (decodeExt_kanonisch _ _ _ h)

/-! ## Validator choice: short form against the ModRM route.

  The validator decides per site: `true` keeps the 6-byte short form,
  `false` takes the ModRM route (the immediate into a scratch register,
  then the register form). The scratch register must differ from RAX.
  Both routes reach the same RAX value, the same flags and the same
  memory; only the scratch register and the RIP advance differ. -/

/-- Validator-decided ADD: short form or the ModRM two-step route. -/
def wahlSchritt : Bool → BitVec 32 → Register → Zustand → Option Zustand
  | true, imm, _, s => stepRax ⟨.addRaxImm imm, 6⟩ s
  | false, imm, tmp, s =>
    match schritt ⟨.movImm64 tmp (dispWort imm), 10⟩ s with
    | none => none
    | some s1 => schritt ⟨.addReg64 .rax tmp, 3⟩ s1

/-- The choice agrees: short and ModRM route reach the same RAX, the
    same flags and the same memory. -/
theorem wahlStimmtUeberein (imm : BitVec 32) (tmp : Register)
    (s s1 s2 : Zustand) (htmp : tmp ≠ .rax)
    (hkurz : stepRax ⟨.addRaxImm imm, 6⟩ s = some s1)
    (hlang : wahlSchritt false imm tmp s = some s2) :
    s1.register .rax = s2.register .rax ∧ s1.flags = s2.flags ∧
      s1.speicher = s2.speicher := by
  have h10 : laengeOk 10 = true := by decide
  have h3 : laengeOk 3 = true := by decide
  have h6 : laengeOk 6 = true := by decide
  have hmov := schritt_movImm64 ⟨.movImm64 tmp (dispWort imm), 10⟩ s
    tmp (dispWort imm) h10 rfl
  have hadd := schritt_addReg64 ⟨.addReg64 .rax tmp, 3⟩
    (schrittRegister s (ripNach s.rip 10) s.flags tmp (dispWort imm))
    .rax tmp h3 rfl
  have htmp_rax : regSet s.register tmp (dispWort imm) .rax =
      s.register .rax :=
    regSet_fremd _ _ _ _ (Ne.symm htmp)
  have htmp_tmp : regSet s.register tmp (dispWort imm) tmp =
      dispWort imm :=
    regSet_gleich _ _ _
  simp only [wahlSchritt] at hlang
  simp only [hmov] at hlang
  rw [hadd] at hlang
  rw [stepRax_add _ s imm h6 rfl] at hkurz
  cases hkurz
  cases hlang
  simp only [schrittRegister, htmp_rax, htmp_tmp, regSet_gleich]
  exact ⟨trivial, trivial, trivial⟩

/-! ## Byte-facing execution through the common architecture.

  The short step lifts to `FpZustand` in the narrow-arm discipline
  (the core moves, XMM and FP control are untouched); the combined
  step runs the accepted unified step on dispatcher rows and the short
  step on short rows; fetch follows the `fetchDekodiert` discipline
  over actual fetched bytes with execute permission only. -/

/-- Short step on the extended state. -/
def stepRaxFp (r : RaxDec) (t : FpZustand) : Option FpZustand :=
  match stepRax r t.kern with
  | some s' => some { t with kern := s' }
  | none => none

/-- Selection: the short arm IS the short evaluator on `kern`. -/
theorem stepRaxFp_weiter (r : RaxDec) (t : FpZustand) (s' : Zustand)
    (h : stepRax r t.kern = some s') :
    stepRaxFp r t = some { t with kern := s' } := by
  unfold stepRaxFp
  rw [h]

/-- Selection: short refusal is lifted refusal. -/
theorem stepRaxFp_verweigert (r : RaxDec) (t : FpZustand)
    (h : stepRax r t.kern = none) : stepRaxFp r t = none := by
  unfold stepRaxFp
  rw [h]

/-- Combined step: the accepted unified step on dispatcher rows, the
    short step on short rows. Any refusal is explicit. -/
def stepRaxCombo : (ExtInstr ⊕ RaxDec) → FpZustand → BereitProfil → ExtAusgang
  | .inl i, t, b => stepExt i t b
  | .inr r, t, _ =>
    match stepRaxFp r t with
    | some t' => .weiter t'
    | none => .verweigert

/-- Selection: the dispatcher arm IS the accepted unified step. -/
theorem stepRaxCombo_pilot (i : ExtInstr) (t : FpZustand)
    (b : BereitProfil) :
    stepRaxCombo (.inl i) t b = stepExt i t b := rfl

/-- Selection: the short arm IS the short step on `kern`. -/
theorem stepRaxCombo_rax (r : RaxDec) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : stepRax r t.kern = some s') :
    stepRaxCombo (.inr r) t b = .weiter { t with kern := s' } := by
  have e : stepRaxCombo (.inr r) t b =
      match stepRaxFp r t with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, stepRaxFp_weiter r t s' h]

/-- Selection: short refusal is combined refusal. -/
theorem stepRaxCombo_rax_verweigert (r : RaxDec) (t : FpZustand)
    (b : BereitProfil) (h : stepRax r t.kern = none) :
    stepRaxCombo (.inr r) t b = .verweigert := by
  have e : stepRaxCombo (.inr r) t b =
      match stepRaxFp r t with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, stepRaxFp_verweigert r t h]

/-- Consumed length of one combined instruction. -/
def raxComboLen : (ExtInstr ⊕ RaxDec) → Nat
  | .inl i => extLen i
  | .inr r => r.laenge

/-- Combined admission: length equation, length guard and execute
    permission of the consumed prefix. -/
def raxZugelassen (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr ⊕ RaxDec) (rest : List Byte) : Bool :=
  decide (raxComboLen i + rest.length = fenster.length) &&
    laengeOk (raxComboLen i) &&
    ausfuehrbarN t.kern.speicher t.kern.rip (raxComboLen i)

/-- Admission carries the length equation. -/
theorem raxZugelassen_summe (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr ⊕ RaxDec) (rest : List Byte)
    (h : raxZugelassen t fenster i rest = true) :
    raxComboLen i + rest.length = fenster.length := by
  unfold raxZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsum, _⟩, _⟩ := h
  exact of_decide_eq_true hsum

/-- Admission carries the length guard. -/
theorem raxZugelassen_laenge (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr ⊕ RaxDec) (rest : List Byte)
    (h : raxZugelassen t fenster i rest = true) :
    laengeOk (raxComboLen i) = true := by
  unfold raxZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, hlen⟩, _⟩ := h
  exact hlen

/-- Admission carries execute permission of the consumed prefix. -/
theorem raxZugelassen_ausfuehrbar (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr ⊕ RaxDec) (rest : List Byte)
    (h : raxZugelassen t fenster i rest = true) :
    ausfuehrbarN t.kern.speicher t.kern.rip (raxComboLen i) = true := by
  unfold raxZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hexe⟩ := h
  exact hexe

/-- Fetch and decode through the combined dispatcher over actual
    bytes. The decoded value is never trusted without admission. -/
def fetchRax (t : FpZustand) (fenster : List Byte) :
    Option ((ExtInstr ⊕ RaxDec) × List Byte) :=
  match decodeRaxCombo fenster with
  | none => none
  | some p =>
    if raxZugelassen t fenster p.1 p.2 then some p else none

/-- A successful fetch decodes to the admitted instruction. -/
theorem fetchRax_erfolg (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr ⊕ RaxDec) (rest : List Byte)
    (h : fetchRax t fenster = some (i, rest)) :
    decodeRaxCombo fenster = some (i, rest) ∧
      raxComboLen i + rest.length = fenster.length ∧
      laengeOk (raxComboLen i) = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip (raxComboLen i) =
        true := by
  have e : fetchRax t fenster =
      match decodeRaxCombo fenster with
      | none => (none : Option ((ExtInstr ⊕ RaxDec) × List Byte))
      | some p =>
        if raxZugelassen t fenster p.1 p.2 then some p else none := rfl
  rw [e] at h
  cases hdec : decodeRaxCombo fenster with
  | none =>
    simp [hdec] at h
  | some p =>
    rw [hdec] at h
    by_cases hz : raxZugelassen t fenster p.1 p.2 = true
    · simp [hz] at h
      rw [h] at hz
      exact ⟨by rw [h],
        raxZugelassen_summe t fenster _ _ hz,
        raxZugelassen_laenge t fenster _ _ hz,
        raxZugelassen_ausfuehrbar t fenster _ _ hz⟩
    · simp [hz] at h

/-- One byte step from actual memory through the combined chain: fetch,
    decode, then the combined step. A forged instruction cannot inject;
    any fetch or step failure is explicit refusal. -/
def raxByteschritt (t : FpZustand) (b : BereitProfil) : ExtAusgang :=
  match fetchRax t (geholt t.kern) with
  | none => .verweigert
  | some (i, _) => stepRaxCombo i t b

/-- Selection: a fetched instruction steps through the combined step. -/
theorem raxByteschritt_weiter (t : FpZustand) (b : BereitProfil)
    (i : ExtInstr ⊕ RaxDec) (rest : List Byte) (o : ExtAusgang)
    (hf : fetchRax t (geholt t.kern) = some (i, rest))
    (hs : stepRaxCombo i t b = o) :
    raxByteschritt t b = o := by
  have e : raxByteschritt t b =
      match fetchRax t (geholt t.kern) with
      | none => ExtAusgang.verweigert
      | some (j, _) => stepRaxCombo j t b := rfl
  rw [e, hf]
  exact hs

/-- Selection: fetch refusal is byte-step refusal. -/
theorem raxByteschritt_verweigert (t : FpZustand) (b : BereitProfil)
    (hf : fetchRax t (geholt t.kern) = none) :
    raxByteschritt t b = .verweigert := by
  have e : raxByteschritt t b =
      match fetchRax t (geholt t.kern) with
      | none => ExtAusgang.verweigert
      | some (j, _) => stepRaxCombo j t b := rfl
  rw [e, hf]

/-- Two byte-steps in sequence; refusal stops the run. -/
def raxSchritt2 (t : FpZustand) (b : BereitProfil) : ExtAusgang :=
  match raxByteschritt t b with
  | .weiter t1 => raxByteschritt t1 b
  | x => x

/-! ## Reached run: short ADD followed by a spilling store.

  The connection theorem ties everything together over a fetched
  two-step run from actual memory: a short ADD on RAX, then a pilot
  store spilling RAX. Every premise is first-order (no hidden
  higher-order assumption); the witness below instantiates all of
  them jointly on a non-degenerate memory-changing run. -/

/-- CONNECTION: a fetched short ADD followed by a pilot store reaches
    the incremented RAX, spills it to memory, sets the ModRM-identical
    flags and advances RIP past both instructions. -/
theorem CompactArithRax_verbindung
    (t : FpZustand) (b : BereitProfil) (imm : BitVec 32) (a : Wort)
    (base : Register) (d : BitVec 32) (s1 : Zustand) (m : Speicher)
    (hrax : t.kern.register .rax = a)
    (hfetch1 : fetchRax t (geholt t.kern) =
      some (.inr ⟨.addRaxImm imm, 6⟩, encode (.store64 base .rax d)))
    (hstep1 : stepRax ⟨.addRaxImm imm, 6⟩ t.kern = some s1)
    (hfetch2 : fetchRax ⟨s1, t.xmm, t.fp⟩ (geholt s1) =
      some (.inl (.pilot ⟨.store64 base .rax d, 7⟩), []))
    (hwr : write64 s1.speicher (effAddr s1 base d) (s1.register .rax) =
      some m)
    (hstore : schritt ⟨.store64 base .rax d, 7⟩ s1 =
      some { s1 with speicher := m, rip := ripNach s1.rip 7 })
    (hles : lesbar8 s1.speicher (effAddr s1 base d) = true) :
    ∃ t2 : FpZustand,
      raxSchritt2 t b = .weiter t2 ∧
      t2.kern.register .rax = a + dispWort imm ∧
      read64 t2.kern.speicher (effAddr s1 base d) =
        some (a + dispWort imm) ∧
      t2.kern.flags = (add64 a (dispWort imm)).2 ∧
      t2.kern.rip = ripNach (ripNach t.kern.rip 6) 7 ∧
      t2.xmm = t.xmm ∧ t2.fp = t.fp := by
  have h6 : laengeOk 6 = true := by decide
  have e1 : s1 = schrittRegister t.kern (ripNach t.kern.rip 6)
      (add64 (t.kern.register .rax) (dispWort imm)).2 .rax
      (add64 (t.kern.register .rax) (dispWort imm)).1 := by
    rw [stepRax_add _ t.kern imm h6 rfl] at hstep1
    cases hstep1
    rfl
  have c1 : stepRaxCombo (.inr ⟨.addRaxImm imm, 6⟩) t b =
      .weiter ⟨s1, t.xmm, t.fp⟩ :=
    stepRaxCombo_rax _ t b s1 hstep1
  have r1 : raxByteschritt t b = .weiter ⟨s1, t.xmm, t.fp⟩ :=
    raxByteschritt_weiter t b _ _ _ hfetch1 c1
  have hl : laufAlt ⟨.store64 base .rax d, 7⟩ ⟨s1, t.xmm, t.fp⟩ =
      some ⟨{ s1 with speicher := m, rip := ripNach s1.rip 7 },
        t.xmm, t.fp⟩ := by
    have e : (⟨s1, t.xmm, t.fp⟩ : FpZustand).kern = s1 := rfl
    unfold laufAlt
    rw [e, hstore]
  have c2 : stepRaxCombo
      (.inl (.pilot ⟨.store64 base .rax d, 7⟩)) ⟨s1, t.xmm, t.fp⟩ b =
      .weiter ⟨{ s1 with speicher := m, rip := ripNach s1.rip 7 },
        t.xmm, t.fp⟩ := by
    rw [stepRaxCombo_pilot]
    exact stepExt_pilot _ _ _ _ hl
  have r2 : raxByteschritt ⟨s1, t.xmm, t.fp⟩ b =
      .weiter ⟨{ s1 with speicher := m, rip := ripNach s1.rip 7 },
        t.xmm, t.fp⟩ :=
    raxByteschritt_weiter _ b _ _ _ hfetch2 c2
  have r12 : raxSchritt2 t b =
      .weiter ⟨{ s1 with speicher := m, rip := ripNach s1.rip 7 },
        t.xmm, t.fp⟩ := by
    unfold raxSchritt2
    rw [r1]
    exact r2
  have hadd1 : ∀ x y : Wort, (add64 x y).1 = x + y := fun x y => rfl
  have greg : s1.register .rax = a + dispWort imm := by
    rw [e1]
    simp only [schrittRegister, regSet_gleich, hrax, hadd1]
  have gflags : s1.flags = (add64 a (dispWort imm)).2 := by
    rw [e1]
    simp only [schrittRegister, hrax]
  have grip : ({ s1 with speicher := m, rip := ripNach s1.rip 7 } :
      Zustand).rip = ripNach (ripNach t.kern.rip 6) 7 := by
    rw [e1]
    simp only [schrittRegister]
  have gmem : read64 m (effAddr s1 base d) =
      some (a + dispWort imm) := by
    have hrd := read64_nach_write64 s1.speicher m (effAddr s1 base d)
      (s1.register .rax) hwr hles
    rw [greg] at hrd
    exact hrd
  exact ⟨_, r12, greg, gmem, gflags, grip, rfl, rfl⟩

/-! ## Witness: 41 + 1 spilled to memory from fetched bytes. -/

/-- Witness code bytes: short ADD RAX,1 then the spilling store. -/
def raxWitBild : List Byte :=
  encodeRax (.addRaxImm (BitVec.ofNat 32 1)) ++
    encode (.store64 .rbx .rax (BitVec.ofNat 32 0))

/-- Witness image bytes: the 13-byte program at 4096, zeroes elsewhere. -/
def raxWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match raxWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness execute permission: exactly the 13 image bytes. -/
def raxWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 13)

/-- Witness data permission: one eight-byte cell at 8192. -/
def raxWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 8)

/-- Witness memory: code is execute-only, data read/write-only. -/
def raxWitSpeicher : Speicher :=
  { bytes := raxWitBytes, lesbar := raxWitDaten,
    schreibbar := raxWitDaten, ausfuehrbar := raxWitCode }

/-- Witness registers: 41 in RAX, the cell address in RBX. -/
def raxWitReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 41
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness core state: code at 4096. -/
def raxWitKern : Zustand :=
  { register := raxWitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := raxWitSpeicher }

/-- Witness start state: reset FP control word. -/
def raxWitStart : FpZustand :=
  ⟨raxWitKern, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness readiness: OS vector state present. -/
def raxWitBereit : BereitProfil := ⟨kontextReset.mxcsr, true⟩

/-- Witness intermediate: the state the short ADD must reach, written
    in the shape the step equation concludes. -/
def raxWitS1 : Zustand :=
  schrittRegister raxWitStart.kern
    (ripNach raxWitStart.kern.rip 6)
    (add64 (raxWitStart.kern.register .rax)
      (dispWort (BitVec.ofNat 32 1))).2 .rax
    (add64 (raxWitStart.kern.register .rax)
      (dispWort (BitVec.ofNat 32 1))).1

/-- Witness memory after the spilling store, in the shape the write
    equation concludes. -/
def raxWitM : Speicher :=
  { raxWitSpeicher with bytes := writeBytes raxWitSpeicher (effAddr raxWitS1 .rbx (BitVec.ofNat 32 0)) (raxWitS1.register .rax) }

/-- WITNESS: all premises of the connection jointly inhabited on a
    non-degenerate memory-changing reached run: RAX moves 41 to 42
    from fetched bytes, the cell moves 0 to 42, RIP advances past
    both instructions. -/
theorem CompactArithRax_verbindung_zeuge :
    ∃ t2 : FpZustand,
      raxSchritt2 raxWitStart raxWitBereit = .weiter t2 ∧
      t2.kern.register .rax = BitVec.ofNat 64 42 ∧
      read64 t2.kern.speicher (BitVec.ofNat 64 8192) =
        some (BitVec.ofNat 64 42) ∧
      raxWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      raxWitStart.kern.register .rax = BitVec.ofNat 64 41 := by
  have hadd42 : BitVec.ofNat 64 41 + dispWort (BitVec.ofNat 32 1) =
      BitVec.ofNat 64 42 := by
    decide
  have haeff : effAddr raxWitS1 .rbx (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8192 := by
    decide
  have hrax : raxWitStart.kern.register .rax =
      BitVec.ofNat 64 41 := by
    decide
  have hfetch1 : fetchRax raxWitStart (geholt raxWitStart.kern) =
      some (.inr ⟨.addRaxImm (BitVec.ofNat 32 1), 6⟩,
        encode (.store64 .rbx .rax (BitVec.ofNat 32 0))) := by
    decide
  have h6 : laengeOk 6 = true := by decide
  have hstep1 : stepRax ⟨.addRaxImm (BitVec.ofNat 32 1), 6⟩
      raxWitStart.kern = some raxWitS1 :=
    stepRax_add ⟨.addRaxImm (BitVec.ofNat 32 1), 6⟩ raxWitStart.kern
      (BitVec.ofNat 32 1) h6 rfl
  have hfetch2 : fetchRax ⟨raxWitS1, raxWitStart.xmm, raxWitStart.fp⟩
      (geholt raxWitS1) =
      some (.inl (.pilot ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩),
        []) := by
    decide
  have hperm : schreibbar8 raxWitS1.speicher
      (effAddr raxWitS1 .rbx (BitVec.ofNat 32 0)) = true := by
    decide
  have hwr : write64 raxWitS1.speicher (effAddr raxWitS1 .rbx (BitVec.ofNat 32 0)) (raxWitS1.register .rax) = some raxWitM := by
    have e : write64 raxWitS1.speicher (effAddr raxWitS1 .rbx (BitVec.ofNat 32 0)) (raxWitS1.register .rax) = some { raxWitS1.speicher with bytes := writeBytes raxWitS1.speicher (effAddr raxWitS1 .rbx (BitVec.ofNat 32 0)) (raxWitS1.register .rax) } := by
      unfold write64
      rw [if_pos hperm]
    exact e
  have h7 : laengeOk 7 = true := by decide
  have hstore : schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ raxWitS1 = some { raxWitS1 with speicher := raxWitM, rip := ripNach raxWitS1.rip 7 } := by
    have h := schritt_store64_erfolg
      ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ raxWitS1 .rbx .rax
      (BitVec.ofNat 32 0) raxWitM h7 rfl hwr
    exact h
  have hles : lesbar8 raxWitS1.speicher
      (effAddr raxWitS1 .rbx (BitVec.ofNat 32 0)) = true := by
    decide
  have h := CompactArithRax_verbindung raxWitStart raxWitBereit
    (BitVec.ofNat 32 1) (BitVec.ofNat 64 41) .rbx (BitVec.ofNat 32 0)
    raxWitS1 raxWitM hrax hfetch1 hstep1 hfetch2 hwr hstore hles
  obtain ⟨t2, hr12, hgreg, hgmem, _, _, _, _⟩ := h
  rw [hadd42] at hgreg hgmem
  rw [haeff] at hgmem
  exact ⟨t2, hr12, hgreg, hgmem, by decide, by decide⟩

/- CUTS:
    Proved here, over the ACTUAL accepted vocabulary (`Typen`,
    `Wort.add64`/`sub64`, `Ausfuehrung.dispWort`/`schrittRegister`/
    `schritt` equations, `Codec` round trips, `Byteschritt.geholt`/
    `ausfuehrbarN`, `Speicher.read64`/`write64`, the UNCHANGED accepted
    `ExtendedExecution` dispatcher and step): the three RAX short rows
    (REX.W + 05/2D/3D id, imm32 sign-extended, canonical REX 0x48 only)
    with canonical encoding, an independent decoder with round trip,
    ModRM-identical flags, memory preservation (no load/store, hence no
    permission gate and no TSO footprint), general pilot/narrow
    disjointness with closed whole-chain pins, the combined dispatcher
    (accepted chain first, never shadowed), the validator-decided
    short-vs-ModRM choice with agreement, fetch under the
    `fetchDekodiert` discipline, and the reached two-step connection
    (short ADD then spilling store) with a jointly inhabited
    non-degenerate memory-changing witness.
    NOT proved here, and not claimed:
    - No hardware correspondence beyond the stated canonical subset:
      the REX.W + 05/2D/3D rows and their flag snapshots are
      self-consistent against the accepted arithmetic, grounded in the
      cited Intel SDM tables, not verified against silicon.
    - No SUB/CMP fetched runs: the reached run pins ADD; SUB and CMP
      share the step and flag-identity proofs but no byte-level run.
    - No per-access TSO bridge: short steps touch no memory, so there
      is nothing to project; the store leg is the accepted pilot step.
    - No source correspondence, no ABI/image/entry/budget connection,
      no cost or time transfer.
    - Whole-chain refusal of short windows is pinned per closed form
      (`ext_weist_*_zurueck`); the general arbitrary-input statement
      over all immediates stays open.
    - AF is `some` (defined) for ADD/SUB/CMP exactly as the accepted
      `add64`/`sub64` compute it; no independent AF claim is made.
-/

#print axioms encodeRax_len
#print axioms roundtripRax
#print axioms pin_add_rax_eins_dekode
#print axioms pin_sub_rax_dekode
#print axioms pin_cmp_rax_dekode
#print axioms stepRax_add
#print axioms stepRax_sub
#print axioms stepRax_cmp
#print axioms rax_add_flag_identitaet
#print axioms rax_sub_flag_identitaet
#print axioms rax_cmp_flag_identitaet
#print axioms stepRax_braucht_laenge
#print axioms stepRax_speicher_bleibt
#print axioms pilot_weist_raxkurz_zurueck
#print axioms narrow_weist_raxkurz_zurueck
#print axioms decodeRax_ohne_rex
#print axioms decodeRax_verweigert_pilot
#print axioms decodeRaxCombo_kanonisch
#print axioms decodeRaxCombo_erweitert
#print axioms decodeRaxCombo_nichts
#print axioms pin_combo_add
#print axioms pin_combo_pilot_ret
#print axioms wahlStimmtUeberein
#print axioms stepRaxFp_weiter
#print axioms stepRaxFp_verweigert
#print axioms stepRaxCombo_pilot
#print axioms stepRaxCombo_rax
#print axioms stepRaxCombo_rax_verweigert
#print axioms fetchRax_erfolg
#print axioms raxByteschritt_weiter
#print axioms raxByteschritt_verweigert
#print axioms CompactArithRax_verbindung
#print axioms CompactArithRax_verbindung_zeuge

end Gabbro.Grammatik.X86
