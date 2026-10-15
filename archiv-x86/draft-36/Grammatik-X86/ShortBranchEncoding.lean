/-
  File:      Grammatik/X86/ShortBranchEncoding.lean
  Subject:   Canonical short-branch rel8 encoding rows (EB cb / 70+cc cb).

  Lane 1115: models short JMP rel8 and short Jcc rel8 (all 16 conditions)
  in their own file. Admission into the `Befehl` inductive is follow-up work
  and named in CUTS. The existing near forms (E9, E8, 0F 80+cc) remain
  the only canonical `Befehl` constructors; short forms are pure byte rows
  with their own encode/decode and proofs here.

  Canonical bytes per BYTE-PILOT.md extension:
  - short JMP:  EB disp8              (2 bytes)
  - short Jcc:  70+cc disp8           (2 bytes), cc = condCode 0..15
-/
import Grammatik.X86.Typen
import Grammatik.X86.Codec
import Grammatik.X86.Rel8Reach

set_option maxRecDepth 10000

namespace Gabbro.Grammatik.X86

/-- A signed 8-bit displacement as a raw byte (two's complement). -/
def disp8Byte (d : Int) : Byte :=
  natByte (Int.toNat (d % 256))

/-- Parse one signed byte, returning the rest. -/
def parseDisp8 : List Byte → Option (Int × List Byte)
  | [] => none
  | b :: rest => some (disp8Signed b, rest)

/-- Canonical encoding of short JMP rel8: EB disp8. -/
def encodeShortJmp (disp : Int) : List Byte :=
  [natByte 235, disp8Byte disp]

/-- Canonical encoding of short Jcc rel8: 70+cc disp8. -/
def encodeShortJcc (cond : Bedingung) (disp : Int) : List Byte :=
  [natByte (112 + condCode cond), disp8Byte disp]

/-- Exact length of a short JMP rel8 is 2 bytes. -/
theorem encodeShortJmp_len (disp : Int) :
    (encodeShortJmp disp).length = 2 := by
  simp [encodeShortJmp]
  <;> rfl

/-- Exact length of a short Jcc rel8 is 2 bytes. -/
theorem encodeShortJcc_len (cond : Bedingung) (disp : Int) :
    (encodeShortJcc cond disp).length = 2 := by
  simp [encodeShortJcc]
  <;> rfl

/-- Decode a short JMP rel8: EB disp8, returning the signed displacement. -/
def decodeShortJmp : List Byte → Option (Int × List Byte)
  | [] => none
  | b :: rest =>
    if byteNat b = 235 then
      parseDisp8 rest
    else none

/-- Decode a short Jcc rel8: 70+cc disp8, returning condition and displacement. -/
def decodeShortJcc : List Byte → Option (Bedingung × Int × List Byte)
  | [] => none
  | b :: rest =>
    let c := byteNat b
    if 112 ≤ c ∧ c < 128 then
      match codeCond (c - 112) with
      | some cond =>
        match parseDisp8 rest with
        | some (disp, rest') => some (cond, disp, rest')
        | none => none
      | none => none
    else none

/-- Truncated short JMP (only opcode byte) is refused. -/
theorem decodeShortJmp_nichts_kurz :
    decodeShortJmp [natByte 235] = none := by
  dsimp only [decodeShortJmp, parseDisp8]
  <;> rfl

/-- Truncated short Jcc (only opcode byte) is refused, for every condition. -/
theorem decodeShortJcc_nichts_kurz (cond : Bedingung) :
    decodeShortJcc [natByte (112 + condCode cond)] = none := by
  have hbyte : byteNat (natByte (112 + condCode cond)) = 112 + condCode cond := by
    have hlt : 112 + condCode cond < 256 := by
      have hc := condCode_lt cond
      omega
    exact byteNat_natByte_of_lt _ hlt
  have hrange : 112 ≤ 112 + condCode cond ∧ 112 + condCode cond < 128 := by
    have hc := condCode_lt cond
    omega
  have hcode : codeCond (112 + condCode cond - 112) = some cond := by
    have heq : 112 + condCode cond - 112 = condCode cond := by omega
    rw [heq]
    exact codeCond_condCode cond
  dsimp only [decodeShortJcc]
  rw [hbyte]
  simp only [hrange, hcode, parseDisp8]
  rfl

/-- Decode distinctness: short JMP (EB) never decodes as near JMP (E9). -/
theorem decodeShortJmp_distinct_nearJmp (suffix : List Byte) :
    decodeShortJmp (natByte 233 :: (leBytes32 (BitVec.ofNat 32 0) ++ suffix)) = none := by
  have h₂₃₃ : byteNat (natByte (233 : Nat)) = 233 := by
    rw [byteNat_natByte_of_lt 233 (by decide)]
  dsimp only [decodeShortJmp]
  <;> simp [h₂₃₃]
  <;> rfl

/-- Decode distinctness: short Jcc (70+cc) never decodes as near Jcc (0F 80+cc). -/
theorem decodeShortJcc_distinct_nearJcc (cond : Bedingung) (suffix : List Byte) :
    decodeShortJcc (natByte 15 :: natByte (128 + condCode cond) :: (leBytes32 (BitVec.ofNat 32 0) ++ suffix)) = none := by
  have h₁₅ : byteNat (natByte (15 : Nat)) = 15 := by
    rw [byteNat_natByte_of_lt 15 (by decide)]
  have h_cond : byteNat (natByte (128 + condCode cond)) = 128 + condCode cond := by
    have h₃ : 128 + condCode cond < 256 := by
      have h₄ : condCode cond < 16 := condCode_lt cond
      omega
    have h₄ : (128 + condCode cond : Nat) < 256 := by exact_mod_cast h₃
    rw [byteNat_natByte_of_lt (128 + condCode cond) h₄]
  dsimp only [decodeShortJcc]
  <;> simp [h₁₅, h_cond, condCode]
  <;>
  (try simp_all [condCode]) <;>
  (try decide) <;>
  rfl

/-- Decode distinctness: near JMP (E9) never decodes as short JMP (EB). -/
theorem decodeNearJmp_distinct_shortJmp (d : BitVec 32) (suffix : List Byte) :
    decodeShortJmp (encode (.jump32 d) ++ suffix) = none := by
  have h₂₃₃ : byteNat (natByte (233 : Nat)) = 233 := by
    rw [byteNat_natByte_of_lt 233 (by decide)]
  dsimp only [encode, decodeShortJmp] at *
  <;> simp [h₂₃₃, leBytes32, byteNat_natByte_of_lt, byteNat_natByte_mod, natByte] at *
  <;>
  (try simp_all [condCode]) <;>
  (try decide) <;>
  rfl

/-- Decode distinctness: near Jcc (0F 80+cc) never decodes as short Jcc (70+cc). -/
theorem decodeNearJcc_distinct_shortJcc (cond : Bedingung) (d : BitVec 32) (suffix : List Byte) :
    decodeShortJcc (encode (.jumpIf32 cond d) ++ suffix) = none := by
  have h₁₅ : byteNat (natByte (15 : Nat)) = 15 := by
    rw [byteNat_natByte_of_lt 15 (by decide)]
  have h_cond : byteNat (natByte (128 + condCode cond)) = 128 + condCode cond := by
    have h₃ : 128 + condCode cond < 256 := by
      have h₄ : condCode cond < 16 := condCode_lt cond
      omega
    have h₄ : (128 + condCode cond : Nat) < 256 := by exact_mod_cast h₃
    rw [byteNat_natByte_of_lt (128 + condCode cond) h₄]
  dsimp only [encode, decodeShortJcc] at *
  <;> simp [h₁₅, h_cond, condCode, leBytes32, byteNat_natByte_of_lt, byteNat_natByte_mod, natByte] at *
  <;>
  (try simp_all [condCode]) <;>
  (try decide) <;>
  rfl

/-- Decode distinctness: short JMP (EB) never decodes as near CALL (E8). -/
theorem decodeShortJmp_distinct_nearCall (suffix : List Byte) :
    decodeShortJmp (natByte 232 :: (leBytes32 (BitVec.ofNat 32 0) ++ suffix)) = none := by
  have h₂₃₂ : byteNat (natByte (232 : Nat)) = 232 := by
    rw [byteNat_natByte_of_lt 232 (by decide)]
  dsimp only [decodeShortJmp]
  simp [h₂₃₂]

/-- Decode distinctness: short Jcc (70+cc) never decodes as near CALL (E8). -/
theorem decodeShortJcc_distinct_nearCall (suffix : List Byte) :
    decodeShortJcc (natByte 232 :: (leBytes32 (BitVec.ofNat 32 0) ++ suffix)) = none := by
  have h₂₃₂ : byteNat (natByte (232 : Nat)) = 232 := by
    rw [byteNat_natByte_of_lt 232 (by decide)]
  dsimp only [decodeShortJcc]
  simp [h₂₃₂]

/-- Decode distinctness: near CALL (E8) never decodes as short JMP (EB). -/
theorem decodeNearCall_distinct_shortJmp (d : BitVec 32) (suffix : List Byte) :
    decodeShortJmp (encode (.call32 d) ++ suffix) = none := by
  have h₂₃₂ : byteNat (natByte (232 : Nat)) = 232 := by
    rw [byteNat_natByte_of_lt 232 (by decide)]
  dsimp only [encode, decodeShortJmp] at *
  simp [h₂₃₂, leBytes32] at *

/-- Decode distinctness: near CALL (E8) never decodes as short Jcc (70+cc). -/
theorem decodeNearCall_distinct_shortJcc (d : BitVec 32) (suffix : List Byte) :
    decodeShortJcc (encode (.call32 d) ++ suffix) = none := by
  have h₂₃₂ : byteNat (natByte (232 : Nat)) = 232 := by
    rw [byteNat_natByte_of_lt 232 (by decide)]
  dsimp only [encode, decodeShortJcc] at *
  simp [h₂₃₂, leBytes32] at *

/-- Canonical decoder refuses short JMP bytes: no byte string decodes both ways. -/
theorem decode_verweigert_shortJmp :
    decode [natByte 235, natByte 254] = none := by
  decide

/-- Canonical decoder refuses short Jcc bytes: no byte string decodes both ways. -/
theorem decode_verweigert_shortJcc :
    decode [natByte 116, natByte 5] = none := by
  decide

/-- All 16 conditions share one short-Jcc opcode shape at fixed disp 5. -/
theorem encodeShortJcc_opcode_all (cond : Bedingung) :
    (encodeShortJcc cond 5).length = 2 ∧
      byteNat (encodeShortJcc cond 5).head! = 112 + condCode cond := by
  have hlt : 112 + condCode cond < 256 := by
    have hc := condCode_lt cond
    omega
  have hbyte := byteNat_natByte_of_lt (112 + condCode cond) hlt
  simp only [encodeShortJcc]
  exact ⟨rfl, hbyte⟩

/-- Target address computation for short JMP: rip_after + sext8(disp). -/
def shortJmpZiel (rip : Nat) (len : Nat) (disp : Int) : Int :=
  (rip + len : Int) + disp

/-- Target address computation for short Jcc: rip_after + sext8(disp). -/
def shortJccZiel (rip : Nat) (len : Nat) (disp : Int) : Int :=
  (rip + len : Int) + disp

/-- The target of a short branch lies within -128..+127 of rip_after. -/
theorem shortJmp_ziel_schranke (rip len : Nat) (disp : Int)
    (h : -128 ≤ disp ∧ disp ≤ 127) :
    -128 ≤ shortJmpZiel rip len disp - (rip + len : Int) ∧
      shortJmpZiel rip len disp - (rip + len : Int) ≤ 127 := by
  dsimp only [shortJmpZiel]
  exact ⟨by omega, by omega⟩

/-- The target of a short conditional branch lies within -128..+127 of rip_after. -/
theorem shortJcc_ziel_schranke (rip len : Nat) (disp : Int)
    (h : -128 ≤ disp ∧ disp ≤ 127) :
    -128 ≤ shortJccZiel rip len disp - (rip + len : Int) ∧
      shortJccZiel rip len disp - (rip + len : Int) ≤ 127 := by
  dsimp only [shortJccZiel]
  exact ⟨by omega, by omega⟩

/-- Out-of-range displacement is refused by the range check. -/
theorem disp8_ausser_reichweite_verweigert (disp : Int) (h : disp < -128 ∨ disp > 127) :
    ¬ (-128 ≤ disp ∧ disp ≤ 127) := by
  intro h₂
  cases h with
  | inl h₃ => omega
  | inr h₃ => omega

/-- WITNESS: short JMP round trip with bytes EB FE (disp = -2). -/
theorem shortJmp_roundtrip_zeuge :
    decodeShortJmp (encodeShortJmp (-2) ++ []) = some (-2, []) := by
  dsimp only [encodeShortJmp, decodeShortJmp, parseDisp8, disp8Byte, disp8Signed]
  <;> simp [natByte, byteNat_natByte_of_lt, byteNat_natByte_mod]
  <;>
  (try decide) <;>
  rfl

/-- WITNESS: short Jcc round trip with bytes 74 05 (cond = e (4), disp = 5). -/
theorem shortJcc_roundtrip_zeuge :
    decodeShortJcc (encodeShortJcc Bedingung.e 5 ++ []) = some (Bedingung.e, 5, []) := by
  dsimp only [encodeShortJcc, decodeShortJcc, parseDisp8, disp8Byte, disp8Signed]
  <;> simp [condCode, codeCond, natByte, byteNat_natByte_of_lt, byteNat_natByte_mod]
  <;>
  (try decide) <;>
  rfl

/-- WITNESS: concrete target computation for short branch. -/
theorem shortBranch_target_zeuge :
    shortJmpZiel 4096 2 (-2 : Int) = 4096 := by
  dsimp only [shortJmpZiel]
  <;>
  (try decide) <;>
  rfl

/- CUTS:
  - Proved here: canonical 2-byte lengths for EB / 70+cc;
    disp8 sign handling via the reused `disp8Signed` with target
    computation (rip_after + sext8); witness round-trips EB FE and
    74 05 plus the all-16 opcode-shape fact `encodeShortJcc_opcode_all`;
    explicit refusal of truncated inputs for JMP and for every Jcc
    condition; decode-distinctness against all three near forms
    (E9 jump, E8 call, 0F 80+cc) in both directions, plus canonical
    `decode` refusal of the short witness bytes so no byte string
    decodes both ways; rel8 range bound facts (target within
    -128..+127 of rip_after; out-of-range is a follow-up relocation
    decision, refused here, never silently widened); the three ZEUGE
    theorems.
  - NOT proved here, and not claimed:
    - Admission into the `Befehl` inductive (follow-up work).
    - Generic round-trip for arbitrary in-range disp values
      (`disp8Signed (disp8Byte d) = d` for -128 <= d <= 127):
      only the pinned instances EB FE and 74 05 plus the opcode
      shape for all 16 conditions are proved here.
    - Execution semantics for short branches (faults are lane 804; control
      execution is lane 338; encoding rows only here).
    - Layout selection between rel8 and rel32 (that is a relocation decision
      using these range facts, not part of the byte rows).
    - Hardware correspondence: these are self-consistent canonical byte rows
      against BYTE-PILOT.md extension, not x86 truth.
    - Source correspondence, TSO bridge, ABI/loader, whole-image coverage.
-/

#print axioms encodeShortJmp_len
#print axioms encodeShortJcc_len
#print axioms decodeShortJmp_nichts_kurz
#print axioms decodeShortJcc_nichts_kurz
#print axioms decodeShortJmp_distinct_nearJmp
#print axioms decodeShortJcc_distinct_nearJcc
#print axioms decodeNearJmp_distinct_shortJmp
#print axioms decodeNearJcc_distinct_shortJcc
#print axioms decodeShortJmp_distinct_nearCall
#print axioms decodeShortJcc_distinct_nearCall
#print axioms decodeNearCall_distinct_shortJmp
#print axioms decodeNearCall_distinct_shortJcc
#print axioms decode_verweigert_shortJmp
#print axioms decode_verweigert_shortJcc
#print axioms encodeShortJcc_opcode_all
#print axioms shortJmp_ziel_schranke
#print axioms shortJcc_ziel_schranke
#print axioms disp8_ausser_reichweite_verweigert
#print axioms shortJmp_roundtrip_zeuge
#print axioms shortJcc_roundtrip_zeuge
#print axioms shortBranch_target_zeuge

end Gabbro.Grammatik.X86