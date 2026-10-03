/-
  File:      Grammatik/X86/CompactImm8Sub.lean
  Subject:   Connection for the REX.W 83/5 imm8 row (SUB r/m64, imm8).

  Lane 749: exactly one row -- REX.W + 83 /5 ib, SUB r/m64, imm8,
  register-direct (mod=3) -- with borrow/flag identity, pinned bytes
  and refusal outside the signed byte. Reuses the accepted producers
  (`IntegerHardwareForms`: encode/decode/step/fetch; `Wort.sub64`;
  canonical `Zustand`/`Speicher`; pilot `schritt` for the witness
  store). No new syntax, decoder, evaluator or state type.

  Manual: Intel SDM 325462-093US (Sep 2026), Vol. 2B 4-685/4-686,
  heading SUB-Subtract: row "REX.W + 83 /5 ib  SUB r/m64, imm8  MI
  Valid N.E. Subtract sign-extended imm8 from r/m64"; Operation
  DEST := (DEST - SRC); immediates sign-extended to the destination
  width; flags OF SF ZF AF PF CF set according to the result.
  Bundle: .tmp/HARDWARE-REFERENCES (REFERENCES.json + intel txt).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.NarrowOps
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.IntegerHardwareForms

namespace Gabbro.Grammatik.X86

/-- Pinned compact bytes: `sub rax, 1` is REX.W, 83, E8, 01. -/
theorem pin_sub_kompakt :
    encodeIntHwImm (.subI .rax 1) =
      [natByte 72, natByte 131, natByte 232, natByte 1] := by
  decide

/-! ## 1. Compact choice and imm8 fit: the row refuses outside i8.

    The encoder emits the 4-byte compact form (REX.W, 83, /5, ib)
    exactly for immediates fitting the signed byte; anything else
    takes the 7-byte wide form (REX.W, 81, /5, id). Dually, every
    byte the compact decoder reads sign-extends into the signed
    byte, so a compact decode can never smuggle a wide value. -/

/-- The compact SUB choice fires exactly on fitting values. -/
theorem kompakt_sub_feuert (dst : Register) (imm : BitVec 32) :
    (encodeIntHwImm (.subI dst imm)).length = 4 ↔ immPasst8 imm = true := by
  unfold encodeIntHwImm
  by_cases h : immPasst8 imm = true
  · simp [h]
  · have hf : immPasst8 imm = false := by
      cases he : immPasst8 imm with
      | true => simp [he] at h
      | false => rfl
    simp [hf, length_leBytes32]

/-- Every byte sign-extends into the signed byte: compact decodes fit.
    Case split at 128 with the reused truncation bridge
    (`narrowTruncMod`) and the bit-31 boundary (`bit31_equiv`). -/
theorem imm8Erweitern_passt (n : Nat) (h : n < 256) :
    immPasst8 (imm8Erweitern n) = true := by
  unfold immPasst8 imm8Erweitern
  by_cases hg : n ≥ 128
  · rw [if_pos hg]
    have hbound : 0xFFFFFF00 + n < 2 ^ 32 := by omega
    have hto : (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat =
        0xFFFFFF00 + n := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have hto64 : (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat).toNat =
        0xFFFFFF00 + n := by
      rw [hto, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have htr : (trunc .b32 (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)).toNat =
        0xFFFFFF00 + n := by
      rw [narrowTruncMod, hto64]
      exact Nat.mod_eq_of_lt hbound
    have hneg : negB .b32 (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat) = true := by
      unfold negB
      rw [htr, show signBit .b32 = 31 from rfl,
        bit31_equiv _ (by omega)]
      exact decide_eq_true (by omega)
    have hbits : Breite.bits .b32 = 32 := rfl
    have hval : sVal .b32 (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat) =
        (((0xFFFFFF00 + n : Nat)) : Int) - (((2 ^ 32 : Nat)) : Int) := by
      have e0 : sVal .b32 (BitVec.ofNat 64
          (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat) =
          if negB .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)
          then ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)).toNat : Int) -
            (((2 ^ Breite.bits .b32 : Nat)) : Int)
          else ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)).toNat : Int) := rfl
      simp only [e0, htr, hneg, hbits, if_true]
    rw [hval]
    exact decide_eq_true (by omega)
  · have hg' : ¬ n ≥ 128 := hg
    rw [if_neg hg']
    have hto : (BitVec.ofNat 32 n).toNat = n := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hto64 : (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat).toNat =
        n := by
      rw [hto, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have htr : (trunc .b32
        (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat)).toNat = n := by
      have hbits : Breite.bits .b32 = 32 := rfl
      rw [narrowTruncMod, hto64, hbits]
      exact Nat.mod_eq_of_lt (by omega)
    have hneg : negB .b32
        (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat) = false := by
      unfold negB
      rw [htr, show signBit .b32 = 31 from rfl,
        bit31_equiv _ (by omega)]
      exact decide_eq_false (by omega)
    have hval : sVal .b32
        (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat) = ((n : Nat) : Int) := by
      have e0 : sVal .b32 (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat) =
          if negB .b32 (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat)
          then ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 n).toNat)).toNat : Int) -
            (((2 ^ Breite.bits .b32 : Nat)) : Int)
          else ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 n).toNat)).toNat : Int) := rfl
      simp only [e0, htr, hneg, Bool.false_eq_true, if_false]
    rw [hval]
    exact decide_eq_true (by omega)

/-- Pinned compact bytes: `sub rax, -1` signs through one byte. -/
theorem pin_sub_neg1 :
    encodeIntHwImm (.subI .rax 0xFFFFFFFF) =
      [natByte 72, natByte 131, natByte 232, natByte 255] := by
  decide

/-- Pinned compact bytes over an extended register: `sub r9, 1`. -/
theorem pin_sub_r9 :
    encodeIntHwImm (.subI .r9 1) =
      [natByte 73, natByte 131, natByte 233, natByte 1] := by
  decide

/-- Pinned wide bytes: `sub rax, 256` needs the imm32 form. -/
theorem pin_sub_weit :
    encodeIntHwImm (.subI .rax 256) =
      [natByte 72, natByte 129, natByte 232,
       natByte 0, natByte 1, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: compact `sub rax, 1` (4 bytes). -/
theorem pin_sub_kompakt_dekode :
    decodeIntHwImm [natByte 72, natByte 131, natByte 232, natByte 1] =
      some ((⟨.subI .rax 1, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned decode: compact `sub rax, -1` (sign extension at decode). -/
theorem pin_sub_neg1_dekode :
    decodeIntHwImm
      [natByte 72, natByte 131, natByte 232, natByte 255] =
      some ((⟨.subI .rax 0xFFFFFFFF, 4⟩ : IntHwImmDec), []) := by
  decide

/-! ## 2. Per-width gates and planted neighbour refusals.

    The SUB-imm row executes at b64 only (the manual's REX.W row;
    no narrow arithmetic flag snapshot exists). The decoder admits
    no 32-bit SUB-imm at any digit-5 arm; SBB/ADC digits, missing
    or R-extended REX prefixes and truncated tails refuse loudly. -/

/-- The width gate admits SUB-imm exactly at b64. -/
theorem subImm_breite_nur_b64 (b : Breite) (dst : Register)
    (imm : BitVec 32) :
    immBreiteOk (.subI dst imm) b = (b == .b64) := by
  cases b <;> rfl

/-- Digit 5 at b32 refuses in every ModRM arm (wide and compact). -/
theorem subkompakt_32_verweigert (bBit : Nat) (m : Byte) (t : List Byte)
    (wide : Bool) (hmod : byteNat m / 64 == 3)
    (hdig : byteNat m / 8 % 8 = 5) :
    decodeIntHwImmModrm .b32 wide bBit (m :: t) = none := by
  simp only [decodeIntHwImmModrm]
  rw [if_pos hmod]
  cases hc : codeReg (bBit * 8 + byteNat m % 8) with
  | none => rfl
  | some rd =>
    rw [hdig]
    cases wide <;> rfl

/-- SBB digit /3 refuses on the compact opcode. -/
theorem subkompakt_sbb_verweigert :
    decodeIntHwImm
      [natByte 72, natByte 131, natByte 216, natByte 1] = none := by
  decide

/-- ADC digit /2 refuses on the compact opcode. -/
theorem subkompakt_adc_verweigert :
    decodeIntHwImm
      [natByte 72, natByte 131, natByte 208, natByte 1] = none := by
  decide

/-- No REX prefix, no row: a bare 83 /5 is refused. -/
theorem subkompakt_ohne_rex_verweigert :
    decodeIntHwImm [natByte 131, natByte 232, natByte 1] = none := by
  decide

/-- REX.R is not a canonical prefix of this row. -/
theorem subkompakt_rex_r_verweigert :
    decodeIntHwImm
      [natByte 76, natByte 131, natByte 232, natByte 1] = none := by
  decide

/-- W=0 compact bytes refuse: no 32-bit SUB-imm exists. -/
theorem subkompakt_w0_kompakt_verweigert :
    decodeIntHwImm
      [natByte 64, natByte 131, natByte 232, natByte 1] = none := by
  decide

/-- W=0 wide bytes refuse: no 32-bit SUB-imm exists. -/
theorem subkompakt_w0_weit_verweigert :
    decodeIntHwImm [natByte 64, natByte 129, natByte 232,
      natByte 1, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- A compact SUB without its immediate byte is truncated. -/
theorem subkompakt_kurz_verweigert :
    decodeIntHwImm [natByte 72, natByte 131, natByte 232] = none := by
  decide

/- CUTS (skeleton; extended below):
   No hardware correspondence beyond the stated row; no source, TSO,
   cost or whole-image claim.
-/

#print axioms pin_sub_kompakt

end Gabbro.Grammatik.X86
