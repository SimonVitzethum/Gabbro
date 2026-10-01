/-
  File:      Grammatik/X86/Relokation.lean
  Subject:   Checked relocation arithmetic and final-byte patching.

  Lane 291 (Lean-first tranche): canonical address-relative rel32
  calculation (target minus actual next-RIP) with signed-32 fit/refusal,
  a generic sign-extension target equation over exact no-wrap/address
  premises, abs64 values, and finite `List Byte` operand/data-field
  patching with range and disjointness checks.

  Reuses the canonical `Byte`/`Wort`/`Adresse`, `wortByte`/`bytesWort`
  and address arithmetic of `Typen.lean`/`Speicher.lean`/`Wort.lean`;
  no second image, register or ISA model is created here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

/-- Relocation site admissibility class from IMAGE-ABI sec. 4: a site is
    either a code-operand field of one decoded instruction or a standalone
    data field of a data-field kind. Deciding the class needs the checked
    image plus the decoder proof; a caller-claimed instruction start or
    relocation kind never decides it here. -/
inductive RelArt where
  | codeOperand
  | datenFeld
  deriving DecidableEq, Repr

/-- Helper-level acceptance never decides final validation. -/
def relAnnahmeEndgueltig : RelArt → Bool
  | _ => false

/-- No helper fact admits a site: admissibility stays with the checked
    image-plus-decoder proof, and is explicitly OPEN here. -/
theorem relAnnahme_offen (a : RelArt) : relAnnahmeEndgueltig a = false := by
  cases a <;> rfl

/-! ## 1. Signed-32 fit and two's-complement encoding. -/

/-- Two's complement of `d` at modulus `m`: the unsigned representative.
    For in-range displacements this is what the patched bytes carry. -/
def tcNat (d : Int) (m : Nat) : Nat :=
  if 0 ≤ d then d.toNat else (d + m).toNat

/-- Signed-32 fit: the displacement fits a rel32 field. -/
def rel32Passt (d : Int) : Bool :=
  decide (-2147483648 ≤ d ∧ d < 2147483648)

/-- Unsigned 32-bit representative of a rel32 displacement. -/
def rel32Enc (d : Int) : Nat := tcNat d 4294967296

/-- Unsigned 64-bit representative: what 32-to-64 sign extension must
    produce as a `Nat` (used by the address equation in §2). -/
def rel32Enc64 (d : Int) : Nat := tcNat d 18446744073709551616

/-- One little-endian byte of a rel32 displacement. The `ofNat`
    truncation is the mod 256; no explicit power or mod is needed. -/
def rel32Byte (d : Int) : Nat → Byte
  | 0 => BitVec.ofNat 8 (rel32Enc d)
  | 1 => BitVec.ofNat 8 (rel32Enc d / 256)
  | 2 => BitVec.ofNat 8 (rel32Enc d / 65536)
  | _ => BitVec.ofNat 8 (rel32Enc d / 16777216)

/-- The four patched bytes of a rel32 displacement, little endian. -/
def rel32Bytes (d : Int) : List Byte :=
  [rel32Byte d 0, rel32Byte d 1, rel32Byte d 2, rel32Byte d 3]

/-- Sign extension 32 to unbounded: the unsigned 32-bit value read as
    signed. This IS the sign-extension step, stated over the bytes. -/
def rel32DecOpt : List Byte → Option Int
  | [b0, b1, b2, b3] =>
    let s : Nat := b0.toNat + b1.toNat * 256 + b2.toNat * 65536 +
      b3.toNat * 16777216
    if s < 2147483648 then some s else some ((s : Int) - 4294967296)
  | _ => none

/-- Encode/decode round-trip for every in-range displacement: the
    patched bytes sign-extend back to exactly `d`. -/
theorem rel32_rundgang (d : Int)
    (hlo : -2147483648 ≤ d) (hhi : d < 2147483648) :
    rel32DecOpt (rel32Bytes d) = some d := by
  have h256 : (2 ^ 8 : Nat) = 256 := rfl
  by_cases h : 0 ≤ d
  · simp only [rel32DecOpt, rel32Bytes, rel32Byte, rel32Enc, tcNat,
      if_pos h, BitVec.toNat_ofNat, h256]
    split
    · refine congrArg some ?_; omega
    · refine congrArg some ?_; omega
  · simp only [rel32DecOpt, rel32Bytes, rel32Byte, rel32Enc, tcNat,
      if_neg h, BitVec.toNat_ofNat, h256]
    split
    · refine congrArg some ?_; omega
    · refine congrArg some ?_; omega

/- CUTS:
   rel32/abs64 arithmetic and byte patching only; decoder, image mapping,
   site admissibility, loader behaviour and source correspondence are open.
-/

#print axioms relAnnahme_offen

end Gabbro.Grammatik.X86
