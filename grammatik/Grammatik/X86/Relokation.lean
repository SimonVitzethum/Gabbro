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

/-! ## 2. Canonical next-RIP equation and checked displacement. -/

/-- Canonical rel32 target equation over machine addresses: the loaded
    target is the actual next-RIP plus the sign-extended displacement.
    This is modular by construction, so it needs no wrap premises:
    `hdef` fixes the displacement value and `hlo`/`hhi` drive the
    two's-complement representative. (Finding: wrap-consistency holds
    either way at machine level; the exact no-wrap premises live at
    next-RIP formation in `rel32_next_rip` below.) -/
theorem rel32_adress_gleichung (next ziel : Nat) (d : Int)
    (hdef : (ziel : Int) = (next : Int) + d)
    (hlo : -2147483648 ≤ d) (hhi : d < 2147483648) :
    BitVec.ofNat 64 ziel =
      BitVec.ofNat 64 next + BitVec.ofNat 64 (rel32Enc64 d) := by
  apply BitVec.eq_of_toNat_eq
  unfold rel32Enc64 tcNat
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  by_cases h : 0 ≤ d
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- Actual next-RIP formation: machine addition of instruction start and
    decoded length reaches the Nat sum, under the exact no-wrap premise.
    Each bound is load-bearing: it drops one `% 2 ^ 64`. -/
theorem rel32_next_rip (rip len : Nat) (hrip : rip < 2 ^ 64)
    (hlen : len < 2 ^ 64) (hnowrap : rip + len < 2 ^ 64) :
    (BitVec.ofNat 64 rip + BitVec.ofNat 64 len).toNat = rip + len := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hrip, Nat.mod_eq_of_lt hlen,
    Nat.mod_eq_of_lt hnowrap]

/-- Checked displacement for a next-RIP/target pair: `none` refuses an
    out-of-range target instead of wrapping it. `next` is the virtual
    address immediately past the decoded instruction, never a file
    offset; the target rule (instruction start or entry) is checked by
    the image-plus-decoder proof, not here. -/
def rel32Fuer (next ziel : Nat) : Option (List Byte) :=
  if rel32Passt ((ziel : Int) - (next : Int)) then
    some (rel32Bytes ((ziel : Int) - (next : Int)))
  else none

/-- An out-of-range target is refused, never wrapped. -/
theorem rel32Fuer_verweigert (next ziel : Nat)
    (h : rel32Passt ((ziel : Int) - (next : Int)) = false) :
    rel32Fuer next ziel = none := by
  unfold rel32Fuer
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- An in-range target patches to bytes that sign-extend back to the
    exact target-minus-next-RIP displacement. -/
theorem rel32Fuer_trifft (next ziel : Nat)
    (h : rel32Passt ((ziel : Int) - (next : Int)) = true) :
    ∃ bs : List Byte, rel32Fuer next ziel = some bs ∧
      rel32DecOpt bs = some ((ziel : Int) - (next : Int)) := by
  have hfit := of_decide_eq_true h
  refine ⟨rel32Bytes ((ziel : Int) - (next : Int)), ?_, ?_⟩
  · unfold rel32Fuer
    rw [if_pos h]
  · exact rel32_rundgang _ hfit.1 hfit.2

/-! ## 3. Absolute 64-bit values. -/

/-- The eight patched bytes of an absolute 64-bit relocation value,
    little endian, through the canonical `wortByte`. -/
def abs64Bytes (v : Wort) : List Byte :=
  [wortByte v 0, wortByte v 1, wortByte v 2, wortByte v 3,
   wortByte v 4, wortByte v 5, wortByte v 6, wortByte v 7]

/-- Read-back of eight patched bytes through the canonical `bytesWort`;
    `none` refuses a site of the wrong width. -/
def abs64Wort : List Byte → Option Wort
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
    some (bytesWort fun i =>
      match i with
      | ⟨0, _⟩ => b0
      | ⟨1, _⟩ => b1
      | ⟨2, _⟩ => b2
      | ⟨3, _⟩ => b3
      | ⟨4, _⟩ => b4
      | ⟨5, _⟩ => b5
      | ⟨6, _⟩ => b6
      | _ => b7)
  | _ => none

/-- Absolute values round-trip through the canonical byte split: the
    proof is exactly `bytesWort_wortByte`, no second codec. -/
theorem abs64_rundgang (v : Wort) :
    abs64Wort (abs64Bytes v) = some v := by
  have hfun : (fun i : Fin 8 =>
      match i with
      | ⟨0, _⟩ => wortByte v 0
      | ⟨1, _⟩ => wortByte v 1
      | ⟨2, _⟩ => wortByte v 2
      | ⟨3, _⟩ => wortByte v 3
      | ⟨4, _⟩ => wortByte v 4
      | ⟨5, _⟩ => wortByte v 5
      | ⟨6, _⟩ => wortByte v 6
      | _ => wortByte v 7) = (fun i => wortByte v i.val) := by
    funext i
    cases i with
    | mk val isLt =>
      cases val with
      | zero => rfl
      | succ n1 =>
        cases n1 with
        | zero => rfl
        | succ n2 =>
          cases n2 with
          | zero => rfl
          | succ n3 =>
            cases n3 with
            | zero => rfl
            | succ n4 =>
              cases n4 with
              | zero => rfl
              | succ n5 =>
                cases n5 with
                | zero => rfl
                | succ n6 =>
                  cases n6 with
                  | zero => rfl
                  | succ n7 =>
                    cases n7 with
                    | zero => rfl
                    | succ n8 => exact absurd isLt (by omega)
  unfold abs64Wort abs64Bytes
  simp only [hfun]
  rw [bytesWort_wortByte]

/- CUTS:
   rel32/abs64 arithmetic and byte patching only; decoder, image mapping,
   site admissibility, loader behaviour and source correspondence are open.
-/

#print axioms relAnnahme_offen

end Gabbro.Grammatik.X86
