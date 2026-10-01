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

/-- Helper-level acceptance never decides final validation: site
    admissibility (code-operand field versus standalone data field,
    IMAGE-ABI sec. 4) needs the checked image plus the decoder proof,
    so this flag stays `false` and no helper fact admits a site. (No
    local inductive is declared for the two classes: the image-mapping
    lane owns that vocabulary, and a second model of it here would
    collide with it.) -/
def relAnnahmeEndgueltig : Bool := false

/-- No helper fact admits a site: complete relocation acceptance is
    explicitly OPEN/refused here. -/
theorem relAnnahme_offen : relAnnahmeEndgueltig = false := by rfl

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

/-! ## 4. Finite byte patching with range and disjointness checks. -/

/-- Checked patch: replace `bs.length` bytes at file offset `off`.
    `none` refuses an overrunning site, including an empty patch past
    the end. This is helper arithmetic only: whether `off` is a
    code-operand field or a declared data field is decided by the
    checked image-plus-decoder proof, never by the caller. -/
def patchAt : List Byte → Nat → List Byte → Option (List Byte)
  | img, off, [] => if off ≤ img.length then some img else none
  | [], _, _ :: _ => none
  | _ :: rest, 0, y :: ys => (patchAt rest 0 ys).map (y :: ·)
  | x :: rest, n + 1, b :: bs => (patchAt rest n (b :: bs)).map (x :: ·)

/-- A successful patch lies inside the image: exact range premise. -/
theorem patchAt_bereich (img : List Byte) (off : Nat) (bs : List Byte)
    (out : List Byte) (h : patchAt img off bs = some out) :
    off + bs.length ≤ img.length := by
  induction img generalizing off bs out with
  | nil =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ ([] : List Byte).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        simpa using hc
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons b bs =>
      simp only [patchAt] at h
      cases h
  | cons x rest ih =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ (x :: rest).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        simpa using hc
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons y ys =>
      cases off with
      | zero =>
        simp only [patchAt] at h
        cases hres : patchAt rest 0 ys with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          have hr := ih 0 ys tail hres
          simp only [List.length_cons] at hr ⊢
          omega
      | succ n =>
        simp only [patchAt] at h
        cases hres : patchAt rest n (y :: ys) with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          have hr := ih n (y :: ys) tail hres
          simp only [List.length_cons] at hr ⊢
          omega

/-- A successful patch keeps the image length. -/
theorem patchAt_laenge (img : List Byte) (off : Nat) (bs : List Byte)
    (out : List Byte) (h : patchAt img off bs = some out) :
    out.length = img.length := by
  induction img generalizing off bs out with
  | nil =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ ([] : List Byte).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        rfl
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons b bs =>
      simp only [patchAt] at h
      cases h
  | cons x rest ih =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ (x :: rest).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        rfl
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons y ys =>
      cases off with
      | zero =>
        simp only [patchAt] at h
        cases hres : patchAt rest 0 ys with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          have hr := ih 0 ys tail hres
          simp only [List.length_cons, hr]
      | succ n =>
        simp only [patchAt] at h
        cases hres : patchAt rest n (y :: ys) with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          have hr := ih n (y :: ys) tail hres
          simp only [List.length_cons, hr]

/-- Patched site bytes are exactly the patch bytes. -/
theorem patchAt_stelle (img : List Byte) (off : Nat) (bs : List Byte)
    (out : List Byte) (h : patchAt img off bs = some out)
    (k : Nat) (hk : k < bs.length) :
    out[off + k]? = bs[k]? := by
  induction img generalizing off bs out k with
  | nil =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ ([] : List Byte).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        simp only [List.length_nil] at hk
        omega
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons b bs =>
      simp only [patchAt] at h
      cases h
  | cons x rest ih =>
    cases bs with
    | nil =>
      simp only [List.length_nil] at hk
      omega
    | cons y ys =>
      cases off with
      | zero =>
        simp only [patchAt] at h
        cases hres : patchAt rest 0 ys with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          cases k with
          | zero =>
            simp only [Nat.zero_add, List.getElem?_cons_zero]
          | succ k =>
            simp only [Nat.zero_add, List.getElem?_cons_succ]
            have hih := ih 0 ys tail hres k (by simpa using hk)
            simpa only [Nat.zero_add] using hih
      | succ n =>
        simp only [patchAt] at h
        cases hres : patchAt rest n (y :: ys) with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          have e : n + 1 + k = (n + k) + 1 := by omega
          rw [e]
          simp only [List.getElem?_cons_succ]
          exact ih n (y :: ys) tail hres k hk

/-- Bytes outside the site keep their image bytes. -/
theorem patchAt_rahmen (img : List Byte) (off : Nat) (bs : List Byte)
    (out : List Byte) (h : patchAt img off bs = some out)
    (i : Nat) (haussen : ∀ k, k < bs.length → i ≠ off + k) :
    out[i]? = img[i]? := by
  induction img generalizing off bs out i with
  | nil =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ ([] : List Byte).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        rfl
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons b bs =>
      simp only [patchAt] at h
      cases h
  | cons x rest ih =>
    cases bs with
    | nil =>
      by_cases hc : off ≤ (x :: rest).length
      · simp only [patchAt, if_pos hc] at h
        cases h
        rfl
      · simp only [patchAt, if_neg hc] at h
        cases h
    | cons y ys =>
      cases off with
      | zero =>
        simp only [patchAt] at h
        cases hres : patchAt rest 0 ys with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          cases i with
          | zero =>
            have hlt : (0 : Nat) < (y :: ys).length := by simp
            have hne := haussen 0 hlt
            rw [Nat.add_zero] at hne
            exact False.elim (absurd rfl hne)
          | succ j =>
            simp only [List.getElem?_cons_succ]
            exact ih 0 ys tail hres j (fun k hk => by
              have hkk : k + 1 < (y :: ys).length := by
                rw [List.length_cons]
                omega
              have hne := haussen (k + 1) hkk
              omega)
      | succ n =>
        simp only [patchAt] at h
        cases hres : patchAt rest n (y :: ys) with
        | none =>
          simp only [hres, Option.map_none] at h
          cases h
        | some tail =>
          simp only [hres, Option.map_some] at h
          cases h
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero]
          | succ j =>
            simp only [List.getElem?_cons_succ]
            exact ih n (y :: ys) tail hres j (fun k hk hcontra => by
              have hne := haussen k hk
              omega)

/-! ## 5. Disjoint double patches and relocation-shaped patching. -/

/-- Two Nat-interval sites are disjoint: neither overlaps the other. -/
def disjunktStellen (o1 l1 o2 l2 : Nat) : Prop :=
  o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1

instance (o1 l1 o2 l2 : Nat) :
    Decidable (disjunktStellen o1 l1 o2 l2) := by
  unfold disjunktStellen
  infer_instance

/-- Two patches in one step: overlapping sites are refused outright,
    so a code-operand site can never silently clobber a neighbour. -/
def patchZwei (img : List Byte) (o1 : Nat) (b1 : List Byte)
    (o2 : Nat) (b2 : List Byte) : Option (List Byte) :=
  if disjunktStellen o1 b1.length o2 b2.length then
    match patchAt img o1 b1 with
    | some m => patchAt m o2 b2
    | none => none
  else none

/-- Overlapping sites are refused, never merged. -/
theorem patchZwei_verweigert (img : List Byte) (o1 : Nat) (b1 : List Byte)
    (o2 : Nat) (b2 : List Byte)
    (h : ¬ disjunktStellen o1 b1.length o2 b2.length) :
    patchZwei img o1 b1 o2 b2 = none := by
  unfold patchZwei
  rw [if_neg h]

/-- The first site's bytes survive a disjoint second patch. -/
theorem patchZwei_erhaelt_erste (img m out : List Byte)
    (o1 : Nat) (b1 : List Byte) (o2 : Nat) (b2 : List Byte)
    (h1 : patchAt img o1 b1 = some m)
    (h2 : patchAt m o2 b2 = some out)
    (hd : disjunktStellen o1 b1.length o2 b2.length)
    (k : Nat) (hk : k < b1.length) :
    out[o1 + k]? = b1[k]? := by
  rcases hd with hd | hd
  · have hne : ∀ j, j < b2.length → o1 + k ≠ o2 + j := by
      intro j hj
      omega
    rw [patchAt_rahmen m o2 b2 out h2 _ hne,
      patchAt_stelle img o1 b1 m h1 k hk]
  · have hne : ∀ j, j < b2.length → o1 + k ≠ o2 + j := by
      intro j hj
      omega
    rw [patchAt_rahmen m o2 b2 out h2 _ hne,
      patchAt_stelle img o1 b1 m h1 k hk]

/-- A rel32 displacement patches only through its fit check. -/
def patchRel32 (img : List Byte) (off : Nat) (d : Int) : Option (List Byte) :=
  if rel32Passt d then patchAt img off (rel32Bytes d) else none

/-- A rel32 site is four bytes wide. -/
theorem rel32Bytes_laenge (d : Int) : (rel32Bytes d).length = 4 := rfl

/-- A patched rel32 site carries exactly the displacement bytes. -/
theorem patchRel32_stelle (img : List Byte) (off : Nat) (d : Int)
    (out : List Byte) (h : patchRel32 img off d = some out)
    (k : Nat) (hk : k < 4) :
    out[off + k]? = (rel32Bytes d)[k]? := by
  unfold patchRel32 at h
  split at h
  · exact patchAt_stelle img off (rel32Bytes d) out h k
      (by rwa [rel32Bytes_laenge])
  · cases h

/-- An absolute value patches at any in-range eight-byte site. -/
def patchAbs64 (img : List Byte) (off : Nat) (v : Wort) :
    Option (List Byte) :=
  patchAt img off (abs64Bytes v)

/-- An abs64 site is eight bytes wide. -/
theorem abs64Bytes_laenge (v : Wort) : (abs64Bytes v).length = 8 := rfl

/-- A patched abs64 site carries exactly the value bytes. -/
theorem patchAbs64_stelle (img : List Byte) (off : Nat) (v : Wort)
    (out : List Byte) (h : patchAbs64 img off v = some out)
    (k : Nat) (hk : k < 8) :
    out[off + k]? = (abs64Bytes v)[k]? := by
  unfold patchAbs64 at h
  exact patchAt_stelle img off (abs64Bytes v) out h k
    (by rwa [abs64Bytes_laenge])

/-! ## 6. Concrete probes: negative, boundaries, refusals, overlap. -/

/-- Negative displacement `-5`: bytes `FB FF FF FF`. -/
theorem sonde_rel32_negativ :
    rel32Bytes (-5) = [0xFB, 0xFF, 0xFF, 0xFF] := by
  decide

/-- Negative displacements decode back. -/
theorem sonde_rel32_negativ_rund :
    rel32DecOpt (rel32Bytes (-5)) = some (-5) := by
  decide

/-- Canonical `sext` agrees with the encoding on `-5`. -/
theorem sonde_sext_negativ :
    sext .b32 (BitVec.ofNat 64 4294967291) = 0xFFFFFFFFFFFFFFFB := by
  decide

/-- Upper boundary `2 ^ 31 - 1`: bytes `FF FF FF 7F`, fits. -/
theorem sonde_rel32_oben :
    rel32Bytes 2147483647 = [0xFF, 0xFF, 0xFF, 0x7F] ∧
    rel32Passt 2147483647 = true := by
  decide

/-- Lower boundary `-2 ^ 31`: bytes `00 00 00 80`, fits. -/
theorem sonde_rel32_unten :
    rel32Bytes (-2147483648) = [0x00, 0x00, 0x00, 0x80] ∧
    rel32Passt (-2147483648) = true := by
  decide

/-- Just out of range both ways: fit refused. -/
theorem sonde_rel32_ausserhalb :
    rel32Passt 2147483648 = false ∧
    rel32Passt (-2147483649) = false := by
  decide

/-- An out-of-range target patches to `none`, never to wrapped bytes. -/
theorem sonde_rel32Fuer_verweigert :
    rel32Fuer 0 2147483648 = none ∧
    rel32Fuer 10 0 = some (rel32Bytes (-10)) := by
  decide

/-- The address equation on a real backward jump (`0x1005` to `0x1000`). -/
theorem sonde_adress_gleichung :
    BitVec.ofNat 64 4096 =
      BitVec.ofNat 64 4101 + BitVec.ofNat 64 (rel32Enc64 (-5)) :=
  rel32_adress_gleichung 4101 4096 (-5) (by decide) (by decide) (by decide)

/-- Next-RIP formation on real addresses. -/
theorem sonde_next_rip :
    (BitVec.ofNat 64 4096 + BitVec.ofNat 64 5).toNat = 4101 :=
  rel32_next_rip 4096 5 (by decide) (by decide) (by decide)

/-- Absolute value bytes, little endian. -/
theorem sonde_abs64_bytes :
    abs64Bytes 0x0102030405060708 =
      [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01] := by
  decide

/-- Absolute values read back through the canonical split. -/
theorem sonde_abs64_rund :
    abs64Wort (abs64Bytes 0x0102030405060708) =
      some 0x0102030405060708 :=
  abs64_rundgang 0x0102030405060708

/-- Overlapping sites are refused. -/
theorem sonde_patchZwei_ueberlappung :
    patchZwei [0, 0, 0, 0, 0, 0, 0, 0] 1 [0xAA, 0xBB] 2 [0xCC, 0xDD] =
      none := by
  decide

/-- Disjoint sites patch to the exact combined bytes. -/
theorem sonde_patchZwei_disjunkt :
    patchZwei [0, 0, 0, 0, 0, 0, 0, 0] 0 [0xAA] 4 [0xBB] =
      some [0xAA, 0, 0, 0, 0xBB, 0, 0, 0] := by
  decide

/-- An overrunning site is refused. -/
theorem sonde_patchAt_ueberlauf :
    patchAt [0, 0, 0] 2 [0xAA, 0xBB] = none := by
  decide

/- CUTS:
   - Proved here: rel32 fit/encode/sign-extending-decode round-trip,
     canonical next-RIP formation and target equation, checked
     displacement with out-of-range refusal, abs64 values with
     read-back, finite byte patching with range/length/site/frame
     facts, disjoint double patches with overlap refusal, and concrete
     negative/boundary/out-of-range/overlap probes.
   - Explicitly OPEN (refused at helper level by `relAnnahme_offen`):
     code-operand versus standalone-data site admissibility, which
     needs the checked image plus the decoder proof (IMAGE-ABI sec. 4);
     caller-claimed instruction starts and relocation kinds are never
     trusted here.
   - No loader or linker assumption: `relocs` handling, load bias,
     entry states and mapping equality belong to the image validator.
   - No final-byte source claim: per-instruction correspondence,
     control-target obligations, ABI checks, concurrency refinement
     and cost transfer are separate wave-B obligations.
   - Finding: the modular target equation needs no wrap premises
     (wrap-consistent by construction); exact no-wrap premises live
     only at next-RIP formation (`rel32_next_rip`).
-/

#print axioms relAnnahme_offen
#print axioms rel32_rundgang
#print axioms rel32_adress_gleichung
#print axioms rel32_next_rip
#print axioms rel32Fuer_verweigert
#print axioms rel32Fuer_trifft
#print axioms abs64_rundgang
#print axioms patchAt_bereich
#print axioms patchAt_laenge
#print axioms patchAt_stelle
#print axioms patchAt_rahmen
#print axioms patchZwei_verweigert
#print axioms patchZwei_erhaelt_erste
#print axioms patchRel32_stelle
#print axioms patchAbs64_stelle
#print axioms sonde_rel32_negativ
#print axioms sonde_adress_gleichung
#print axioms sonde_patchZwei_ueberlappung

end Gabbro.Grammatik.X86
