/-
  File:      Grammatik/X86/Ganzzahl.lean
  Subject:   Remaining integer families over canonical Wort/Breite (lane 282).

  Extension helpers for the SAME x86-64 target: AND/OR/NOT, multiply
  low/high halves, checked division/remainder, masked shifts, extension
  reuse. Reuses trunc/sext from Wort.lean; no new word/register/state
  types, no Befehl change. Undefined flags are never set to false: AF is
  Option-none, other undefined flags are left unconstrained behind an
  explicit flag-validity relation.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Width-truncated AND. -/
def andB (b : Breite) (x y : Wort) : Wort := trunc b (x &&& y)

/-- Width-truncated OR. -/
def orB (b : Breite) (x y : Wort) : Wort := trunc b (x ||| y)

/-- Width-truncated NOT. -/
def notB (b : Breite) (x : Wort) : Wort := trunc b (~~~x)

/-- 64-bit AND with flags; CF/OF cleared, AF undefined. -/
def and64 (x y : Wort) : Wort × Flags :=
  let r := x &&& y
  (r, Flags.mk false (parityEven r) none (zfTest r) (sfTest r) false)

/-- 64-bit OR with flags; CF/OF cleared, AF undefined. -/
def or64 (x y : Wort) : Wort × Flags :=
  let r := x ||| y
  (r, Flags.mk false (parityEven r) none (zfTest r) (sfTest r) false)

/- CUTS (skeleton):
   Multiply/division/shift/extension/range/flag-validity/lemmas/probes
   are open. No encoding/source/cost/TSO bridge is claimed.
-/

/-! ## 1. Multiply: low half and unsigned/signed high halves.

    Low half is modular at the named width (signed and unsigned agree
    there). High halves are the upper bits of the full double-width
    product: unsigned via `toNat`, signed via the signed value `sVal`
    with floor division by `2 ^ b.bits`, wrapped into a word. -/

/-- Modular low half of the product at width `b`. -/
def mulLow (b : Breite) (x y : Wort) : Wort := trunc b (x * y)

/-- Unsigned high half of the `b`-bit product, zero-extended. -/
def mulHighU (b : Breite) (x y : Wort) : Wort :=
  BitVec.ofNat 64 (((trunc b x).toNat * (trunc b y).toNat) / 2 ^ b.bits)

/-- Signed value of the truncated operand (two's complement). -/
def sVal (b : Breite) (w : Wort) : Int :=
  let n := (trunc b w).toNat
  if negB b w then (n : Int) - ((2 ^ b.bits : Nat) : Int) else (n : Int)

/-- Signed high half of the `b`-bit product (arithmetic upper bits). -/
def mulHighS (b : Breite) (x y : Wort) : Wort :=
  let p := sVal b x * sVal b y
  let hi := p.ediv (((2 ^ b.bits : Nat) : Int))
  BitVec.ofNat 64 (hi.emod (((2 ^ 64 : Nat) : Int))).toNat

/-! ## 2. Checked division and remainder.

    Unsigned division refuses only divide-by-zero. Signed division
    refuses divide-by-zero AND the `INT_MIN / -1` quotient overflow
    (the quotient would need one more bit than the width holds).
    Results are `(quotient, remainder)` words at the named width. -/

/-- Division refusal cause. -/
inductive TeilFehler where
  | durchNull
  | quotientUeberlauf
  deriving DecidableEq, Repr

/-- Unsigned division at width `b`: `none` exactly on divisor zero. -/
def divU (b : Breite) (x y : Wort) : Option (Wort × Wort) :=
  let xn := (trunc b x).toNat
  let yn := (trunc b y).toNat
  if yn = 0 then none
  else some (trunc b (BitVec.ofNat 64 (xn / yn)),
    trunc b (BitVec.ofNat 64 (xn % yn)))

/-- Signed minimum of width `b` as an integer (`-2 ^ (bits-1)`). -/
def sMin (b : Breite) : Int := - (((2 ^ (b.bits - 1) : Nat) : Int))

/-- Signed division at width `b`: `none` on divisor zero or the
    `sMin / -1` quotient overflow. -/
def divS (b : Breite) (x y : Wort) : Option (Wort × Wort) :=
  let xn := sVal b x
  let yn := sVal b y
  if yn = 0 then none
  else if xn = sMin b ∧ yn = -1 then none
  else
    let q := xn.tdiv yn
    let r := xn.tmod yn
    some (trunc b (BitVec.ofNat 64 (q.emod ((2 ^ 64 : Nat) : Int)).toNat),
      trunc b (BitVec.ofNat 64 (r.emod ((2 ^ 64 : Nat) : Int)).toNat))

/-! ## 3. Shifts with architectural count masking.

    Hardware masks the count (5 bits for 8/16/32-bit operands, 6 bits
    for 64-bit operands), so a shift by the width or by a large count
    is a shift by the masked count, never a refusal. `shlB` inserts
    zeros, `shrB` is logical (zeros), `sarB` repeats the sign bit. -/

/-- Masked shift count: `% 32` below 64 bits, `% 64` at 64 bits. -/
def schiebeZaehler (b : Breite) (c : Nat) : Nat :=
  match b with
  | .b64 => c % 64
  | _ => c % 32

/-- Left shift at width `b` with masked count. -/
def shlB (b : Breite) (x : Wort) (c : Nat) : Wort :=
  trunc b (BitVec.ofNat 64 (((trunc b x).toNat * 2 ^ schiebeZaehler b c) % 2 ^ 64))

/-- Logical right shift at width `b` with masked count. -/
def shrB (b : Breite) (x : Wort) (c : Nat) : Wort :=
  BitVec.ofNat 64 ((trunc b x).toNat / 2 ^ schiebeZaehler b c)

/-- Arithmetic right shift at width `b` with masked count. -/
def sarB (b : Breite) (x : Wort) (c : Nat) : Wort :=
  let k := schiebeZaehler b c
  let q := (sVal b x).ediv (((2 ^ k : Nat) : Int))
  trunc b (BitVec.ofNat 64 (q.emod (((2 ^ 64 : Nat) : Int))).toNat)

/-! ## 4. Flag validity: undefined is unconstrained, never false.

    AND/OR keep the `xor64` discipline (CF/OF cleared, AF `none`).
    MUL/SHIFT leave several flags architecturally undefined, and `Flags`
    stores all but AF as `Bool`, so returning a `Flags` would force an
    arbitrary defined value. Instead each operation returns its defined
    evidence (MUL carry, shift carry plus an optional overflow valid
    only for a one-bit shift) and a VALIDITY RELATION pins only the
    defined flags, leaving the rest unconstrained. -/

/-- Validity for logic results: CF/OF cleared, AF undefined. -/
def LogikGueltig (r : Wort) (f : Flags) : Prop :=
  f.cf = false ∧ f.of = false ∧ f.af = none ∧
  f.zf = zfTest r ∧ f.sf = sfTest r ∧ f.pf = parityEven r

/-- MUL defined evidence: the carry flag (CF = OF = high half nonzero). -/
def mulTrag (b : Breite) (x y : Wort) : Bool :=
  decide (mulHighU b x y ≠ 0)

/-- Validity for a MUL flag snapshot: CF/OF pinned, AF undefined,
    SF/ZF/PF unconstrained (existentially, never forced false). -/
def MulGueltig (b : Breite) (x y : Wort) (f : Flags) : Prop :=
  f.cf = mulTrag b x y ∧ f.of = mulTrag b x y ∧ f.af = none

/-- Shift defined evidence: carry out plus optional overflow (only a
    one-bit shift defines OF; otherwise it is undefined). -/
structure SchiebeNachweis where
  ergebnis : Wort
  trag : Bool
  ueberlauf : Option Bool
  deriving DecidableEq, Repr

/-- Validity for a shift flag snapshot: result flags pinned, CF pinned,
    OF pinned exactly when the count is one, AF undefined; for wider
    counts OF is unconstrained. -/
def SchiebeGueltig (s : SchiebeNachweis) (c : Nat) (f : Flags) : Prop :=
  f.cf = s.trag ∧ f.af = none ∧
  f.zf = zfTest s.ergebnis ∧ f.sf = sfTest s.ergebnis ∧
  f.pf = parityEven s.ergebnis ∧
  (schiebeZaehler .b64 c = 1 → f.of = s.ueberlauf.getD f.of) ∧
  (s.ueberlauf = none → schiebeZaehler .b64 c ≠ 1)

/-! ## 5. Source range arithmetic stays distinct from modular results.

    Source types carry Nat/Int RANGES (unbounded mathematical sums);
    the target computes MODULAR words. The two meet only through an
    explicit range check: a source sum fits exactly when it is below
    `2 ^ b.bits` (unsigned) or inside the signed interval. -/

/-- Unsigned source sum fits the width. -/
def passtU (b : Breite) (a c : Nat) : Prop := a + c < 2 ^ b.bits

/-- Signed source sum fits the width. -/
def passtS (b : Breite) (a c : Int) : Prop :=
  -(((2 ^ (b.bits - 1) : Nat) : Int)) ≤ a + c ∧
  a + c < (((2 ^ (b.bits - 1) : Nat) : Int))

/-! ## 6. Generic result, range and refusal facts. -/

/-- Full-width AND is plain machine AND. -/
theorem andB_b64 (x y : Wort) : andB .b64 x y = x &&& y := by
  simp [andB, trunc_b64]

/-- Full-width OR is plain machine OR. -/
theorem orB_b64 (x y : Wort) : orB .b64 x y = x ||| y := by
  simp [orB, trunc_b64]

/-- Full-width NOT is plain machine NOT. -/
theorem notB_b64 (x : Wort) : notB .b64 x = ~~~x := by
  simp [notB, trunc_b64]

/-- AND clears CF. -/
theorem and64_cf (x y : Wort) : (and64 x y).2.cf = false := by
  simp [and64]

/-- AND clears OF. -/
theorem and64_of (x y : Wort) : (and64 x y).2.of = false := by
  simp [and64]

/-- AND leaves AF undefined (`none`, never false). -/
theorem and64_af (x y : Wort) : (and64 x y).2.af = none := by
  simp [and64]

/-- OR clears CF. -/
theorem or64_cf (x y : Wort) : (or64 x y).2.cf = false := by
  simp [or64]

/-- OR clears OF. -/
theorem or64_of (x y : Wort) : (or64 x y).2.of = false := by
  simp [or64]

/-- OR leaves AF undefined (`none`, never false). -/
theorem or64_af (x y : Wort) : (or64 x y).2.af = none := by
  simp [or64]

/-- The AND flags satisfy the logic validity relation. -/
theorem and64_gueltig (x y : Wort) :
    LogikGueltig (and64 x y).1 (and64 x y).2 := by
  simp [and64, LogikGueltig]

/-- The OR flags satisfy the logic validity relation. -/
theorem or64_gueltig (x y : Wort) :
    LogikGueltig (or64 x y).1 (or64 x y).2 := by
  simp [or64, LogikGueltig]

/-- Full-width low multiply is plain machine multiply. -/
theorem mulLow_b64 (x y : Wort) : mulLow .b64 x y = x * y := by
  simp [mulLow, trunc_b64]

/-- Zero times anything has zero high half (unsigned). -/
theorem mulHighU_null_links (b : Breite) (y : Wort) :
    mulHighU b 0 y = 0 := by
  simp [mulHighU, trunc]

/-- Zero times anything has zero low half. -/
theorem mulLow_null_links (b : Breite) (y : Wort) :
    mulLow b 0 y = 0 := by
  simp [mulLow, trunc]

/-- MUL carry reads the high half. -/
theorem mulTrag_heisst (b : Breite) (x y : Wort) :
    mulTrag b x y = true ↔ mulHighU b x y ≠ 0 := by
  simp [mulTrag]

/-- Unsigned division refuses exactly on divisor zero. -/
theorem divU_verweigert_bei_null (b : Breite) (x y : Wort)
    (h : (trunc b y).toNat = 0) : divU b x y = none := by
  simp [divU, h]

/-- Unsigned division answers on nonzero divisor. -/
theorem divU_antwortet_bei_nichtnull (b : Breite) (x y : Wort)
    (h : (trunc b y).toNat ≠ 0) :
    ∃ q r, divU b x y = some (q, r) := by
  simp [divU, h]

/-- Signed division refuses on divisor zero. -/
theorem divS_verweigert_bei_null (b : Breite) (x y : Wort)
    (h : sVal b y = 0) : divS b x y = none := by
  simp [divS, h]

/-- Signed division refuses the `sMin / -1` quotient overflow. -/
theorem divS_verweigert_min_durch_neg1 (b : Breite) (x y : Wort)
    (h1 : sVal b x = sMin b) (h2 : sVal b y = -1) :
    divS b x y = none := by
  simp [divS, h1, h2]

/-- Masked 64-bit counts stay below 64. -/
theorem schiebeZaehler_b64_schranke (c : Nat) :
    schiebeZaehler .b64 c < 64 :=
  Nat.mod_lt c (by decide)

/-- Masked narrow counts stay below 32. -/
theorem schiebeZaehler_schmal_schranke (b : Breite) (c : Nat)
    (h : b ≠ .b64) : schiebeZaehler b c < 32 := by
  cases b with
  | b64 => exact absurd rfl h
  | b8 => exact Nat.mod_lt c (by decide)
  | b16 => exact Nat.mod_lt c (by decide)
  | b32 => exact Nat.mod_lt c (by decide)

/-- Shift by zero keeps the word at full width (left). -/
theorem shlB_b64_null (x : Wort) : shlB .b64 x 0 = x := by
  have hx : (trunc .b64 x).toNat = x.toNat := by rw [trunc_b64]
  unfold shlB schiebeZaehler
  simp only [show (0 % 64) = 0 from rfl,
    show (2 ^ 0 : Nat) = 1 from rfl, Nat.mul_one, hx]
  rw [trunc_b64]
  apply BitVec.eq_of_toNat_eq
  have hmod : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt x.isLt
  simp [hmod]

/-- Shift by zero keeps the word at full width (logical right). -/
theorem shrB_b64_null (x : Wort) : shrB .b64 x 0 = x := by
  have hx : (trunc .b64 x).toNat = x.toNat := by rw [trunc_b64]
  unfold shrB schiebeZaehler
  simp only [show (0 % 64) = 0 from rfl,
    show (2 ^ 0 : Nat) = 1 from rfl, Nat.div_one, hx]
  apply BitVec.eq_of_toNat_eq
  simp

/-- 64-bit counts wrap every 64: the mask period. -/
theorem schiebeZaehler_periode_b64 (c : Nat) :
    schiebeZaehler .b64 (c + 64) = schiebeZaehler .b64 c := by
  simp [schiebeZaehler]

/-- A 64-bit left shift by 64 is a shift by zero (masking, not refusal). -/
theorem shlB_b64_breite_ist_null (x : Wort) :
    shlB .b64 x 64 = shlB .b64 x 0 := by
  unfold shlB schiebeZaehler
  simp only [show (64 % 64) = 0 from rfl]

/-- A MUL flag snapshot always exists (undefined flags arbitrary). -/
theorem mul_gueltig_existenz (b : Breite) (x y : Wort) :
    ∃ f : Flags, MulGueltig b x y f :=
  ⟨Flags.mk (mulTrag b x y) true none true true (mulTrag b x y),
    rfl, rfl, rfl⟩

/-- Undefined MUL flags are unconstrained: two valid snapshots differ. -/
theorem mul_unbestimmt_unbeschraenkt (b : Breite) (x y : Wort) :
    ∃ f1 f2 : Flags, MulGueltig b x y f1 ∧ MulGueltig b x y f2 ∧
      f1.sf ≠ f2.sf :=
   ⟨Flags.mk (mulTrag b x y) true none true true (mulTrag b x y),
   Flags.mk (mulTrag b x y) false none false false (mulTrag b x y),
   ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, by simp⟩

/-- A shift flag snapshot exists away from the one-bit overflow case. -/
theorem schiebe_gueltig_existenz (s : SchiebeNachweis) (c : Nat)
    (h : s.ueberlauf = none) (h2 : schiebeZaehler .b64 c ≠ 1) :
    ∃ f : Flags, SchiebeGueltig s c f := by
  refine ⟨Flags.mk s.trag (parityEven s.ergebnis) none
    (zfTest s.ergebnis) (sfTest s.ergebnis) false, rfl, rfl, rfl, rfl,
    rfl, ?_, fun _ => h2⟩
  · intro _
    rw [h]
    rfl

/-- A fitting unsigned source sum is below the width bound. -/
theorem passtU_heisst (b : Breite) (a c : Nat)
    (h : passtU b a c) : a + c < 2 ^ b.bits := h

/-- A fitting signed source sum lies in the signed interval. -/
theorem passtS_heisst (b : Breite) (a c : Int)
    (h : passtS b a c) :
    -(((2 ^ (b.bits - 1) : Nat) : Int)) ≤ a + c ∧
    a + c < (((2 ^ (b.bits - 1) : Nat) : Int)) := h

/-! ## 7. Boundary probes (finite concrete checks via `decide`). -/

/-- Logic: disjoint AND is zero, OR fills, narrow NOT clears. -/
theorem probe_logik :
    andB .b64 0xF0 0x0F = 0 ∧ orB .b64 0xF0 0x0F = 0xFF ∧
    notB .b8 0xFF = 0 := by
  decide

/-- Logic flags: AND of disjoint nibbles sets ZF, AF stays undefined. -/
theorem probe_logik_flags :
    (and64 0xF0 0x0F).2.zf = true ∧
    (and64 0xF0 0x0F).2.af = none ∧
    (or64 0xF0 0x0F).1 = 0xFF := by
  decide

/-- Unsigned high multiply: `max * max` overflows into `max - 1`. -/
theorem probe_mul_hoch_u :
    mulHighU .b64 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF =
      0xFFFFFFFFFFFFFFFE ∧
    mulLow .b64 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 1 ∧
    mulHighU .b8 0xFF 0xFF = 0xFE := by
  decide

/-- Signed high multiply differs: `-1 * -1` has zero high half. -/
theorem probe_mul_hoch_s :
    mulHighS .b8 0xFF 0xFF = 0 ∧ sVal .b8 0xFF = -1 ∧
    mulLow .b8 0xFF 0xFF = 1 := by
  decide

/-- Signed division refuses `INT_MIN / -1` (quotient overflow). -/
theorem probe_div_s_ueberlauf :
    divS .b64 0x8000000000000000 0xFFFFFFFFFFFFFFFF = none := by
  decide

/-- Division answers and refusals at small values. -/
theorem probe_div_antwort :
    divS .b64 10 2 = some (5, 0) ∧ divU .b64 7 3 = some (2, 1) ∧
    divU .b8 5 0 = none ∧ divS .b16 7 0 = none := by
  decide

/-- Shifts: zero count, width count (masked to zero) and large counts. -/
theorem probe_schiebung :
    shlB .b64 1 3 = 8 ∧ shlB .b64 1 64 = 1 ∧
    shlB .b8 1 33 = 2 ∧ shrB .b64 0x8000000000000000 63 = 1 := by
  decide

/-- Arithmetic shift repeats the sign bit. -/
theorem probe_sar :
    sarB .b64 0xFFFFFFFFFFFFFFFF 63 = 0xFFFFFFFFFFFFFFFF ∧
    sarB .b8 0x80 7 = 0xFF ∧ shrB .b8 0x80 7 = 1 := by
  decide

/-- Extension reuse: `0x80` fills, narrow zero extension keeps. -/
theorem probe_erweiterung :
    sext .b8 0x80 = 0xFFFFFFFFFFFFFF80 ∧ zext .b8 0xFF = 0xFF := by
  decide

/-- Source range vs modular target: 255 fits eight bits, 256 does not. -/
theorem probe_bereich : passtU .b8 200 55 ∧ ¬ passtU .b8 200 56 := by
  constructor
  · show 200 + 55 < 2 ^ Breite.bits .b8
    decide
  · show ¬ 200 + 56 < 2 ^ Breite.bits .b8
    decide

/-! ## 8. Memory probe: a computed shift result stored and read back.

    The value is produced by `shlB` (section 3), written through the
    canonical permission-checked `write64` and read back through
    `read64`; the store observably changes memory. This keeps the
    helpers executable against real byte memory (WELLE-A: a
    memory-changing witness is required; per-access TSO granularity
    stays with the bridge lane). -/

/-- The witness memory after storing the computed `1 << 3`. -/
def sondenSpeicherNach : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 (shlB .b64 1 3) }

/-- A computed shift result goes through memory and changes it. -/
theorem ganzzahl_speicher_sonde :
    ∃ (m m' : Speicher) (a : Adresse),
      write64 m a (shlB .b64 1 3) = some m' ∧
      read64 m' a = some (shlB .b64 1 3) ∧
      m.bytes a ≠ m'.bytes a := by
  refine ⟨zeugenSpeicher, sondenSpeicherNach, 0, ?_, ?_, ?_⟩
  · unfold write64
    have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
    rfl
  · exact read64_nach_write64 zeugenSpeicher _ 0 (shlB .b64 1 3)
      (by unfold write64
          have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
          rw [if_pos hc]
          rfl) rfl
  · have hhit := writeBytesN_hit zeugenSpeicher 0 (shlB .b64 1 3)
      8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 (shlB .b64 1 3) 0
    unfold writeBytes
    rw [hhit]
    decide

/- CUTS:
   - No instruction encoding or decoding: nothing here claims which
     bytes encode AND/OR/MUL/DIV/SHIFT forms; Codec (lane 279) owns that.
   - No source correspondence: `passtU`/`passtS` only name when an
     unbounded source sum fits a width; no source lowering, duty reuse
     or range-proof transfer is established (bridge lane 277's business).
   - No cost transfer: shift/mul/div latency or throughput is not modelled.
   - No TSO/concurrency bridge: all facts are sequential over one word
     or one `Speicher`; per-access granularity, alignment/tearing and the
     GX refinement stay with the TSO lane (274/284).
   - No hardware verification: the 5-bit/6-bit count mask, the
     `INT_MIN / -1` fault, the MUL carry rule and the flag-validity
     relations are STATED executable semantics, not verified against
     silicon; the even-parity reading of PF is inherited from Wort.lean.
   - Narrow shifts use one uniform `% 32` mask; any per-form hardware
     deviation is open and must be settled by the encoding review.
   - This file adds no new source-language construct or checker rule:
     no diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms andB
#print axioms orB
#print axioms notB
#print axioms mulLow
#print axioms mulHighU
#print axioms mulHighS
#print axioms divU
#print axioms divS
#print axioms shlB
#print axioms shrB
#print axioms sarB
#print axioms mulTrag_heisst
#print axioms divS_verweigert_min_durch_neg1
#print axioms schiebe_gueltig_existenz
#print axioms probe_mul_hoch_u
#print axioms probe_div_s_ueberlauf
#print axioms probe_schiebung
#print axioms probe_sar
#print axioms ganzzahl_speicher_sonde

end Gabbro.Grammatik.X86
