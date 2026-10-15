/-
  File:      Grammatik/X86/ShiftLogic.lean
  Subject:   Shift/logic extension helpers over the canonical words (lane 337).

  Extension helpers for the SAME x86-64 target (WORK-ALLOCATION A3): NEG plus
  per-operation flag evidence for SHL/SHR/SAR/AND/OR/NOT/NEG with the
  architectural count mask (`schiebeZaehler` from `Ganzzahl.lean`), width-
  correct flag snapshots, the signed-division-vs-shift refusal and the float
  `x - x -> 0` refusal. Value operations (`shlB`/`shrB`/`sarB`/`andB`/`orB`/
  `notB`, `and64`/`or64`) and the validity relations (`SchiebeGueltig`,
  `LogikGueltig`) are REUSED from `Ganzzahl.lean`, carry/overflow
  characterisation from `FlagBeweis.lean`; nothing is redefined here. This
  file does NOT extend `Befehl` and does NOT change `schritt` (the 14 pilot
  forms are untouched); it exposes exactly how a future shift/logic
  instruction form must present its evidence (one `SchiebeNachweis` per
  shift, one width-correct flag snapshot per logic op).
-/
import Grammatik.X86.Ganzzahl
import Grammatik.X86.FlagBeweis
import Grammatik.X86.Gleitprofil

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Width-truncated NEG (two's complement): `0 - x` at width `b`. -/
def negW (b : Breite) (x : Wort) : Wort := subB b 0 x

/-! ## 1. NEG flag evidence.

    NEG (`0 - x`) has fully defined flags: CF is the nonzero borrow, OF
    is the `sMin / -1` shape (negating the signed minimum overflows),
    AF is the nibble borrow reused from `afSub`, SF/ZF/PF read the
    width-correct result. -/

/-- NEG carry: set exactly when the truncated operand is nonzero. -/
def negTrag (b : Breite) (x : Wort) : Bool := decide (trunc b x ≠ 0)

/-- NEG overflow: set exactly when the operand is the signed minimum. -/
def negUeberlauf (b : Breite) (x : Wort) : Bool :=
  decide (sVal b x = sMin b)

/-- Validity for a NEG flag snapshot at width `b`: every flag pinned,
    with the width-correct sign `negB b` (bit 63 alone misclassifies
    narrow results). -/
def NegGueltig (b : Breite) (x : Wort) (f : Flags) : Prop :=
  f.cf = negTrag b x ∧ f.of = negUeberlauf b x ∧
  f.af = some (afSub 0 (trunc b x)) ∧
  f.zf = zfTest (negW b x) ∧ f.sf = negB b (negW b x) ∧
  f.pf = parityEven (negW b x)

/-- NEG value with its flag snapshot. -/
def negWf (b : Breite) (x : Wort) : Wort × Flags :=
  (negW b x, Flags.mk (negTrag b x) (parityEven (negW b x))
    (some (afSub 0 (trunc b x)))
    (zfTest (negW b x)) (negB b (negW b x)) (negUeberlauf b x))

/-- NEG is `0 - x` at the named width. -/
theorem negW_ist_sub (b : Breite) (x : Wort) : negW b x = subB b 0 x := rfl

/-- The NEG snapshot satisfies its validity relation. -/
theorem negWf_gueltig (b : Breite) (x : Wort) :
    NegGueltig b x (negWf b x).2 := by
  simp [negWf, NegGueltig]

/-- NEG carry means a nonzero operand. -/
theorem negTrag_heisst (b : Breite) (x : Wort) :
    negTrag b x = true ↔ trunc b x ≠ 0 := by
  simp [negTrag]

/-- NEG overflow means the signed-minimum operand. -/
theorem negUeberlauf_heisst (b : Breite) (x : Wort) :
    negUeberlauf b x = true ↔ sVal b x = sMin b := by
  simp [negUeberlauf]

/-! ## 2. Per-shift flag evidence.

    Each shift form presents its defined evidence as a `SchiebeNachweis`
    over the REUSED value operations (`shlB`/`shrB`/`sarB`) and the
    REUSED validity relation (`SchiebeGueltig`): carry out is the last
    bit shifted out of the truncated operand (saturating at the sign bit
    where the masked count reaches past the width), overflow is defined
    exactly for a masked count of one. A masked count of zero changes no
    flags on hardware; the snapshots below are the nonzero-count profile
    and the zero-count case is pinned separately by the null lemmas of
    §3 (value identity, no snapshot claimed). -/

/-- SHL carry: bit `bits - k` of the truncated operand (the last bit
    shifted out); past the width everything shifted out is zero. -/
def shlTrag (b : Breite) (x : Wort) (c : Nat) : Bool :=
  let k := schiebeZaehler b c
  if k = 0 then false
  else if decide (k ≤ b.bits) then (trunc b x).toNat.testBit (b.bits - k)
  else false

/-- SHR/SAR carry: bit `k - 1` of the truncated operand, saturating at
    the sign bit where the masked count reaches past the width. -/
def shrTrag (b : Breite) (x : Wort) (c : Nat) : Bool :=
  let k := schiebeZaehler b c
  if k = 0 then false
  else (trunc b x).toNat.testBit (min (k - 1) (b.bits - 1))

/-- SHL overflow: defined exactly for a masked count of one, where the
    sign bit changes. -/
def shlUeberlauf (b : Breite) (x : Wort) (c : Nat) : Option Bool :=
  if schiebeZaehler b c = 1 then some (negB b x != negB b (shlB b x c))
  else none

/-- SHR overflow: defined exactly for a masked count of one, where it is
    the original sign bit. -/
def shrUeberlauf (b : Breite) (x : Wort) (c : Nat) : Option Bool :=
  if schiebeZaehler b c = 1 then some (negB b x) else none

/-- SAR overflow: defined exactly for a masked count of one, where it is
    cleared (an arithmetic shift by one never changes the sign). The
    operand is carried only for uniform dispatch; the value is constant. -/
def sarUeberlauf (b : Breite) (_x : Wort) (c : Nat) : Option Bool :=
  if schiebeZaehler b c = 1 then some false else none

/-- SHL evidence over the reused `shlB` value. -/
def shlNachweis (b : Breite) (x : Wort) (c : Nat) : SchiebeNachweis :=
  ⟨shlB b x c, shlTrag b x c, shlUeberlauf b x c⟩

/-- SHR evidence over the reused `shrB` value. -/
def shrNachweis (b : Breite) (x : Wort) (c : Nat) : SchiebeNachweis :=
  ⟨shrB b x c, shrTrag b x c, shrUeberlauf b x c⟩

/-- SAR evidence over the reused `sarB` value. -/
def sarNachweis (b : Breite) (x : Wort) (c : Nat) : SchiebeNachweis :=
  ⟨sarB b x c, shrTrag b x c, sarUeberlauf b x c⟩

/-- SHL one-count snapshot: the overflow flag is the sign change. -/
theorem shlNachweis_eins (b : Breite) (x : Wort) (c : Nat)
    (h : schiebeZaehler b c = 1) :
    ∃ f : Flags, SchiebeGueltig b (shlNachweis b x c) c f ∧
      f.of = (negB b x != negB b (shlB b x c)) := by
  refine ⟨Flags.mk (shlTrag b x c) (parityEven (shlB b x c)) none
    (zfTest (shlB b x c)) (negB b (shlB b x c))
    (negB b x != negB b (shlB b x c)), ?_, rfl⟩
  unfold SchiebeGueltig shlNachweis
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro _
    simp [shlUeberlauf, h]
  · intro hn
    rw [shlUeberlauf, if_pos h] at hn
    simp at hn

/-- SHL wider-count snapshot: overflow is undefined (`none`). -/
theorem shlNachweis_ohne_eins (b : Breite) (x : Wort) (c : Nat)
    (h : schiebeZaehler b c ≠ 1) :
    ∃ f : Flags, SchiebeGueltig b (shlNachweis b x c) c f := by
  have hn : shlUeberlauf b x c = none := by simp [shlUeberlauf, h]
  exact schiebe_gueltig_existenz b (shlNachweis b x c) c hn h

/-- SHR one-count snapshot: the overflow flag is the original sign. -/
theorem shrNachweis_eins (b : Breite) (x : Wort) (c : Nat)
    (h : schiebeZaehler b c = 1) :
    ∃ f : Flags, SchiebeGueltig b (shrNachweis b x c) c f ∧
      f.of = negB b x := by
  refine ⟨Flags.mk (shrTrag b x c) (parityEven (shrB b x c)) none
    (zfTest (shrB b x c)) (negB b (shrB b x c)) (negB b x), ?_, rfl⟩
  unfold SchiebeGueltig shrNachweis
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro _
    simp [shrUeberlauf, h]
  · intro hn
    rw [shrUeberlauf, if_pos h] at hn
    simp at hn

/-- SHR wider-count snapshot: overflow is undefined (`none`). -/
theorem shrNachweis_ohne_eins (b : Breite) (x : Wort) (c : Nat)
    (h : schiebeZaehler b c ≠ 1) :
    ∃ f : Flags, SchiebeGueltig b (shrNachweis b x c) c f := by
  have hn : shrUeberlauf b x c = none := by simp [shrUeberlauf, h]
  exact schiebe_gueltig_existenz b (shrNachweis b x c) c hn h

/-- SAR one-count snapshot: the overflow flag is cleared. -/
theorem sarNachweis_eins (b : Breite) (x : Wort) (c : Nat)
    (h : schiebeZaehler b c = 1) :
    ∃ f : Flags, SchiebeGueltig b (sarNachweis b x c) c f ∧
      f.of = false := by
  refine ⟨Flags.mk (shrTrag b x c) (parityEven (sarB b x c)) none
    (zfTest (sarB b x c)) (negB b (sarB b x c)) false, ?_, rfl⟩
  unfold SchiebeGueltig sarNachweis
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro _
    simp [sarUeberlauf, h]
  · intro hn
    rw [sarUeberlauf, if_pos h] at hn
    simp at hn

/-- SAR wider-count snapshot: overflow is undefined (`none`). -/
theorem sarNachweis_ohne_eins (b : Breite) (x : Wort) (c : Nat)
    (h : schiebeZaehler b c ≠ 1) :
    ∃ f : Flags, SchiebeGueltig b (sarNachweis b x c) c f := by
  have hn : sarUeberlauf b x c = none := by simp [sarUeberlauf, h]
  exact schiebe_gueltig_existenz b (sarNachweis b x c) c hn h

/-! ## 3. Count masking pinned: oversized counts wrap, never refuse.

    A shift by the width or by a large count is a shift by the masked
    count. Narrow widths mask with five bits (`% 32`), the full width
    with six (`% 64`); a masked count of zero keeps the value (§2 claims
    no flag snapshot there). -/

/-- Narrow counts wrap every 32: the five-bit mask period. -/
theorem schiebeZaehler_periode_schmal (b : Breite) (c : Nat)
    (h : b ≠ .b64) : schiebeZaehler b (c + 32) = schiebeZaehler b c := by
  cases b with
  | b64 => exact absurd rfl h
  | b8 => simp [schiebeZaehler, Nat.add_mod_right]
  | b16 => simp [schiebeZaehler, Nat.add_mod_right]
  | b32 => simp [schiebeZaehler, Nat.add_mod_right]

/-- A 64-bit logical shift by 64 is a shift by zero (masking; the
    count period itself is the reused `schiebeZaehler_periode_b64`). -/
theorem shrB_b64_breite_ist_null (x : Wort) :
    shrB .b64 x 64 = shrB .b64 x 0 := by
  unfold shrB schiebeZaehler
  simp only [show (64 % 64) = 0 from rfl]

/-- A 64-bit arithmetic shift by 64 is a shift by zero (masking). -/
theorem sarB_b64_breite_ist_null (x : Wort) :
    sarB .b64 x 64 = sarB .b64 x 0 := by
  unfold sarB schiebeZaehler
  simp only [show (64 % 64) = 0 from rfl]

/-- Oversized counts are pinned to their masked behaviour. -/
theorem probe_zaehler_ueberlauf :
    shlB .b64 1 65 = 2 ∧ shrB .b64 8 66 = 2 ∧
    sarB .b8 0x80 39 = 0xFF ∧ shlB .b32 1 33 = 2 := by
  decide

/-! ## 4. Width-correct logic snapshots.

    `andB`/`orB` values are reused; the snapshots pair them with flags
    whose sign is the width-correct `negB b` (bit 63 alone misclassifies
    narrow results, the same finding `Ganzzahl.lean` pins for shifts).
    At full width the snapshots agree with `and64`/`or64`. -/

/-- Width-correct logic flags: CF/OF cleared, AF undefined, sign read
    at the named width. -/
def logikFlags (b : Breite) (r : Wort) : Flags :=
  Flags.mk false (parityEven r) none (zfTest r) (negB b r) false

/-- AND value with its width-correct flag snapshot. -/
def andW (b : Breite) (x y : Wort) : Wort × Flags :=
  let r := andB b x y
  (r, logikFlags b r)

/-- OR value with its width-correct flag snapshot. -/
def orW (b : Breite) (x y : Wort) : Wort × Flags :=
  let r := orB b x y
  (r, logikFlags b r)

/-- The width-correct sign is the top-bit test at full width. -/
theorem negB_b64 (w : Wort) : negB .b64 w = sfTest w := by
  simp [negB, sfTest, trunc_b64, signBit]

/-- The AND snapshot keeps the reused value. -/
theorem andW_wert (b : Breite) (x y : Wort) :
    (andW b x y).1 = andB b x y := rfl

/-- The OR snapshot keeps the reused value. -/
theorem orW_wert (b : Breite) (x y : Wort) :
    (orW b x y).1 = orB b x y := rfl

/-- At full width the AND snapshot agrees with `and64`. -/
theorem andW_b64_flaggen (x y : Wort) :
    (andW .b64 x y).2 = (and64 x y).2 := by
  simp [andW, and64, logikFlags, negB_b64, andB_b64]

/-- At full width the OR snapshot agrees with `or64`. -/
theorem orW_b64_flaggen (x y : Wort) :
    (orW .b64 x y).2 = (or64 x y).2 := by
  simp [orW, or64, logikFlags, negB_b64, orB_b64]

/-- Narrow logic flags are pinned jointly with the value. -/
theorem probe_logik_schmal :
    (andW .b8 0xF0 0x0F).1 = 0 ∧ (andW .b8 0xF0 0x0F).2.zf = true ∧
    (andW .b8 0xF0 0x0F).2.sf = false ∧
    (andW .b8 0xF0 0x0F).2.af = none ∧
    (orW .b8 0x80 0x01).1 = 0x81 ∧ (orW .b8 0x80 0x01).2.sf = true := by
  decide

/-- NEG flags are pinned jointly with the value: `-1` borrows, the
    signed minimum overflows, zero is exact. -/
theorem probe_neg :
    (negWf .b64 1).1 = 0xFFFFFFFFFFFFFFFF ∧
    (negWf .b64 1).2.cf = true ∧ (negWf .b64 1).2.of = false ∧
    (negWf .b64 0x8000000000000000).2.of = true ∧
    (negWf .b64 0x8000000000000000).2.cf = true ∧
    (negWf .b64 0).1 = 0 ∧ (negWf .b64 0).2.cf = false ∧
    (negWf .b64 0).2.zf = true := by
  decide

/-! ## 5. Refusals: what is NOT a shift and NOT a zero.

    A signed division is not an arithmetic shift (`tdiv` truncates
    toward zero, `sarB` floors via `ediv`: `-3 / 2` truncates to `-1`
    but shifts to `-2`), a float `x - x` is not `+0` for NaN inputs,
    and a shift without overflow evidence is not the product. None of
    these becomes a peephole; each is a named refusal with a concrete
    counterexample. -/

/-- The word `-3` at full width. -/
def negDrei : Wort := BitVec.ofNat 64 (2 ^ 64 - 3)

/-- The word `-1` at full width (the truncated quotient of `-3 / 2`). -/
def negEins : Wort := BitVec.ofNat 64 (2 ^ 64 - 1)

/-- Signed division is not an arithmetic shift: `sarB` floors `-3`
    to `-2` while `divS` truncates to `-1`. -/
theorem sdiv_ist_kein_sar :
    sVal .b64 negDrei = -3 ∧ sVal .b64 (sarB .b64 negDrei 1) = -2 ∧
    divS .b64 negDrei 2 = some (negEins, negEins) ∧
    sVal .b64 negEins = -1 := by
  decide

/-- A float `x - x` is not `+0`: NaN minus NaN stays NaN, so the
    integer `x - x -> 0` peephole is refused on floats. -/
theorem float_sub_self_kein_null :
    Gleitkomma.sub Gleitkomma.f64 (Gleitkomma.nanQ Gleitkomma.f64)
        (Gleitkomma.nanQ Gleitkomma.f64)
      = Gleitkomma.nanQ Gleitkomma.f64 ∧
    Gleitkomma.nanQ Gleitkomma.f64 ≠
      Gleitkomma.nullP Gleitkomma.f64 := by
  decide

/-- No strength reduction without range evidence: an unchecked shift
    is not the product (`2^63 << 1` wraps to zero). The consumer gate
    is the checked `shlW_keinUeberlauf` of `StaerkeReduktion.lean`. -/
theorem staerke_braucht_bereich :
    ∃ (x : Wort) (k : Nat),
      (shlB .b64 x k).toNat ≠ x.toNat * 2 ^ k := by
  refine ⟨0x8000000000000000, 1, by decide⟩

/-! ## 6. Joint witness: masked shift plus flag read through memory.

    `1 << 66` is a shift by the masked count 2 (value 4, no carry
    out), and the computed word goes through the real permission-
    checked `write64`/`read64` and observably changes the byte at the
    address. Value, flag evidence and memory change are pinned jointly,
    on a nonzero word. -/

/-- The witness memory after storing the masked shift `1 << 66 = 4`. -/
def shiftSondenSpeicherNach : Speicher :=
  { zeugenSpeicher with
    bytes := writeBytes zeugenSpeicher 0 (shlB .b64 1 66) }

/-- Shift with masked count plus flag read changing memory. -/
theorem shift_maskiert_speicher_zeuge :
    shlB .b64 1 66 = 4 ∧ (shlNachweis .b64 1 66).trag = false ∧
    (shlNachweis .b64 1 66).ergebnis = 4 ∧
    ∃ (m' : Speicher),
      write64 zeugenSpeicher 0 (shlB .b64 1 66) = some m' ∧
      read64 m' 0 = some 4 ∧
      zeugenSpeicher.bytes 0 ≠ m'.bytes 0 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  refine ⟨shiftSondenSpeicherNach, ?_, ?_, ?_⟩
  · have hwr : write64 zeugenSpeicher 0 (shlB .b64 1 66) =
        some shiftSondenSpeicherNach := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    exact hwr
  · have hwr : write64 zeugenSpeicher 0 (shlB .b64 1 66) =
        some shiftSondenSpeicherNach := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd := read64_nach_write64 zeugenSpeicher _ 0 (shlB .b64 1 66)
      hwr rfl
    have hval : shlB .b64 1 66 = 4 := by decide
    rw [hval] at hrd
    exact hrd
  · have hhit := writeBytesN_hit zeugenSpeicher 0 (shlB .b64 1 66)
      8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 (shlB .b64 1 66) 0
    unfold writeBytes
    rw [hhit]
    decide

/-! ## 7. Extension interface: how a future form presents itself.

    This file adds no `Befehl` constructor and changes no `schritt`
    equation (the 14 pilot forms are untouched). A future shift/logic
    instruction form carries exactly one of the shapes below and
    presents exactly the evidence named beside it: a shift presents its
    `SchiebeNachweis` (§2) against `SchiebeGueltig`, AND/OR present
    `logikFlags` (§4), NEG presents `NegGueltig` (§1). The value is
    always the routed call, never a second implementation. -/

/-- The seven shift/logic shapes a future form may carry (data only). -/
inductive ShiftOp where
  | shl | shr | sar | and | or | not | neg
  deriving DecidableEq, Repr

/-- Value dispatch: every shape routes to the reused canonical op. -/
def shiftOpWert : ShiftOp → Breite → Wort → Wort → Nat → Wort
  | .shl, b, x, _, c => shlB b x c
  | .shr, b, x, _, c => shrB b x c
  | .sar, b, x, _, c => sarB b x c
  | .and, b, x, y, _ => andB b x y
  | .or, b, x, y, _ => orB b x y
  | .not, b, x, _, _ => notB b x
  | .neg, b, x, _, _ => negW b x

/-- The dispatch routes every shape to its canonical op. -/
theorem shiftOpWert_routen (b : Breite) (x y : Wort) (c : Nat) :
    shiftOpWert .shl b x y c = shlB b x c ∧
    shiftOpWert .shr b x y c = shrB b x c ∧
    shiftOpWert .sar b x y c = sarB b x c ∧
    shiftOpWert .and b x y c = andB b x y ∧
    shiftOpWert .or b x y c = orB b x y ∧
    shiftOpWert .not b x y c = notB b x ∧
    shiftOpWert .neg b x y c = negW b x := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- CUTS:
   No `Befehl` extension, no `schritt` change, no encoding/decoding, no
   TSO bridge, no source correspondence, no cost transfer and no final-
   image acceptance is claimed here. Value operations (`shlB`/`shrB`/
   `sarB`/`andB`/`orB`/`notB`, `and64`/`or64`) and the validity
   relations (`SchiebeGueltig`, `LogikGueltig`) are reused from
   `Ganzzahl.lean`; carry/overflow characterisation from
   `FlagBeweis.lean`; the float model from `Gleitkomma.lean` via
   `Gleitprofil.lean`. The count masks (six bits at 64, five bits
   narrow), the NEG
   AF (nibble borrow via `afSub`), the shift CF/OF corners past the
   width and the zero-count flag preservation (documented, no snapshot
   claimed) are stated executable semantics, not verified against
   silicon. Full final-byte/source/hardware correspondence stays OPEN.
-/

#print axioms negW
#print axioms negW_ist_sub
#print axioms negWf_gueltig
#print axioms negTrag_heisst
#print axioms negUeberlauf_heisst
#print axioms shlNachweis_eins
#print axioms shlNachweis_ohne_eins
#print axioms shrNachweis_eins
#print axioms shrNachweis_ohne_eins
#print axioms sarNachweis_eins
#print axioms sarNachweis_ohne_eins
#print axioms schiebeZaehler_periode_schmal
#print axioms shrB_b64_breite_ist_null
#print axioms sarB_b64_breite_ist_null
#print axioms probe_zaehler_ueberlauf
#print axioms negB_b64
#print axioms andW_wert
#print axioms orW_wert
#print axioms andW_b64_flaggen
#print axioms orW_b64_flaggen
#print axioms probe_logik_schmal
#print axioms probe_neg
#print axioms sdiv_ist_kein_sar
#print axioms float_sub_self_kein_null
#print axioms staerke_braucht_bereich
#print axioms shift_maskiert_speicher_zeuge
#print axioms shiftOpWert_routen

end Gabbro.Grammatik.X86
