/-
  File:      Grammatik/X86/IntExtend.lean
  Subject:   Zero/sign extension (MOVZX/MOVSX/MOVSXD), byte swap (BSWAP),
             shift groups (D0/D1/D2/D3/C0/C1 /4 /5 /7) and double shifts
             (SHLD/SHRD) connected to the coherent machine.

  Lane 1353: lifts the accepted evaluators unchanged -- `extendNarrow`/
  `mergeRegNarrow` (NarrowOps), `bswap32`/`bswap64` (ByteSwap),
  `shlB`/`shrB`/`sarB` with `shlNachweis`/`shrNachweis`/`sarNachweis`
  (ShiftLogic over Ganzzahl), the prefix/width parsers `rotNimmPraefix`/
  `rotBreite` plus `rotPraefixBytes`/`rotSibTail` (IntRotate) -- into
  canonical decoders, a register-state step and an `HwAdapter` over
  `HwMaschine`. Rotate digits /0 to /3 stay with `IntRotate.decodeRot`;
  this family decodes shifts /4 /5 (/6 is the architectural SHL alias)
  /7 only. Memory forms decode (shift group only) but the register
  plug refuses them: memory moves through TSO events, never through
  a substituted word effect (the `IntRotate` discipline).

  Manual provenance (lane-clone snapshot): Intel SDM 325462-093US Sep
  2026 instruction reference text (MOVZX/MOVSX/MOVSXD/BSWAP/SHL/SHR/
  SAR/SHLD/SHRD entries); headings only, no silicon proof beyond
  self-consistency (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Wort
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ganzzahl
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.Befehle.Arithmetik.ShiftLogic
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Befehle.Arithmetik.ByteSwap
import Grammatik.X86.Befehle.Ganzzahl.IntRotate
import Grammatik.X86.Befehle.Ganzzahl.IntegerCore
import Grammatik.X86.Hw.Grundlage.ExtendedExecution
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Kern.Gleitprofil

namespace Gabbro.Grammatik.X86

/-! ## 1. Value core: extension, MOVSXD and byte swap reuse.

    MOVZX/MOVSX reuse `extendNarrow` (zero is truncation, sign is the
    canonical `sext`); the destination writeback reuses
    `mergeRegNarrow` (8/16-bit writes merge, 32-bit writes
    zero-extend, 64-bit writes are whole). MOVSXD reuses `sext .b32`.
    BSWAP reuses `bswap32`/`bswap64`/`bswapBreite`. Nothing is
    redefined here. -/

/-- Extension mode of a MOVZX/MOVSX row: zero/sign over 8/16-bit. -/
inductive IxExtModus where
  | zx8 | zx16 | sx8 | sx16
  deriving DecidableEq, Repr

/-- Source width of an extension mode. -/
def ixQuellBreite : IxExtModus → Breite
  | .zx8 => .b8 | .zx16 => .b16 | .sx8 => .b8 | .sx16 => .b16

/-- The source width names the mode. -/
theorem ixQuellBreite_faelle :
    ixQuellBreite .zx8 = .b8 ∧ ixQuellBreite .zx16 = .b16 ∧
    ixQuellBreite .sx8 = .b8 ∧ ixQuellBreite .sx16 = .b16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Extension value over the accepted `extendNarrow`. -/
def ixExtWert (m : IxExtModus) (v : Wort) : Wort :=
  match m with
  | .zx8 => extendNarrow .zero .b8 v
  | .zx16 => extendNarrow .zero .b16 v
  | .sx8 => extendNarrow .sign .b8 v
  | .sx16 => extendNarrow .sign .b16 v

/-- Zero extension is truncation (the accepted equation, lifted). -/
theorem ixExtWert_zx8 (v : Wort) :
    ixExtWert .zx8 v = trunc .b8 v := rfl

/-- Zero extension of 16 bits is truncation. -/
theorem ixExtWert_zx16 (v : Wort) :
    ixExtWert .zx16 v = trunc .b16 v := rfl

/-- Sign extension reuses the canonical `sext`. -/
theorem ixExtWert_sx8 (v : Wort) :
    ixExtWert .sx8 v = sext .b8 v := rfl

/-- Sign extension of 16 bits reuses the canonical `sext`. -/
theorem ixExtWert_sx16 (v : Wort) :
    ixExtWert .sx16 v = sext .b16 v := rfl

/-- Pinned extensions: zero keeps, sign fills. -/
theorem probe_ixExtWert :
    ixExtWert .zx8 0xFF = 0xFF ∧
    ixExtWert .sx8 0xFF = 0xFFFFFFFFFFFFFFFF ∧
    ixExtWert .zx16 0x8000 = 0x8000 ∧
    ixExtWert .sx16 0x8000 = 0xFFFFFFFFFFFF8000 := by
  decide

/-- Destination writeback with architectural upper-bit discipline. -/
def ixZielSchreiben (w : Breite) (alt neu : Wort) : Wort :=
  mergeRegNarrow w alt neu

/-- A 16-bit extension write merges into the low bits. -/
theorem ixZielSchreiben_b16 (alt neu : Wort) :
    ixZielSchreiben .b16 alt neu =
      (alt &&& ~~~(maske .b16)) ||| trunc .b16 neu := rfl

/-- A 32-bit extension write zero-extends like the accepted merge. -/
theorem ixZielSchreiben_b32 (alt neu : Wort) :
    ixZielSchreiben .b32 alt neu = trunc .b32 neu :=
  mergeRegNarrow_b32 alt neu

/-- A 64-bit extension write is whole like the accepted merge. -/
theorem ixZielSchreiben_b64 (alt neu : Wort) :
    ixZielSchreiben .b64 alt neu = neu :=
  mergeRegNarrow_b64 alt neu

/-- Pinned 32-bit write: the upper half is cleared. -/
theorem probe_ixZielSchreiben_b32 :
    ixZielSchreiben .b32 0xABCDEF1234567890 0x11223344 =
      0x11223344 := by
  decide

/-- MOVSXD value: sign extension of the low 32 bits. -/
def ixMovsxdWert (v : Wort) : Wort := sext .b32 v

/-- MOVSXD is the canonical 32-bit sign extension. -/
theorem ixMovsxdWert_sext (v : Wort) :
    ixMovsxdWert v = sext .b32 v := rfl

/-- Pinned MOVSXD: the sign fills, a clear sign keeps. -/
theorem probe_ixMovsxdWert :
    ixMovsxdWert 0x80000000 = 0xFFFFFFFF80000000 ∧
    ixMovsxdWert 0x7FFFFFFF = 0x7FFFFFFF := by
  decide

/-- BSWAP value dispatch reuses the accepted width dispatch
    (32/64 bits only; 8/16 bits stay refused there). -/
theorem ixBswap_breite_b8 : bswapBreite .b8 = none :=
  bswapBreite_b8

/-- BSWAP of the witness word through the accepted helper. -/
theorem probe_ixBswap64 :
    bswap64 bswapZeugenWort = BitVec.ofNat 64 0x0807060504030201 :=
  probe_bswap64_wert

/-! ## 2. Single shifts reuse the accepted evidence.

    Values route to `shlB`/`shrB`/`sarB`, flag evidence to
    `shlNachweis`/`shrNachweis`/`sarNachweis` (ShiftLogic): carry is
    the last bit shifted out, overflow is defined exactly for a
    masked count of one and stays free otherwise. Digit /6 is the
    architectural SHL alias of /4; digits /0 to /3 refuse here and stay
    with `IntRotate.decodeRot`. -/

/-- Shift direction with a canonical row here: SHL /4, SHR /5, SAR /7. -/
inductive IxShiftRichtung where
  | shl | shr | sar
  deriving DecidableEq, Repr

/-- Group-2 extension digit: SHL is /4, SHR is /5, SAR is /7. -/
def ixRichtungFeld : IxShiftRichtung → Nat
  | .shl => 4 | .shr => 5 | .sar => 7

/-- Digit back to a shift direction: /6 is the SHL alias; rotate
    digits /0 to /3 refuse here. -/
def ixFeldRichtung : Nat → Option IxShiftRichtung
  | 4 => some .shl | 5 => some .shr | 6 => some .shl | 7 => some .sar
  | _ => none

/-- Decoding inverts encoding on every shift digit. -/
theorem ixFeldRichtung_richtungFeld (r : IxShiftRichtung) :
    ixFeldRichtung (ixRichtungFeld r) = some r := by
  cases r <;> rfl

/-- The /6 alias decodes to SHL. -/
theorem ixFeldRichtung_alias :
    ixFeldRichtung 6 = some .shl := rfl

/-- Rotate digits refuse in the shift digit space. -/
theorem ixFeld_weist_rot_zu :
    ixFeldRichtung 0 = none ∧ ixFeldRichtung 1 = none ∧
    ixFeldRichtung 2 = none ∧ ixFeldRichtung 3 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Shift value dispatch over the accepted operations. -/
def ixShiftWert : IxShiftRichtung → Breite → Wort → Nat → Wort
  | .shl, b, x, c => shlB b x c
  | .shr, b, x, c => shrB b x c
  | .sar, b, x, c => sarB b x c

/-- The dispatch routes every direction to its canonical op. -/
theorem ixShiftWert_routen (b : Breite) (x : Wort) (c : Nat) :
    ixShiftWert .shl b x c = shlB b x c ∧
    ixShiftWert .shr b x c = shrB b x c ∧
    ixShiftWert .sar b x c = sarB b x c :=
  ⟨rfl, rfl, rfl⟩

/-- Shift flag evidence over the accepted ShiftLogic snapshots. -/
def ixShiftNachweis : IxShiftRichtung → Breite → Wort → Nat →
    SchiebeNachweis
  | .shl, b, x, c => shlNachweis b x c
  | .shr, b, x, c => shrNachweis b x c
  | .sar, b, x, c => sarNachweis b x c

/-- The evidence routes to the accepted snapshots. -/
theorem ixShiftNachweis_routen (b : Breite) (x : Wort) (c : Nat) :
    ixShiftNachweis .shl b x c = shlNachweis b x c ∧
    ixShiftNachweis .shr b x c = shrNachweis b x c ∧
    ixShiftNachweis .sar b x c = sarNachweis b x c :=
  ⟨rfl, rfl, rfl⟩

/-- SHL overflow evidence is defined exactly at count one. -/
theorem ixShl_ueberlauf (b : Breite) (x : Wort) (c : Nat) :
    (schiebeZaehler b c = 1 →
      (shlNachweis b x c).ueberlauf ≠ none) ∧
    (schiebeZaehler b c ≠ 1 →
      (shlNachweis b x c).ueberlauf = none) := by
  constructor <;> intro hcond <;>
    simp [shlNachweis, shlUeberlauf, hcond]

/-- SHR overflow evidence is defined exactly at count one. -/
theorem ixShr_ueberlauf (b : Breite) (x : Wort) (c : Nat) :
    (schiebeZaehler b c = 1 →
      (shrNachweis b x c).ueberlauf ≠ none) ∧
    (schiebeZaehler b c ≠ 1 →
      (shrNachweis b x c).ueberlauf = none) := by
  constructor <;> intro hcond <;>
    simp [shrNachweis, shrUeberlauf, hcond]

/-- SAR overflow evidence is defined exactly at count one. -/
theorem ixSar_ueberlauf (b : Breite) (x : Wort) (c : Nat) :
    (schiebeZaehler b c = 1 →
      (sarNachweis b x c).ueberlauf ≠ none) ∧
    (schiebeZaehler b c ≠ 1 →
      (sarNachweis b x c).ueberlauf = none) := by
  constructor <;> intro hcond <;>
    simp [sarNachweis, sarUeberlauf, hcond]

/-- Executable flag snapshot for a single shift: a zero masked count
    keeps every flag, else the accepted evidence with the incoming OF
    bit where the architecture leaves it undefined. -/
def ixShiftSnap (r : IxShiftRichtung) (b : Breite) (x : Wort)
    (vor : Flags) (c : Nat) : Flags :=
  if schiebeZaehler b c = 0 then vor
  else
    let n := ixShiftNachweis r b x c
    Flags.mk n.trag (parityEven n.ergebnis) none
      (zfTest n.ergebnis) (negB b n.ergebnis)
      (n.ueberlauf.getD vor.of)

/-- A zero masked count keeps every flag. -/
theorem ixShiftSnap_null (r : IxShiftRichtung) (b : Breite) (x : Wort)
    (vor : Flags) (c : Nat) (h : schiebeZaehler b c = 0) :
    ixShiftSnap r b x vor c = vor := by
  unfold ixShiftSnap
  rw [if_pos h]

/-- The SHL snapshot satisfies the accepted validity relation. -/
theorem ixShiftSnap_gueltig_shl (b : Breite) (x : Wort) (vor : Flags)
    (c : Nat) (h0 : schiebeZaehler b c ≠ 0) :
    SchiebeGueltig b (shlNachweis b x c) c
      (ixShiftSnap .shl b x vor c) := by
  have hn : ixShiftNachweis .shl b x c = shlNachweis b x c := rfl
  unfold ixShiftSnap
  rw [hn, if_neg h0]
  unfold SchiebeGueltig
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro h1
    have hne : (shlNachweis b x c).ueberlauf ≠ none :=
      (ixShl_ueberlauf b x c).1 h1
    cases hueb : (shlNachweis b x c).ueberlauf with
    | some v => simp only [hueb, Option.getD_some]
    | none => exact absurd hueb hne
  · intro hnone hcon
    exact (ixShl_ueberlauf b x c).1 hcon hnone

/-- The SHR snapshot satisfies the accepted validity relation. -/
theorem ixShiftSnap_gueltig_shr (b : Breite) (x : Wort) (vor : Flags)
    (c : Nat) (h0 : schiebeZaehler b c ≠ 0) :
    SchiebeGueltig b (shrNachweis b x c) c
      (ixShiftSnap .shr b x vor c) := by
  have hn : ixShiftNachweis .shr b x c = shrNachweis b x c := rfl
  unfold ixShiftSnap
  rw [hn, if_neg h0]
  unfold SchiebeGueltig
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro h1
    have hne : (shrNachweis b x c).ueberlauf ≠ none :=
      (ixShr_ueberlauf b x c).1 h1
    cases hueb : (shrNachweis b x c).ueberlauf with
    | some v => simp only [hueb, Option.getD_some]
    | none => exact absurd hueb hne
  · intro hnone hcon
    exact (ixShr_ueberlauf b x c).1 hcon hnone

/-- The SAR snapshot satisfies the accepted validity relation. -/
theorem ixShiftSnap_gueltig_sar (b : Breite) (x : Wort) (vor : Flags)
    (c : Nat) (h0 : schiebeZaehler b c ≠ 0) :
    SchiebeGueltig b (sarNachweis b x c) c
      (ixShiftSnap .sar b x vor c) := by
  have hn : ixShiftNachweis .sar b x c = sarNachweis b x c := rfl
  unfold ixShiftSnap
  rw [hn, if_neg h0]
  unfold SchiebeGueltig
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro h1
    have hne : (sarNachweis b x c).ueberlauf ≠ none :=
      (ixSar_ueberlauf b x c).1 h1
    cases hueb : (sarNachweis b x c).ueberlauf with
    | some v => simp only [hueb, Option.getD_some]
    | none => exact absurd hueb hne
  · intro hnone hcon
    exact (ixSar_ueberlauf b x c).1 hcon hnone

/-- Pinned one-count snapshot: SHL carries out with sign-change OF. -/
theorem probe_ixShiftSnap_eins :
    (ixShiftNachweis .shl .b64 0x4000000000000000 1).trag = false ∧
    (ixShiftNachweis .shl .b64 0x4000000000000000 1).ueberlauf =
      some true ∧
    (ixShiftNachweis .shl .b64 1 66).ueberlauf = none := by
  decide

/-! ## 3. Double shifts (SHLD/SHRD).

    Counts reuse the architectural mask (`schiebeZaehler`: five bits
    below 64, six at 64). A zero masked count changes nothing; a
    count past the width is undefined on silicon and is refused by
    the step (§6), never pinned here. CF is the last bit shifted out
    of the destination; OF is defined exactly for a masked count of
    one (the sign-change sentence) and stays free otherwise. SF/ZF/PF
    read the result, AF is undefined. -/

/-- Double-shift left value (SHLD): `dst << k` filled from `src`. -/
def shldB (b : Breite) (dst src : Wort) (c : Nat) : Wort :=
  let k := schiebeZaehler b c
  if k = 0 then trunc b dst
  else BitVec.ofNat 64 (((trunc b dst).toNat * 2 ^ k +
    (trunc b src).toNat / 2 ^ (b.bits - k)) % 2 ^ b.bits)

/-- Double-shift right value (SHRD): `dst >> k` filled from `src`. -/
def shrdB (b : Breite) (dst src : Wort) (c : Nat) : Wort :=
  let k := schiebeZaehler b c
  if k = 0 then trunc b dst
  else BitVec.ofNat 64 (((trunc b dst).toNat / 2 ^ k +
    (trunc b src).toNat % 2 ^ k * 2 ^ (b.bits - k)) % 2 ^ b.bits)

/-- A zero count is the truncated identity. -/
theorem shldB_null (b : Breite) (dst src : Wort) (c : Nat)
    (h : schiebeZaehler b c = 0) :
    shldB b dst src c = trunc b dst := by
  unfold shldB
  rw [if_pos h]

/-- A zero count is the truncated identity. -/
theorem shrdB_null (b : Breite) (dst src : Wort) (c : Nat)
    (h : schiebeZaehler b c = 0) :
    shrdB b dst src c = trunc b dst := by
  unfold shrdB
  rw [if_pos h]

/-- Pinned double shifts: fill from the other operand, zero is idle. -/
theorem probe_shldB :
    shldB .b32 0x12345678 0xABCDEF00 8 = 0x345678AB ∧
    shldB .b64 1 0x8000000000000000 1 = 3 ∧
    shldB .b32 0x12345678 0xABCDEF00 0 = 0x12345678 := by
  decide

/-- Pinned double shifts right. -/
theorem probe_shrdB :
    shrdB .b32 0x12345678 0xABCDEF00 8 = 0x00123456 ∧
    shrdB .b64 0x8000000000000001 0 1 = 0x4000000000000000 ∧
    shrdB .b32 0x12345678 0xABCDEF00 0 = 0x12345678 := by
  decide

/-- SHLD carry: bit `bits - k` of the destination. -/
def shldTrag (b : Breite) (dst : Wort) (c : Nat) : Bool :=
  let k := schiebeZaehler b c
  if k = 0 then false
  else (trunc b dst).toNat.testBit (b.bits - k)

/-- SHRD carry: bit `k - 1` of the destination. -/
def shrdTrag (b : Breite) (dst : Wort) (c : Nat) : Bool :=
  let k := schiebeZaehler b c
  if k = 0 then false
  else (trunc b dst).toNat.testBit (k - 1)

/-- Pinned carries: SHLD shifts `0x80000001` out as set, SHRD reads
    the low bit out. -/
theorem probe_shldTrag :
    shldTrag .b32 0x80000001 1 = true ∧
    shrdTrag .b32 0x80000001 1 = true ∧
    shldTrag .b32 0x80000001 0 = false := by
  decide

/-- SHLD overflow: the sign change at count one, free otherwise. -/
def shldUeberlauf (b : Breite) (dst src : Wort) (c : Nat) :
    Option Bool :=
  if schiebeZaehler b c = 1 then
    some (negB b dst != negB b (shldB b dst src c))
  else none

/-- SHRD overflow: the sign change at count one, free otherwise. -/
def shrdUeberlauf (b : Breite) (dst src : Wort) (c : Nat) :
    Option Bool :=
  if schiebeZaehler b c = 1 then
    some (negB b dst != negB b (shrdB b dst src c))
  else none

/-- Defined double-shift evidence: value, carry out, optional OF. -/
structure ShldNachweis where
  ergebnis : Wort
  trag : Bool
  ueberlauf : Option Bool
  deriving DecidableEq, Repr

/-- SHLD evidence. -/
def shldNachweis (b : Breite) (dst src : Wort) (c : Nat) :
    ShldNachweis :=
  ⟨shldB b dst src c, shldTrag b dst c, shldUeberlauf b dst src c⟩

/-- SHRD evidence. -/
def shrdNachweis (b : Breite) (dst src : Wort) (c : Nat) :
    ShldNachweis :=
  ⟨shrdB b dst src c, shrdTrag b dst c, shrdUeberlauf b dst src c⟩

/-- SHLD overflow evidence is defined exactly at count one. -/
theorem shldUeberlauf_char (b : Breite) (dst src : Wort) (c : Nat) :
    (schiebeZaehler b c = 1 →
      (shldNachweis b dst src c).ueberlauf ≠ none) ∧
    (schiebeZaehler b c ≠ 1 →
      (shldNachweis b dst src c).ueberlauf = none) := by
  constructor <;> intro hcond <;>
    simp [shldNachweis, shldUeberlauf, hcond]

/-- SHRD overflow evidence is defined exactly at count one. -/
theorem shrdUeberlauf_char (b : Breite) (dst src : Wort) (c : Nat) :
    (schiebeZaehler b c = 1 →
      (shrdNachweis b dst src c).ueberlauf ≠ none) ∧
    (schiebeZaehler b c ≠ 1 →
      (shrdNachweis b dst src c).ueberlauf = none) := by
  constructor <;> intro hcond <;>
    simp [shrdNachweis, shrdUeberlauf, hcond]

/-- Validity of a double-shift flag snapshot: a zero masked count
    keeps every flag; otherwise CF/result flags are pinned, AF is
    undefined, and OF is pinned exactly at count one. -/
def ShldGueltig (b : Breite) (n : ShldNachweis) (c : Nat)
    (vor nach : Flags) : Prop :=
  if schiebeZaehler b c = 0 then nach = vor
  else nach.cf = n.trag ∧ nach.af = none ∧
    nach.zf = zfTest n.ergebnis ∧ nach.sf = negB b n.ergebnis ∧
    nach.pf = parityEven n.ergebnis ∧
    (schiebeZaehler b c = 1 → nach.of = n.ueberlauf.getD nach.of) ∧
    (n.ueberlauf = none → schiebeZaehler b c ≠ 1)

/-- Executable SHLD flag snapshot. -/
def shldFlags (b : Breite) (dst src : Wort) (vor : Flags)
    (c : Nat) : Flags :=
  if schiebeZaehler b c = 0 then vor
  else
    let n := shldNachweis b dst src c
    Flags.mk n.trag (parityEven n.ergebnis) none
      (zfTest n.ergebnis) (negB b n.ergebnis)
      (n.ueberlauf.getD vor.of)

/-- Executable SHRD flag snapshot. -/
def shrdFlags (b : Breite) (dst src : Wort) (vor : Flags)
    (c : Nat) : Flags :=
  if schiebeZaehler b c = 0 then vor
  else
    let n := shrdNachweis b dst src c
    Flags.mk n.trag (parityEven n.ergebnis) none
      (zfTest n.ergebnis) (negB b n.ergebnis)
      (n.ueberlauf.getD vor.of)

/-- The SHLD snapshot satisfies its validity relation. -/
theorem shldFlags_gueltig (b : Breite) (dst src : Wort) (vor : Flags)
    (c : Nat) :
    ShldGueltig b (shldNachweis b dst src c) c vor
      (shldFlags b dst src vor c) := by
  unfold ShldGueltig shldFlags
  by_cases h0 : schiebeZaehler b c = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    have hue := shldUeberlauf_char b dst src c
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro h1
      have hne : (shldNachweis b dst src c).ueberlauf ≠ none :=
        hue.1 h1
      cases hueb : (shldNachweis b dst src c).ueberlauf with
      | some v => simp only [hueb, Option.getD_some]
      | none => exact absurd hueb hne
    · intro hnone hcon
      exact hue.1 hcon hnone

/-- The SHRD snapshot satisfies its validity relation. -/
theorem shrdFlags_gueltig (b : Breite) (dst src : Wort) (vor : Flags)
    (c : Nat) :
    ShldGueltig b (shrdNachweis b dst src c) c vor
      (shrdFlags b dst src vor c) := by
  unfold ShldGueltig shrdFlags
  by_cases h0 : schiebeZaehler b c = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    have hue := shrdUeberlauf_char b dst src c
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro h1
      have hne : (shrdNachweis b dst src c).ueberlauf ≠ none :=
        hue.1 h1
      cases hueb : (shrdNachweis b dst src c).ueberlauf with
      | some v => simp only [hueb, Option.getD_some]
      | none => exact absurd hueb hne
    · intro hnone hcon
      exact hue.1 hcon hnone

/-- Pinned double-shift OF rows: the sign change at count one, free
    past it. -/
theorem probe_shldUeberlauf :
    shldUeberlauf .b32 0x40000000 0 1 = some true ∧
    shldUeberlauf .b32 0x40000000 0 2 = none ∧
    shrdUeberlauf .b32 0x80000001 0 1 = some true := by
  decide

/-! ## 4. Canonical bytes: decode, encode, round trips, refusals.

    Opcodes 0F B6/B7/BE/BF (MOVZX/MOVSX), 63 (MOVSXD), 0F C8-CF
    (BSWAP), D0/D1/D2/D3/C0/C1 with digits /4 to /7 (shifts) and
    0F A4/A5/AC/AD (SHLD/SHRD). Prefix and width parsing reuse
    `rotNimmPraefix`/`rotBreite`; register prefix emission reuses
    `rotPraefixBytes`/`rotSibTail`. REX.R would rewrite a group
    digit and REX.X has no SIB to extend, so both refuse on group
    rows; LOCK refuses at the prefix. The decoder parses bytes,
    never encode-equality. -/

/-- Destination width of extension and double-shift rows: 16,
    32 or 64 bits. Neither family has an 8-bit destination form, so
    the width is its own type and no phantom row can be stated. -/
inductive IxZielBreite where
  | w16 | w32 | w64
  deriving DecidableEq, Repr

/-- Architectural width of a destination width. -/
def ixZielBreite : IxZielBreite → Breite
  | .w16 => .b16 | .w32 => .b32 | .w64 => .b64

/-- Destination width back from an architectural width: 8 bits has
    no destination form and refuses. -/
def ixZielAusBreite : Breite → Option IxZielBreite
  | .b16 => some .w16
  | .b32 => some .w32
  | .b64 => some .w64
  | .b8 => none

/-- Count source of a single shift: by one, by CL, or by immediate. -/
inductive IxZaehler where
  | eins | cl | imm8 (n : Nat)
  deriving DecidableEq, Repr

/-- Count source of a double shift: by CL or by immediate. -/
inductive IxDoppelZaehler where
  | cl | imm8 (n : Nat)
  deriving DecidableEq, Repr

/-- Shift operand: register-direct or base-plus-displacement memory
    (the pilot canonical memory shape). -/
inductive IxShiftOperand where
  | reg (dst : Register)
  | mem (base : Register) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- One single-shift form. -/
structure IxShiftForm where
  dir : IxShiftRichtung
  breite : Breite
  quelle : IxZaehler
  operand : IxShiftOperand
  deriving DecidableEq, Repr

/-- One family instruction. -/
inductive IxBefehl where
  | ext (m : IxExtModus) (w : IxZielBreite) (dst src : Register)
  | sxd (w64 : Bool) (dst src : Register)
  | bswap (w64 : Bool) (r : Register)
  | shift (f : IxShiftForm)
  | shld (links : Bool) (w : IxZielBreite) (q : IxDoppelZaehler)
      (dst src : Register)
  deriving DecidableEq, Repr

/-- A decoded family instruction with its consumed length. -/
structure IxDecodiert where
  befehl : IxBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- A REX byte is present exactly when the parsed prefix length
    exceeds the optional 66h byte. -/
def ixHatRex (p : RotPraefix) : Bool :=
  decide (p.n = (if p.op16 then 2 else 1))

/-- No prefix means no REX byte. -/
theorem ixHatRex_ohnePraefix :
    ixHatRex ⟨false, 0, 0, 0, 0, 0⟩ = false := rfl

/-- Register-direct ModRM for extension rows: the reg field is the
    destination (REX.R extends), the rm field the source (REX.B
    extends). An 8-bit source with a low code 4-7 and no REX byte
    would be AH/BH/CH/DH, which has no `Register` name here, so it
    refuses. -/
def ixModrmExt (p : RotPraefix) (is8 : Bool) :
    List Byte → Option (Register × Register × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (p.r * 8 + byteNat m / 8 % 8),
          codeReg (p.b * 8 + byteNat m % 8) with
      | some dst, some src =>
        if is8 && decide (4 ≤ regLow src) && !ixHatRex p then none
        else some (dst, src, rest)
      | _, _ => none
    else none

/-- Register-direct ModRM for double shifts: the reg field is the
    source (REX.R extends), the rm field the destination. -/
def ixModrmShld (p : RotPraefix) :
    List Byte → Option (Register × Register × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (p.r * 8 + byteNat m / 8 % 8),
          codeReg (p.b * 8 + byteNat m % 8) with
      | some src, some dst => some (src, dst, rest)
      | _, _ => none
    else none

/-- Shift ModRM: register-direct or disp32 memory (with the pilot
    SIB byte), shift digits /4 to /7; rotate digits and every other
    mode refuse. -/
def ixShiftModrm (p : RotPraefix) :
    List Byte →
      Option (IxShiftRichtung × IxShiftOperand × Nat × List Byte)
  | [] => none
  | m :: rest =>
    match ixFeldRichtung (byteNat m / 8 % 8) with
    | none => none
    | some r =>
      if byteNat m / 64 == 3 then
        match codeReg (p.b * 8 + byteNat m % 8) with
        | some dst => some (r, .reg dst, 1, rest)
        | none => none
      else if byteNat m / 64 == 2 then
        let rm := byteNat m % 8
        if rm == 4 then
          match rest with
          | sib :: rest2 =>
            if byteNat sib == 36 then
              match parseLe32 rest2 with
              | some (d, rest3) =>
                match codeReg (p.b * 8 + rm) with
                | some base => some (r, .mem base d, 6, rest3)
                | none => none
              | none => none
            else none
          | [] => none
        else
          match parseLe32 rest with
          | some (d, rest2) =>
            match codeReg (p.b * 8 + rm) with
            | some base => some (r, .mem base d, 5, rest2)
            | none => none
          | none => none
      else none

/-- Group decode for the by-one and by-CL shifts. -/
def ixShiftGruppe (p : RotPraefix) (is8 : Bool) (q : IxZaehler) :
    List Byte → Option (IxDecodiert × List Byte)
  | bs =>
    if p.r == 1 || p.x == 1 then none
    else match rotBreite is8 p with
    | none => none
    | some b =>
      match ixShiftModrm p bs with
      | some (r, operand, ml, rest) =>
        some (⟨.shift ⟨r, b, q, operand⟩, p.n + 1 + ml⟩, rest)
      | none => none

/-- Group decode for the imm8 shifts. -/
def ixShiftGruppeImm (p : RotPraefix) (is8 : Bool) :
    List Byte → Option (IxDecodiert × List Byte)
  | bs =>
    if p.r == 1 || p.x == 1 then none
    else match rotBreite is8 p with
    | none => none
    | some b =>
      match ixShiftModrm p bs with
      | some (r, operand, ml, ib :: rest) =>
        some (⟨.shift ⟨r, b, .imm8 (byteNat ib), operand⟩, p.n + 2 + ml⟩,
          rest)
      | _ => none

/-- 0F B6/B7/BE/BF rows: destination width from the prefix. -/
def ixExtNachOp (p : RotPraefix) (m : IxExtModus) (is8 : Bool) :
    List Byte → Option (IxDecodiert × List Byte)
  | bs =>
    if p.x == 1 then none
    else match rotBreite false p with
    | none => none
    | some w =>
      match ixZielAusBreite w with
      | none => none
      | some zw =>
        match ixModrmExt p is8 bs with
        | some (dst, src, rest) =>
          some (⟨.ext m zw dst src, p.n + 3⟩, rest)
        | none => none

/-- Opcode 63 rows (MOVSXD): 66h refuses, REX.W selects 64 bits. -/
def ixSxd (p : RotPraefix) :
    List Byte → Option (IxDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if p.op16 then none
    else if p.x == 1 then none
    else if byteNat m / 64 == 3 then
      match codeReg (p.r * 8 + byteNat m / 8 % 8),
          codeReg (p.b * 8 + byteNat m % 8) with
      | some dst, some src =>
        some (⟨.sxd (p.w == 1) dst src, p.n + 2⟩, rest)
      | _, _ => none
    else none

/-- 0F C8+rd rows (BSWAP): 66h refuses, REX.W selects 64 bits. -/
def ixBswap (p : RotPraefix) :
    List Byte → Option (IxDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    if p.op16 then none
    else
      let rd := byteNat op - 200
      if decide (200 ≤ byteNat op) && decide (byteNat op < 208) then
        match codeReg (p.b * 8 + rd) with
        | some r => some (⟨.bswap (p.w == 1) r, p.n + 2⟩, rest)
        | none => none
      else none

/-- Double-shift rows with a CL count. -/
def ixShldCl (p : RotPraefix) (links : Bool) :
    List Byte → Option (IxDecodiert × List Byte)
  | bs =>
    if p.x == 1 then none
    else match rotBreite false p with
    | none => none
    | some w =>
      match ixZielAusBreite w with
      | none => none
      | some zw =>
        match ixModrmShld p bs with
        | some (src, dst, rest) =>
          some (⟨.shld links zw .cl dst src, p.n + 3⟩, rest)
        | none => none

/-- Double-shift rows with an imm8 count. -/
def ixShldImm (p : RotPraefix) (links : Bool) :
    List Byte → Option (IxDecodiert × List Byte)
  | bs =>
    if p.x == 1 then none
    else match rotBreite false p with
    | none => none
    | some w =>
      match ixZielAusBreite w with
      | none => none
      | some zw =>
      match ixModrmShld p bs with
      | some (src, dst, ib :: rest) =>
        some (⟨.shld links zw (.imm8 (byteNat ib)) dst src, p.n + 4⟩,
          rest)
      | _ => none

/-- 0F-escape dispatch: extension, double shift, byte swap. -/
def ixNach0F (p : RotPraefix) :
    List Byte → Option (IxDecodiert × List Byte)
  | [] => none
  | op2 :: rest =>
    let n := byteNat op2
    if n == 182 then ixExtNachOp p .zx8 true rest
    else if n == 183 then ixExtNachOp p .zx16 false rest
    else if n == 190 then ixExtNachOp p .sx8 true rest
    else if n == 191 then ixExtNachOp p .sx16 false rest
    else if n == 164 then ixShldImm p true rest
    else if n == 165 then ixShldCl p true rest
    else if n == 172 then ixShldImm p false rest
    else if n == 173 then ixShldCl p false rest
    else if decide (200 ≤ n) && decide (n < 208) then
      ixBswap p (op2 :: rest)
    else none

/-- Opcode dispatch after the prefix. -/
def ixNachOpcode (p : RotPraefix) :
    List Byte → Option (IxDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    let n := byteNat op
    if n == 99 then ixSxd p rest
    else if n == 208 then ixShiftGruppe p true .eins rest
    else if n == 209 then ixShiftGruppe p false .eins rest
    else if n == 210 then ixShiftGruppe p true .cl rest
    else if n == 211 then ixShiftGruppe p false .cl rest
    else if n == 192 then ixShiftGruppeImm p true rest
    else if n == 193 then ixShiftGruppeImm p false rest
    else if n == 15 then ixNach0F p rest
    else none

/-- Full family decode: prefix then opcode, ModRM and immediates. -/
def decodeIntExtend : List Byte → Option (IxDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    match rotNimmPraefix (b :: rest) with
    | none => none
    | some (p, tail) => ixNachOpcode p tail

/-! ## 5. Canonical encoding and decoded length. -/

/-- Second opcode byte of an extension row. -/
def ixExtOp2 : IxExtModus → Nat
  | .zx8 => 182 | .zx16 => 183 | .sx8 => 190 | .sx16 => 191

/-- Canonical prefix of an extension row: 66h for a 16-bit
    destination, REX.W for 64 bits, REX.R/B for high registers, and
    a bare REX where an 8-bit source needs SPL/BPL/SIL/DIL. -/
def ixExtPraefix (m : IxExtModus) (w : IxZielBreite)
    (dst src : Register) :
    List Byte :=
  let op16 : List Byte :=
    match w with | .w16 => [natByte 102] | _ => []
  let wbit : Nat := match w with | .w64 => 8 | _ => 0
  let need8 : Bool :=
    match m with
    | .zx8 => decide (4 ≤ regLow src)
    | .sx8 => decide (4 ≤ regLow src)
    | _ => false
  let rex : List Byte :=
    if wbit + 4 * regHigh dst + regHigh src == 0 && !need8 then []
    else [natByte (64 + wbit + 4 * regHigh dst + regHigh src)]
  op16 ++ rex

/-- Canonical REX for the MOVSXD row: W for 64 bits, R for a
    high destination (reg field), B for a high source. -/
def ixRex2 (w64 : Bool) (dst src : Register) : List Byte :=
  let w : Nat := match w64 with | true => 8 | false => 0
  if w + 4 * regHigh dst + regHigh src == 0 then []
  else [natByte (64 + w + 4 * regHigh dst + regHigh src)]

/-- Canonical REX for BSWAP: W for 64 bits, B for a high register. -/
def ixRexB (w64 : Bool) (r : Register) : List Byte :=
  let w : Nat := match w64 with | true => 8 | false => 0
  if w + regHigh r == 0 then []
  else [natByte (64 + w + regHigh r)]

/-- Canonical prefix of a double shift: 66h for 16 bits, REX.W for
    64 bits, REX.R/B for high source/destination registers. -/
def ixShldPraefix (w : IxZielBreite) (dst src : Register) : List Byte :=
  let op16 : List Byte :=
    match w with | .w16 => [natByte 102] | _ => []
  let wbit : Nat := match w with | .w64 => 8 | _ => 0
  let rex : List Byte :=
    if wbit + 4 * regHigh src + regHigh dst == 0 then []
    else [natByte (64 + wbit + 4 * regHigh src + regHigh dst)]
  op16 ++ rex

/-- Group opcode byte of a shift width and count source. -/
def ixShiftOpcode : Breite → IxZaehler → Nat
  | .b8, .eins => 208
  | .b8, .cl => 210
  | .b8, .imm8 _ => 192
  | _, .eins => 209
  | _, .cl => 211
  | _, .imm8 _ => 193

/-- ModRM byte of a shift form. -/
def ixShiftModrmByte (f : IxShiftForm) : Nat :=
  match f.operand with
  | .reg dst => 192 + 8 * ixRichtungFeld f.dir + regLow dst
  | .mem base _ => 128 + 8 * ixRichtungFeld f.dir + regLow base

/-- Second opcode byte of a double shift. -/
def ixShldOp2 : Bool → IxDoppelZaehler → Nat
  | true, .cl => 165
  | true, .imm8 _ => 164
  | false, .cl => 173
  | false, .imm8 _ => 172

/-- Canonical bytes of one family instruction. -/
def ixEncode : IxBefehl → List Byte
  | .ext m w dst src =>
    ixExtPraefix m w dst src ++ [natByte 15, natByte (ixExtOp2 m),
      natByte (192 + 8 * regLow dst + regLow src)]
  | .sxd w64 dst src =>
    ixRex2 w64 dst src ++ [natByte 99,
      natByte (192 + 8 * regLow dst + regLow src)]
  | .bswap w64 r =>
    ixRexB w64 r ++ [natByte 15, natByte (200 + regLow r)]
  | .shift f =>
    (match f.operand with
     | .reg dst => rotPraefixBytes f.breite dst
     | .mem base _ => rotPraefixBytes f.breite base) ++
    [natByte (ixShiftOpcode f.breite f.quelle),
     natByte (ixShiftModrmByte f)] ++
    (match f.operand with
     | .reg _ => []
     | .mem base d => rotSibTail base ++ leBytes32 d) ++
    (match f.quelle with | .imm8 n => [natByte n] | _ => [])
  | .shld links w q dst src =>
    ixShldPraefix w dst src ++
      [natByte 15, natByte (ixShldOp2 links q),
       natByte (192 + 8 * regLow src + regLow dst)] ++
    (match q with | .imm8 n => [natByte n] | _ => [])

/-- Decoded length of one family instruction. -/
def ixLaenge : IxBefehl → Nat
  | .ext m w dst src => (ixExtPraefix m w dst src).length + 3
  | .sxd w64 dst src => (ixRex2 w64 dst src).length + 2
  | .bswap w64 r => (ixRexB w64 r).length + 2
  | .shift f =>
    (match f.operand with
     | .reg dst => rotPraefixBytes f.breite dst
     | .mem base _ => rotPraefixBytes f.breite base).length + 2 +
    (match f.operand with
     | .reg _ => 0
     | .mem base _ => (rotSibTail base).length + 4) +
    (match f.quelle with | .imm8 _ => 1 | _ => 0)
  | .shld _ w q dst src =>
    (ixShldPraefix w dst src).length + 3 +
    (match q with | .imm8 _ => 1 | _ => 0)

/-- The encoding is exactly the decoded length. -/
theorem ixEncode_laenge (f : IxBefehl) :
    (ixEncode f).length = ixLaenge f := by
  cases f with
  | ext m w dst src => simp [ixEncode, ixLaenge]
  | sxd w64 dst src => simp [ixEncode, ixLaenge]
  | bswap w64 r => simp [ixEncode, ixLaenge]
  | shift g =>
    cases g with
    | mk dir b q operand =>
      cases operand with
      | reg dst =>
        cases q with
        | eins => simp [ixEncode, ixLaenge]
        | cl => simp [ixEncode, ixLaenge]
        | imm8 ib => simp [ixEncode, ixLaenge]
      | mem base d =>
        have he : (leBytes32 d).length = 4 := rfl
        cases q with
        | eins => simp [ixEncode, ixLaenge, he]; omega
        | cl => simp [ixEncode, ixLaenge, he]; omega
        | imm8 ib => simp [ixEncode, ixLaenge, he]; omega
  | shld links w q dst src =>
    cases q with
    | cl => simp [ixEncode, ixLaenge]
    | imm8 ib => simp [ixEncode, ixLaenge]

/-- An extension prefix is at most two bytes. -/
theorem ixExtPraefix_len_le (m : IxExtModus) (w : IxZielBreite)
    (dst src : Register) :
    (ixExtPraefix m w dst src).length ≤ 2 := by
  cases m <;> cases w <;> cases dst <;> cases src <;> decide

/-- A MOVSXD REX prefix is at most one byte. -/
theorem ixRex2_len_le (w64 : Bool) (dst src : Register) :
    (ixRex2 w64 dst src).length ≤ 1 := by
  cases w64 <;> cases dst <;> cases src <;> decide

/-- A BSWAP REX prefix is at most one byte. -/
theorem ixRexB_len_le (w64 : Bool) (r : Register) :
    (ixRexB w64 r).length ≤ 1 := by
  cases w64 <;> cases r <;> decide

/-- A double-shift prefix is at most two bytes. -/
theorem ixShldPraefix_len_le (w : IxZielBreite) (dst src : Register) :
    (ixShldPraefix w dst src).length ≤ 2 := by
  cases w <;> cases dst <;> cases src <;> decide

/-- Every family encoding fits the 1 to 15 instruction bound. -/
theorem ixEncode_len_ok (f : IxBefehl) :
    1 ≤ (ixEncode f).length ∧ (ixEncode f).length ≤ 15 := by
  rw [ixEncode_laenge]
  cases f with
  | ext m w dst src =>
    have h := ixExtPraefix_len_le m w dst src
    simp only [ixLaenge]
    omega
  | sxd w64 dst src =>
    have h := ixRex2_len_le w64 dst src
    simp only [ixLaenge]
    omega
  | bswap w64 r =>
    have h := ixRexB_len_le w64 r
    simp only [ixLaenge]
    omega
  | shift g =>
    cases g with
    | mk dir b q operand =>
      cases operand with
      | reg dst =>
        have hp := rotPraefixBytes_len b dst
        cases q with
        | eins => simp only [ixLaenge]; omega
        | cl => simp only [ixLaenge]; omega
        | imm8 ib => simp only [ixLaenge]; omega
      | mem base d =>
        have hp := rotPraefixBytes_len b base
        have hs := rotSibTail_len base
        cases q with
        | eins => simp only [ixLaenge]; omega
        | cl => simp only [ixLaenge]; omega
        | imm8 ib => simp only [ixLaenge]; omega
  | shld links w q dst src =>
    have h := ixShldPraefix_len_le w dst src
    cases q with
    | cl => simp only [ixLaenge]; omega
    | imm8 ib => simp only [ixLaenge]; omega

/-! ## 6. Round trips, pins and planted refusals. -/

/-- Round trip for extension rows, over any suffix. -/
theorem ixRoundtrip_ext (m : IxExtModus) (w : IxZielBreite)
    (dst src : Register)
    (suffix : List Byte) :
    decodeIntExtend (ixEncode (.ext m w dst src) ++ suffix) =
      some (⟨.ext m w dst src, ixLaenge (.ext m w dst src)⟩,
        suffix) := by
  cases m <;> cases w <;> cases dst <;> cases src <;> rfl

/-- Round trip for MOVSXD rows, over any suffix. -/
theorem ixRoundtrip_sxd (w64 : Bool) (dst src : Register)
    (suffix : List Byte) :
    decodeIntExtend (ixEncode (.sxd w64 dst src) ++ suffix) =
      some (⟨.sxd w64 dst src, ixLaenge (.sxd w64 dst src)⟩,
        suffix) := by
  cases w64 <;> cases dst <;> cases src <;> rfl

/-- Round trip for BSWAP rows, over any suffix. -/
theorem ixRoundtrip_bswap (w64 : Bool) (r : Register)
    (suffix : List Byte) :
    decodeIntExtend (ixEncode (.bswap w64 r) ++ suffix) =
      some (⟨.bswap w64 r, ixLaenge (.bswap w64 r)⟩, suffix) := by
  cases w64 <;> cases r <;> rfl

/-- Round trip for by-one register shifts, over any suffix. -/
theorem ixRoundtrip_shift_eins (r : IxShiftRichtung) (b : Breite)
    (dst : Register) (suffix : List Byte) :
    decodeIntExtend
        (ixEncode (.shift ⟨r, b, .eins, .reg dst⟩) ++ suffix) =
      some (⟨.shift ⟨r, b, .eins, .reg dst⟩,
        ixLaenge (.shift ⟨r, b, .eins, .reg dst⟩)⟩, suffix) := by
  cases r <;> cases b <;> cases dst <;> rfl

/-- Round trip for by-CL register shifts, over any suffix. -/
theorem ixRoundtrip_shift_cl (r : IxShiftRichtung) (b : Breite)
    (dst : Register) (suffix : List Byte) :
    decodeIntExtend
        (ixEncode (.shift ⟨r, b, .cl, .reg dst⟩) ++ suffix) =
      some (⟨.shift ⟨r, b, .cl, .reg dst⟩,
        ixLaenge (.shift ⟨r, b, .cl, .reg dst⟩)⟩, suffix) := by
  cases r <;> cases b <;> cases dst <;> rfl

/-- Closed ground truth: one imm8 round trip, no free variables. -/
theorem diag_imm_closed :
    decodeIntExtend [natByte 192, natByte 224, natByte 7] =
      some (⟨.shift ⟨.shl, .b8, .imm8 7, .reg .rax⟩, 3⟩,
        []) := by
  rfl

/-- Diagnostic: closed imm byte, free suffix. -/
theorem diag_imm_suffix (suffix : List Byte) :
    decodeIntExtend ([natByte 192, natByte 224, natByte 7] ++ suffix) =
      some (⟨.shift ⟨.shl, .b8, .imm8 7, .reg .rax⟩, 3⟩,
        suffix) := by
  rfl

/-- Diagnostic: length with a free imm count. -/
theorem diag_laenge_ib (n : Nat) :
    ixLaenge (.shift ⟨.shl, .b8, .imm8 n, .reg .rax⟩) = 3 := by
  rfl

/-- Closed ground truth: shl.b8.rcx.imm8. -/
theorem pin_ix_shlrcx_rt :
    decodeIntExtend [natByte 192, natByte 225, natByte 7] =
      some (⟨.shift ⟨.shl, .b8, .imm8 7, .reg .rcx⟩, 3⟩,
        []) := by
  rfl

/-- Kernel Nat.div on zero numerator. -/
theorem diag_natdiv0 : (0 / 8 == 0) = true := by rfl

/-- Kernel Nat.div on nonzero numerator. -/
theorem diag_natdiv1 : (1 / 8 == 0) = true := by rfl

/-- Kernel Nat.mod on nonzero numerator. -/
theorem diag_natmod1 : 1 % 8 = 1 := by rfl

/-- Kernel Nat.div on a ModRM byte. -/
theorem diag_natdiv225 : 225 / 8 = 28 := by rfl

/-- Closed ground truth: shl.b16.rdx.imm8. -/
theorem pin_ix_shlrdx16_rt :
    decodeIntExtend
      [natByte 102, natByte 193, natByte 226, natByte 7] =
      some (⟨.shift ⟨.shl, .b16, .imm8 7, .reg .rdx⟩, 4⟩,
        []) := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
/-- Round trip for imm8 register shifts, 8-bit width. -/
theorem ixRoundtrip_shift_imm8 (r : IxShiftRichtung)
    (dst : Register) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeIntExtend
        (ixEncode (.shift ⟨r, .b8, .imm8 n, .reg dst⟩) ++ suffix) =
      some (⟨.shift ⟨r, .b8, .imm8 n, .reg dst⟩,
        ixLaenge (.shift ⟨r, .b8, .imm8 n, .reg dst⟩)⟩,
        suffix) := by
  cases r <;> cases dst <;>
    simp [ixEncode, decodeIntExtend, ixNachOpcode, ixShiftGruppeImm,
      ixShiftModrm, ixFeldRichtung, rotNimmPraefix, rotNimmRex, rotBreite,
      ixRichtungFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      ixShiftOpcode, ixShiftModrmByte, ixLaenge, (byteNat_natByte_of_lt n h)]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
/-- Round trip for imm8 register shifts, 16-bit width. -/
theorem ixRoundtrip_shift_imm16 (r : IxShiftRichtung)
    (dst : Register) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeIntExtend
        (ixEncode (.shift ⟨r, .b16, .imm8 n, .reg dst⟩) ++ suffix) =
      some (⟨.shift ⟨r, .b16, .imm8 n, .reg dst⟩,
        ixLaenge (.shift ⟨r, .b16, .imm8 n, .reg dst⟩)⟩,
        suffix) := by
  cases r <;> cases dst <;>
    simp [ixEncode, decodeIntExtend, ixNachOpcode, ixShiftGruppeImm,
      ixShiftModrm, ixFeldRichtung, rotNimmPraefix, rotNimmRex, rotBreite,
      ixRichtungFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      ixShiftOpcode, ixShiftModrmByte, ixLaenge, (byteNat_natByte_of_lt n h)]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
/-- Round trip for imm8 register shifts, 32-bit width. -/
theorem ixRoundtrip_shift_imm32 (r : IxShiftRichtung)
    (dst : Register) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeIntExtend
        (ixEncode (.shift ⟨r, .b32, .imm8 n, .reg dst⟩) ++ suffix) =
      some (⟨.shift ⟨r, .b32, .imm8 n, .reg dst⟩,
        ixLaenge (.shift ⟨r, .b32, .imm8 n, .reg dst⟩)⟩,
        suffix) := by
  cases r <;> cases dst <;>
    simp [ixEncode, decodeIntExtend, ixNachOpcode, ixShiftGruppeImm,
      ixShiftModrm, ixFeldRichtung, rotNimmPraefix, rotNimmRex, rotBreite,
      ixRichtungFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      ixShiftOpcode, ixShiftModrmByte, ixLaenge, (byteNat_natByte_of_lt n h)]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
/-- Round trip for imm8 register shifts, 64-bit width. -/
theorem ixRoundtrip_shift_imm64 (r : IxShiftRichtung)
    (dst : Register) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeIntExtend
        (ixEncode (.shift ⟨r, .b64, .imm8 n, .reg dst⟩) ++ suffix) =
      some (⟨.shift ⟨r, .b64, .imm8 n, .reg dst⟩,
        ixLaenge (.shift ⟨r, .b64, .imm8 n, .reg dst⟩)⟩,
        suffix) := by
  cases r <;> cases dst <;>
    simp [ixEncode, decodeIntExtend, ixNachOpcode, ixShiftGruppeImm,
      ixShiftModrm, ixFeldRichtung, rotNimmPraefix, rotNimmRex, rotBreite,
      ixRichtungFeld, codeReg, regHigh, regLow, regCode, rotPraefixBytes,
      ixShiftOpcode, ixShiftModrmByte, ixLaenge, (byteNat_natByte_of_lt n h)]

/-- Closed ground truth: one imm8 round trip with no free variables. -/
theorem pin_ix_sarib_rt :
    decodeIntExtend [natByte 192, natByte 224, natByte 7] =
      some (⟨.shift ⟨.shl, .b8, .imm8 7, .reg .rax⟩, 3⟩,
        []) := by
  rfl

/-- Round trip for double shifts by CL, over any suffix. -/
theorem ixRoundtrip_shld_cl (links : Bool) (w : IxZielBreite)
    (dst src : Register) (suffix : List Byte) :
    decodeIntExtend (ixEncode (.shld links w .cl dst src) ++ suffix) =
      some (⟨.shld links w .cl dst src,
        ixLaenge (.shld links w .cl dst src)⟩, suffix) := by
  cases links <;> cases w <;> cases dst <;> cases src <;> rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
/-- Round trip for double shifts by imm8, over a byte premise. -/
theorem ixRoundtrip_shld_imm (links : Bool) (w : IxZielBreite)
    (dst src : Register) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeIntExtend (ixEncode (.shld links w (.imm8 n) dst src) ++ suffix) =
      some (⟨.shld links w (.imm8 n) dst src,
        ixLaenge (.shld links w (.imm8 n) dst src)⟩, suffix) := by
  cases links <;> cases w <;> cases dst <;> cases src <;>
    simp [ixEncode, decodeIntExtend, ixNachOpcode, ixNach0F, ixShldImm,
      ixModrmShld, rotNimmPraefix, rotNimmRex, rotBreite, ixZielAusBreite,
      codeReg, regHigh, regLow, regCode, ixShldPraefix, ixShldOp2, ixLaenge,
      (byteNat_natByte_of_lt n h)]

/-- Pin: MOVZX r32, r/m16 takes the family arm. -/
theorem pin_ix_movzx16 :
    decodeIntExtend [natByte 15, natByte 183, natByte 193] =
      some (⟨.ext .zx16 .w32 .rax .rcx, 3⟩, []) := by
  decide

/-- Pin: MOVSXD r64 takes the family arm. -/
theorem pin_ix_sxd64 :
    decodeIntExtend [natByte 72, natByte 99, natByte 193] =
      some (⟨.sxd true .rax .rcx, 3⟩, []) := by
  decide

/-- Pin: BSWAP eax takes the family arm. -/
theorem pin_ix_bswap32 :
    decodeIntExtend [natByte 15, natByte 200] =
      some (⟨.bswap false .rax, 2⟩, []) := by
  decide

/-- Pin: SHL Eb,1 takes the family arm. -/
theorem pin_ix_shl1 :
    decodeIntExtend [natByte 208, natByte 227] =
      some (⟨.shift ⟨.shl, .b8, .eins, .reg .rbx⟩, 2⟩, []) := by
  decide

/-- Pin: SHR Ev,1 (32-bit) takes the family arm. -/
theorem pin_ix_shr1w :
    decodeIntExtend [natByte 209, natByte 237] =
      some (⟨.shift ⟨.shr, .b32, .eins, .reg .rbp⟩, 2⟩, []) := by
  decide

/-- Pin: SHL Ev,CL with a disp32 memory operand (family arm). -/
theorem pin_ix_shlcl_mem :
    decodeIntExtend
      [natByte 211, natByte 160, natByte 120, natByte 86,
        natByte 52, natByte 18] =
      some (⟨.shift ⟨.shl, .b32, .cl,
        .mem .rax (BitVec.ofNat 32 0x12345678)⟩, 6⟩, []) := by
  decide

/-- Pin: SAR Eb,ib with the /7 digit (family arm). -/
theorem pin_ix_sarib :
    decodeIntExtend [natByte 192, natByte 251, natByte 3] =
      some (⟨.shift ⟨.sar, .b8, .imm8 3, .reg .rbx⟩, 3⟩,
        []) := by
  decide

/-- Pin: 16-bit SHLD by imm8 takes the family arm. -/
theorem pin_ix_shld16 :
    decodeIntExtend [natByte 102, natByte 15, natByte 164,
        natByte 200, natByte 4] =
      some (⟨.shld true .w16 (.imm8 4) .rax .rcx, 5⟩,
        []) := by
  decide

/-- Pin: SHRD by CL takes the family arm. -/
theorem pin_ix_shrdcl :
    decodeIntExtend [natByte 15, natByte 173, natByte 217] =
      some (⟨.shld false .w32 .cl .rcx .rbx, 3⟩, []) := by
  decide

/-! ## 7. Extended dispatcher over the unified chain.

    The dispatcher tries the accepted unified decoder first and the
    family decoder only where it refuses: no pilot or extension form
    is shadowed. A maintainer wires a row into the machine by adding
    a `decodeIntExtend` arm behind `decodeExt` in
    `ExtendedExecution.lean` (or by routing `IxHwInstr` through
    `fetchExt`); this file states the extended chain as a new
    definition over the old one. -/

/-- Unified dispatcher instruction: the accepted unified chain
    first, the family only where it refuses. -/
inductive IxHwInstr where
  | ext : ExtInstr → IxHwInstr
  | ix : IxDecodiert → IxHwInstr
  deriving DecidableEq, Repr

/-- Dispatcher: the unified decoder first, the family decoder only
    where the unified chain refuses. -/
def decodeIntExtendHw :
    List Byte → Option (IxHwInstr × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.ext i, rest)
    | none =>
      match decodeIntExtend bs with
      | some (d, rest) => some (.ix d, rest)
      | none => none

/-- Consumed length of one dispatcher instruction. -/
def ixHwLen : IxHwInstr → Nat
  | .ext i => extLen i
  | .ix d => d.laenge

/-- The dispatcher agrees with the unified chain wherever it
    accepts: no existing form is shadowed. -/
theorem decodeIntExtendHw_prefers_ext (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeIntExtendHw bs = some (.ext i, rest) := by
  unfold decodeIntExtendHw
  rw [h]

/-- Where the unified chain refuses, a covered family row is taken. -/
theorem decodeIntExtendHw_ix (bs : List Byte) (d : IxDecodiert)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeIntExtend bs = some (d, rest)) :
    decodeIntExtendHw bs = some (.ix d, rest) := by
  unfold decodeIntExtendHw
  rw [h1, h2]

/-- Where both chains refuse, the dispatcher refuses. -/
theorem decodeIntExtendHw_nichts (bs : List Byte)
    (h1 : decodeExt bs = none) (h2 : decodeIntExtend bs = none) :
    decodeIntExtendHw bs = none := by
  unfold decodeIntExtendHw
  rw [h1, h2]

/-! ## 8. No shadowing: the unified chain refuses the new rows. -/

/-- The 16-bit MOVZX row is refused by the unified chain. -/
theorem ext_weist_ixMovzx16_zurueck :
    decodeExt [natByte 15, natByte 183, natByte 193] = none := by
  decide

/-- The 64-bit MOVSXD row is refused by the unified chain. -/
theorem ext_weist_ixMovsxd64_zurueck :
    decodeExt [natByte 72, natByte 99, natByte 193] = none := by
  decide

/-- The BSWAP row is refused by the unified chain. -/
theorem ext_weist_ixBswap_zurueck :
    decodeExt [natByte 15, natByte 200] = none := by
  decide

/-- The byte shift-by-one row is refused by the unified chain. -/
theorem ext_weist_ixShl1_zurueck :
    decodeExt [natByte 208, natByte 227] = none := by
  decide

/-- The wide shift-by-one row is refused by the unified chain. -/
theorem ext_weist_ixShr1w_zurueck :
    decodeExt [natByte 209, natByte 237] = none := by
  decide

/-- The SHLD row is refused by the unified chain. -/
theorem ext_weist_ixShld_zurueck :
    decodeExt [natByte 102, natByte 15, natByte 164, natByte 200,
      natByte 4] = none := by
  decide

/-- Pin: the new MOVZX row takes the family arm. -/
theorem pin_ixHw_movzx16 :
    decodeIntExtendHw [natByte 15, natByte 183, natByte 193] =
      some (.ix ⟨.ext .zx16 .w32 .rax .rcx, 3⟩, []) :=
  decodeIntExtendHw_ix _ _ _ ext_weist_ixMovzx16_zurueck
    pin_ix_movzx16

/-- Pin: the new MOVSXD row takes the family arm. -/
theorem pin_ixHw_sxd64 :
    decodeIntExtendHw [natByte 72, natByte 99, natByte 193] =
      some (.ix ⟨.sxd true .rax .rcx, 3⟩, []) :=
  decodeIntExtendHw_ix _ _ _ ext_weist_ixMovsxd64_zurueck
    pin_ix_sxd64

/-- Pin: the new BSWAP row takes the family arm. -/
theorem pin_ixHw_bswap32 :
    decodeIntExtendHw [natByte 15, natByte 200] =
      some (.ix ⟨.bswap false .rax, 2⟩, []) :=
  decodeIntExtendHw_ix _ _ _ ext_weist_ixBswap_zurueck
    pin_ix_bswap32

/-- Pin: the new shift-by-one row takes the family arm. -/
theorem pin_ixHw_shl1 :
    decodeIntExtendHw [natByte 208, natByte 227] =
      some (.ix ⟨.shift ⟨.shl, .b8, .eins, .reg .rbx⟩, 2⟩, []) :=
  decodeIntExtendHw_ix _ _ _ ext_weist_ixShl1_zurueck pin_ix_shl1

/-- Pin: the new wide shift-by-one row takes the family arm. -/
theorem pin_ixHw_shr1w :
    decodeIntExtendHw [natByte 209, natByte 237] =
      some (.ix ⟨.shift ⟨.shr, .b32, .eins, .reg .rbp⟩, 2⟩, []) :=
  decodeIntExtendHw_ix _ _ _ ext_weist_ixShr1w_zurueck pin_ix_shr1w

/-- Pin: the new SHLD row takes the family arm. -/
theorem pin_ixHw_shld16 :
    decodeIntExtendHw [natByte 102, natByte 15, natByte 164,
        natByte 200, natByte 4] =
      some (.ix ⟨.shld true .w16 (.imm8 4) .rax .rcx, 5⟩,
        []) :=
  decodeIntExtendHw_ix _ _ _ ext_weist_ixShld_zurueck pin_ix_shld16

/-- Pin: the pilot row keeps the unified arm. -/
theorem pin_ixHw_pilot_ret :
    decodeIntExtendHw (encode .ret) =
      some (.ext (.pilot ⟨.ret, 1⟩), []) :=
  decodeIntExtendHw_prefers_ext _ _ _ pin_ext_pilot_ret

/-! ## 9. Planted refusals: what the family decoder rejects. -/

/-- LOCK refuses at the prefix. -/
theorem ix_weist_lock_zu :
    decodeIntExtend [natByte 240, natByte 208, natByte 227] = none := by
  decide

/-- A REX.R over a group row refuses (it would rewrite the digit). -/
theorem ix_weist_rexR_gruppe_zu :
    decodeIntExtend [natByte 68, natByte 209, natByte 227] = none := by
  decide

/-- A rotate digit refuses in the shift group. -/
theorem ix_weist_rot_digit_zu :
    decodeIntExtend [natByte 209, natByte 195] = none := by
  decide

/-- A memory-mode ModRM refuses on extension rows. -/
theorem ix_weist_ext_mem_zu :
    decodeIntExtend [natByte 15, natByte 183, natByte 129] = none := by
  decide

/-- An AH source without REX refuses (no `Register` name for it). -/
theorem ix_weist_ah_ohne_rex_zu :
    decodeIntExtend [natByte 15, natByte 182, natByte 196] = none := by
  decide

/-- 66h refuses on MOVSXD (invalid on silicon). -/
theorem ix_weist_sxd66_zu :
    decodeIntExtend [natByte 102, natByte 99, natByte 193] = none := by
  decide

/-- 66h refuses on BSWAP (no 16-bit form; kept refused). -/
theorem ix_weist_bswap66_zu :
    decodeIntExtend [natByte 102, natByte 15, natByte 200] = none := by
  decide

/-- Truncation refuses: the ModRM byte is missing. -/
theorem ix_weist_rumpf_zu :
    decodeIntExtend [natByte 15, natByte 183] = none := by
  decide

/-- The dispatcher refuses LOCK through both chains. -/
theorem ixHw_weist_lock_zu :
    decodeIntExtendHw [natByte 240, natByte 208, natByte 227] =
      none := by
  have h1 : decodeExt [natByte 240, natByte 208, natByte 227] =
      none := by
    decide
  exact decodeIntExtendHw_nichts _ h1 ix_weist_lock_zu

/-! ## 10. Register-state step.

    Every success arm carries `speicher := s.speicher`; refusals and
    the past-width double shift carry no state at all. Extension and
    byte swap preserve flags (architectural MOV/BSWAP discipline);
    shifts take the §2/§3 snapshots. Memory moves only through the
    TSO issue path (§12), never through a substituted word effect:
    the register plug refuses memory operands. -/

/-- Family outcome: success with a successor state, or refusal. The
    family has no fault: an undefined past-width count refuses. -/
inductive IxAusgang where
  | ok (s' : Zustand)
  | misslungen

/-- CL count: the low eight bits of RCX. -/
def ixClZaehler (s : Zustand) : Nat := (s.register .rcx).toNat % 256

/-- Count value of a single-shift source. -/
def ixZaehlerWert : IxZaehler → Zustand → Nat
  | .eins, _ => 1
  | .cl, s => ixClZaehler s
  | .imm8 n, _ => n

/-- Count value of a double-shift source. -/
def ixDoppelZaehlerWert : IxDoppelZaehler → Zustand → Nat
  | .cl, s => ixClZaehler s
  | .imm8 n, _ => n

/-- One single-shift register step: value through the accepted op
    with narrow-merge writeback, flags through the §2 snapshot. -/
def ixShiftRegSchritt (f : IxShiftForm) (s : Zustand) : IxAusgang :=
  match f.operand with
  | .mem _ _ => .misslungen
  | .reg dst =>
    match f.dir with
    | .shl =>
      .ok { s with
        register := fun q =>
          if q = dst then
            ixZielSchreiben f.breite (s.register dst)
              (shlB f.breite (s.register dst)
                (ixZaehlerWert f.quelle s))
          else s.register q,
        flags := ixShiftSnap .shl f.breite (s.register dst) s.flags
          (ixZaehlerWert f.quelle s) }
    | .shr =>
      .ok { s with
        register := fun q =>
          if q = dst then
            ixZielSchreiben f.breite (s.register dst)
              (shrB f.breite (s.register dst)
                (ixZaehlerWert f.quelle s))
          else s.register q,
        flags := ixShiftSnap .shr f.breite (s.register dst) s.flags
          (ixZaehlerWert f.quelle s) }
    | .sar =>
      .ok { s with
        register := fun q =>
          if q = dst then
            ixZielSchreiben f.breite (s.register dst)
              (sarB f.breite (s.register dst)
                (ixZaehlerWert f.quelle s))
          else s.register q,
        flags := ixShiftSnap .sar f.breite (s.register dst) s.flags
          (ixZaehlerWert f.quelle s) }

/-- A shift register step leaves canonical memory alone. -/
theorem ixShiftRegSchritt_speicher (f : IxShiftForm) (s s' : Zustand)
    (h : ixShiftRegSchritt f s = .ok s') :
    s'.speicher = s.speicher := by
  unfold ixShiftRegSchritt at h
  cases hop : f.operand with
  | reg dst =>
    simp [hop] at h
    cases hdir : f.dir with
    | shl => simp [hdir] at h; cases h; rfl
    | shr => simp [hdir] at h; cases h; rfl
    | sar => simp [hdir] at h; cases h; rfl
  | mem base d => simp [hop] at h

/-- A shift memory operand admits no register step. -/
theorem ixShiftRegSchritt_mem (r : IxShiftRichtung) (b : Breite)
    (q : IxZaehler) (base : Register) (d : BitVec 32) (s : Zustand) :
    ixShiftRegSchritt ⟨r, b, q, .mem base d⟩ s = .misslungen := by
  simp [ixShiftRegSchritt]

/-- One double-shift register step: past-width counts refuse (the
    result is undefined on silicon and is never pinned). -/
def ixShldRegSchritt (links : Bool) (w : Breite)
    (q : IxDoppelZaehler) (dst src : Register) (s : Zustand) :
    IxAusgang :=
  if schiebeZaehler w (ixDoppelZaehlerWert q s) ≤ w.bits then
    match links with
    | true =>
      .ok { s with
        register := fun a =>
          if a = dst then
            ixZielSchreiben w (s.register dst)
              (shldB w (s.register dst) (s.register src)
                (ixDoppelZaehlerWert q s))
          else s.register a,
        flags := shldFlags w (s.register dst) (s.register src)
          s.flags (ixDoppelZaehlerWert q s) }
    | false =>
      .ok { s with
        register := fun a =>
          if a = dst then
            ixZielSchreiben w (s.register dst)
              (shrdB w (s.register dst) (s.register src)
                (ixDoppelZaehlerWert q s))
          else s.register a,
        flags := shrdFlags w (s.register dst) (s.register src)
          s.flags (ixDoppelZaehlerWert q s) }
  else .misslungen

/-- A double-shift register step leaves canonical memory alone. -/
theorem ixShldRegSchritt_speicher (links : Bool) (w : Breite)
    (q : IxDoppelZaehler) (dst src : Register) (s s' : Zustand)
    (h : ixShldRegSchritt links w q dst src s = .ok s') :
    s'.speicher = s.speicher := by
  unfold ixShldRegSchritt at h
  by_cases hk : schiebeZaehler w (ixDoppelZaehlerWert q s) ≤ w.bits
  · simp [hk] at h
    cases links with
    | true => simp at h; cases h; rfl
    | false => simp at h; cases h; rfl
  · simp [hk] at h

/-- A past-width double-shift count refuses the register step. -/
theorem ixShldRegSchritt_weit (links : Bool) (w : Breite)
    (q : IxDoppelZaehler) (dst src : Register) (s : Zustand)
    (hweit : w.bits <
      schiebeZaehler w (ixDoppelZaehlerWert q s)) :
    ixShldRegSchritt links w q dst src s = .misslungen := by
  have hle : ¬ schiebeZaehler w (ixDoppelZaehlerWert q s) ≤ w.bits := by
    omega
  unfold ixShldRegSchritt
  simp [hle]

/-- One family step on a core state. -/
def ixSchritt (d : IxDecodiert) (s : Zustand) : IxAusgang :=
  match laengeOk d.laenge with
  | false => .misslungen
  | true =>
    match d.befehl with
    | .ext m w dst src =>
      .ok { s with
        register := fun q =>
          if q = dst then
            ixZielSchreiben (ixZielBreite w) (s.register dst)
              (ixExtWert m (s.register src))
          else s.register q }
    | .sxd w64 dst src =>
      .ok { s with
        register := fun q =>
          if q = dst then
            match w64 with
            | true =>
              ixZielSchreiben .b64 (s.register dst)
                (ixMovsxdWert (s.register src))
            | false =>
              ixZielSchreiben .b32 (s.register dst)
                (ixMovsxdWert (s.register src))
          else s.register q }
    | .bswap w64 r =>
      .ok { s with
        register := fun q =>
          if q = r then
            match w64 with
            | true => bswap64 (s.register r)
            | false => bswap32 (s.register r)
          else s.register q }
    | .shift f => ixShiftRegSchritt f s
    | .shld links w q dst src =>
      ixShldRegSchritt links (ixZielBreite w) q dst src s

/-- A bad decode length refuses every family form. -/
theorem ix_laenge_misslungen (d : IxDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) :
    ixSchritt d s = .misslungen := by
  unfold ixSchritt
  simp [h]

/-- A successful family step leaves canonical memory alone. -/
theorem ixSchritt_speicher (d : IxDecodiert) (s s' : Zustand)
    (h : ixSchritt d s = .ok s') :
    s'.speicher = s.speicher := by
  unfold ixSchritt at h
  cases hlen : laengeOk d.laenge with
  | false => simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases hbef : d.befehl with
    | ext m w dst src => simp [hbef] at h; cases h; rfl
    | sxd w64 dst src =>
      simp [hbef] at h
      cases w64 with
      | true => simp at h; cases h; rfl
      | false => simp at h; cases h; rfl
    | bswap w64 r =>
      simp [hbef] at h
      cases w64 with
      | true => simp at h; cases h; rfl
      | false => simp at h; cases h; rfl
    | shift f =>
      simp [hbef] at h
      exact ixShiftRegSchritt_speicher f s s' h
    | shld links w q dst src =>
      simp [hbef] at h
      exact ixShldRegSchritt_speicher links (ixZielBreite w) q dst src
        s s' h

/-- A shift memory operand admits no family step. -/
theorem ixSchritt_mem_verweigert (r : IxShiftRichtung) (b : Breite)
    (q : IxZaehler) (base : Register) (d : BitVec 32) (l : Nat)
    (s : Zustand) (hok : laengeOk l = true) :
    ixSchritt ⟨.shift ⟨r, b, q, .mem base d⟩, l⟩ s =
      .misslungen := by
  unfold ixSchritt
  simp [hok, ixShiftRegSchritt]

/-- A past-width double-shift count admits no family step. -/
theorem ixSchritt_shld_weit_verweigert (links : Bool) (w : IxZielBreite)
    (q : IxDoppelZaehler) (dst src : Register) (l : Nat) (s : Zustand)
    (hok : laengeOk l = true)
    (hweit : (ixZielBreite w).bits <
      schiebeZaehler (ixZielBreite w) (ixDoppelZaehlerWert q s)) :
    ixSchritt ⟨.shld links w q dst src, l⟩ s = .misslungen := by
  have hle : ¬ schiebeZaehler (ixZielBreite w) (ixDoppelZaehlerWert q s) ≤
      (ixZielBreite w).bits := by
    omega
  unfold ixSchritt
  simp [hok, hle, ixShldRegSchritt]

/-! ## 11. Step agreement: the step runs the accepted evaluators.

    Each arm writes exactly the §1-§3 value with the architectural
    writeback; extension and byte swap preserve flags, shifts take
    the evidence snapshots. -/

/-- The extension step writes the accepted value and keeps flags. -/
theorem ixSchritt_ext_reg (m : IxExtModus) (w : IxZielBreite)
    (dst src : Register) (l : Nat) (s s' : Zustand)
    (hok : laengeOk l = true)
    (h : ixSchritt ⟨.ext m w dst src, l⟩ s = .ok s') :
    s'.register dst =
        ixZielSchreiben (ixZielBreite w) (s.register dst)
          (ixExtWert m (s.register src)) ∧
      s'.flags = s.flags := by
  unfold ixSchritt at h
  simp [hok] at h
  cases h
  exact ⟨by simp, rfl⟩

/-- The 64-bit MOVSXD step writes the accepted value. -/
theorem ixSchritt_sxd64_reg (dst src : Register) (l : Nat)
    (s s' : Zustand) (hok : laengeOk l = true)
    (h : ixSchritt ⟨.sxd true dst src, l⟩ s = .ok s') :
    s'.register dst = ixMovsxdWert (s.register src) ∧
      s'.flags = s.flags := by
  unfold ixSchritt at h
  simp [hok] at h
  cases h
  refine ⟨?_, rfl⟩
  simp [ixZielSchreiben, mergeRegNarrow_b64, ixMovsxdWert]

/-- The 32-bit MOVSXD step writes zero-extended. -/
theorem ixSchritt_sxd32_reg (dst src : Register) (l : Nat)
    (s s' : Zustand) (hok : laengeOk l = true)
    (h : ixSchritt ⟨.sxd false dst src, l⟩ s = .ok s') :
    s'.register dst =
        trunc .b32 (ixMovsxdWert (s.register src)) ∧
      s'.flags = s.flags := by
  unfold ixSchritt at h
  simp [hok] at h
  cases h
  refine ⟨?_, rfl⟩
  simp [ixZielSchreiben, mergeRegNarrow_b32]

/-- The 64-bit BSWAP step writes the accepted reversal. -/
theorem ixSchritt_bswap64_reg (r : Register) (l : Nat)
    (s s' : Zustand) (hok : laengeOk l = true)
    (h : ixSchritt ⟨.bswap true r, l⟩ s = .ok s') :
    s'.register r = bswap64 (s.register r) ∧
      s'.flags = s.flags := by
  unfold ixSchritt at h
  simp [hok] at h
  cases h
  exact ⟨by simp, rfl⟩

/-- The 32-bit BSWAP step writes the accepted reversal. -/
theorem ixSchritt_bswap32_reg (r : Register) (l : Nat)
    (s s' : Zustand) (hok : laengeOk l = true)
    (h : ixSchritt ⟨.bswap false r, l⟩ s = .ok s') :
    s'.register r = bswap32 (s.register r) ∧
      s'.flags = s.flags := by
  unfold ixSchritt at h
  simp [hok] at h
  cases h
  exact ⟨by simp, rfl⟩

/-- The shift step writes the routed accepted value. -/
theorem ixSchritt_shift_reg (dir : IxShiftRichtung) (b : Breite)
    (q : IxZaehler) (dst : Register) (l : Nat) (s s' : Zustand)
    (hok : laengeOk l = true)
    (h : ixSchritt ⟨.shift ⟨dir, b, q, .reg dst⟩, l⟩ s =
      .ok s') :
    s'.register dst =
      ixZielSchreiben b (s.register dst)
        (ixShiftWert dir b (s.register dst)
          (ixZaehlerWert q s)) := by
  cases dir with
  | shl =>
    unfold ixSchritt at h
    simp [hok, ixShiftRegSchritt] at h
    cases h
    simp [ixShiftWert]
  | shr =>
    unfold ixSchritt at h
    simp [hok, ixShiftRegSchritt] at h
    cases h
    simp [ixShiftWert]
  | sar =>
    unfold ixSchritt at h
    simp [hok, ixShiftRegSchritt] at h
    cases h
    simp [ixShiftWert]

/-- The shift step takes the evidence snapshot. -/
theorem ixSchritt_shift_flags (dir : IxShiftRichtung) (b : Breite)
    (q : IxZaehler) (dst : Register) (l : Nat) (s s' : Zustand)
    (hok : laengeOk l = true)
    (h : ixSchritt ⟨.shift ⟨dir, b, q, .reg dst⟩, l⟩ s =
      .ok s') :
    s'.flags =
      ixShiftSnap dir b (s.register dst) s.flags
        (ixZaehlerWert q s) := by
  cases dir with
  | shl =>
    unfold ixSchritt at h
    simp [hok, ixShiftRegSchritt] at h
    cases h
    rfl
  | shr =>
    unfold ixSchritt at h
    simp [hok, ixShiftRegSchritt] at h
    cases h
    rfl
  | sar =>
    unfold ixSchritt at h
    simp [hok, ixShiftRegSchritt] at h
    cases h
    rfl

/-- The double-shift step writes the accepted value. -/
theorem ixSchritt_shld_reg (links : Bool) (w : IxZielBreite)
    (q : IxDoppelZaehler) (dst src : Register) (l : Nat)
    (s s' : Zustand) (hok : laengeOk l = true)
    (hfit : schiebeZaehler (ixZielBreite w) (ixDoppelZaehlerWert q s) ≤
      (ixZielBreite w).bits)
    (h : ixSchritt ⟨.shld links w q dst src, l⟩ s = .ok s') :
    s'.register dst =
      ixZielSchreiben (ixZielBreite w) (s.register dst)
        (if links then
          shldB (ixZielBreite w) (s.register dst) (s.register src)
            (ixDoppelZaehlerWert q s)
        else
          shrdB (ixZielBreite w) (s.register dst) (s.register src)
            (ixDoppelZaehlerWert q s)) := by
  cases links with
  | true =>
    unfold ixSchritt at h
    simp [hok, hfit, ixShldRegSchritt] at h
    cases h
    simp
  | false =>
    unfold ixSchritt at h
    simp [hok, hfit, ixShldRegSchritt] at h
    cases h
    simp

/-- The double-shift step takes the evidence snapshot. -/
theorem ixSchritt_shld_flags (links : Bool) (w : IxZielBreite)
    (q : IxDoppelZaehler) (dst src : Register) (l : Nat)
    (s s' : Zustand) (hok : laengeOk l = true)
    (hfit : schiebeZaehler (ixZielBreite w) (ixDoppelZaehlerWert q s) ≤
      (ixZielBreite w).bits)
    (h : ixSchritt ⟨.shld links w q dst src, l⟩ s = .ok s') :
    s'.flags =
      (if links then
        shldFlags (ixZielBreite w) (s.register dst) (s.register src)
          s.flags (ixDoppelZaehlerWert q s)
      else
        shrdFlags (ixZielBreite w) (s.register dst) (s.register src)
          s.flags (ixDoppelZaehlerWert q s)) := by
  cases links with
  | true =>
    unfold ixSchritt at h
    simp [hok, hfit, ixShldRegSchritt] at h
    cases h
    rfl
  | false =>
    unfold ixSchritt at h
    simp [hok, hfit, ixShldRegSchritt] at h
    cases h
    rfl

/-! ## 12. Capstone-level chain over `kapDecode`.

    The 64-bit extension rows (REX.W 0F B6/B7/BE/BF, REX.W 63) stay
    with `decodeCore` (the capstone `kern` arm): the overlap pins
    below show the chain taking that arm, never the family arm. Every
    other row of §4 is refused by the whole capstone chain and takes
    the family arm here. A maintainer wires a row into the machine by
    adding a family arm behind `kapDecode` in
    `HwKapsteinDecoder.lean`; this file states that extended chain as
    a new definition over the old one. -/

/-- Capstone-level dispatcher instruction: the accepted capstone
    chain first, the family only where it refuses. -/
inductive IxKapInstr where
  | kap : KapDekodiert → IxKapInstr
  | ix : IxDecodiert → IxKapInstr
  deriving DecidableEq, Repr

/-- Extended chain: the capstone decoder first, the family decoder
    only where the capstone chain refuses. -/
def decodeIntExtendKap :
    List Byte → Option (IxKapInstr × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.kap k, rest)
    | none =>
      match decodeIntExtend bs with
      | some (d, rest) => some (.ix d, rest)
      | none => none

/-- The extended chain agrees with the capstone chain wherever it
    accepts: no modelled row is shadowed. -/
theorem decodeIntExtendKap_prefers_kap (bs : List Byte)
    (k : KapDekodiert) (rest : List Byte)
    (h : kapDecode bs = some (k, rest)) :
    decodeIntExtendKap bs = some (.kap k, rest) := by
  unfold decodeIntExtendKap
  rw [h]

/-- Where the capstone chain refuses, a covered family row is taken. -/
theorem decodeIntExtendKap_ix (bs : List Byte) (d : IxDecodiert)
    (rest : List Byte) (h1 : kapDecode bs = none)
    (h2 : decodeIntExtend bs = some (d, rest)) :
    decodeIntExtendKap bs = some (.ix d, rest) := by
  unfold decodeIntExtendKap
  rw [h1, h2]

/-- Where both chains refuse, the extended chain refuses. -/
theorem decodeIntExtendKap_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : decodeIntExtend bs = none) :
    decodeIntExtendKap bs = none := by
  unfold decodeIntExtendKap
  rw [h1, h2]

/-- The 16-bit MOVZX row is refused by the whole capstone chain. -/
theorem kap_weist_ixMovzx16_zurueck :
    kapDecode [natByte 15, natByte 183, natByte 193] = none := by
  decide

/-- The 32-bit MOVSXD row is refused by the whole capstone chain. -/
theorem kap_weist_ixSxd32_zurueck :
    kapDecode [natByte 99, natByte 193] = none := by
  decide

/-- The BSWAP row is refused by the whole capstone chain. -/
theorem kap_weist_ixBswap_zurueck :
    kapDecode [natByte 15, natByte 200] = none := by
  decide

/-- The byte shift-by-one row is refused by the whole chain. -/
theorem kap_weist_ixShl1_zurueck :
    kapDecode [natByte 208, natByte 227] = none := by
  decide

/-- The wide shift-by-one row is refused by the whole chain. -/
theorem kap_weist_ixShr1w_zurueck :
    kapDecode [natByte 209, natByte 237] = none := by
  decide

/-- The SHLD row is refused by the whole capstone chain. -/
theorem kap_weist_ixShld_zurueck :
    kapDecode [natByte 102, natByte 15, natByte 164, natByte 200,
      natByte 4] = none := by
  decide

/-- Pin: the MOVZX row takes the family arm of the extended chain. -/
theorem pin_ixKap_movzx16 :
    decodeIntExtendKap [natByte 15, natByte 183, natByte 193] =
      some (.ix ⟨.ext .zx16 .w32 .rax .rcx, 3⟩, []) :=
  decodeIntExtendKap_ix _ _ _ kap_weist_ixMovzx16_zurueck
    pin_ix_movzx16

/-- Pin: MOVSXD r32 takes the family arm. -/
theorem pin_ix_sxd32 :
    decodeIntExtend [natByte 99, natByte 193] =
      some (⟨.sxd false .rax .rcx, 2⟩, []) := by
  decide

/-- Pin: the MOVSXD row takes the family arm of the extended chain. -/
theorem pin_ixKap_sxd32 :
    decodeIntExtendKap [natByte 99, natByte 193] =
      some (.ix ⟨.sxd false .rax .rcx, 2⟩, []) :=
  decodeIntExtendKap_ix _ _ _ kap_weist_ixSxd32_zurueck
    pin_ix_sxd32

/-- Pin: the BSWAP row takes the family arm of the extended chain. -/
theorem pin_ixKap_bswap32 :
    decodeIntExtendKap [natByte 15, natByte 200] =
      some (.ix ⟨.bswap false .rax, 2⟩, []) :=
  decodeIntExtendKap_ix _ _ _ kap_weist_ixBswap_zurueck
    pin_ix_bswap32

/-- Pin: the shift-by-one row takes the family arm. -/
theorem pin_ixKap_shl1 :
    decodeIntExtendKap [natByte 208, natByte 227] =
      some (.ix ⟨.shift ⟨.shl, .b8, .eins, .reg .rbx⟩, 2⟩, []) :=
  decodeIntExtendKap_ix _ _ _ kap_weist_ixShl1_zurueck pin_ix_shl1

/-- Pin: the wide shift-by-one row takes the family arm. -/
theorem pin_ixKap_shr1w :
    decodeIntExtendKap [natByte 209, natByte 237] =
      some (.ix ⟨.shift ⟨.shr, .b32, .eins, .reg .rbp⟩, 2⟩, []) :=
  decodeIntExtendKap_ix _ _ _ kap_weist_ixShr1w_zurueck pin_ix_shr1w

/-- Pin: the SHLD row takes the family arm of the extended chain. -/
theorem pin_ixKap_shld16 :
    decodeIntExtendKap [natByte 102, natByte 15, natByte 164,
        natByte 200, natByte 4] =
      some (.ix ⟨.shld true .w16 (.imm8 4) .rax .rcx, 5⟩,
        []) :=
  decodeIntExtendKap_ix _ _ _ kap_weist_ixShld_zurueck pin_ix_shld16

/-- Overlap: the REX.W MOVZX row keeps the capstone `kern` arm
    (`decodeCore` owns the 64-bit extension rows). -/
theorem pin_ixKap_movzx64 :
    kapDecode [natByte 72, natByte 15, natByte 182, natByte 193] =
      some (.kern ⟨.movzx64From8 .rax .rcx, 4⟩, []) := by
  decide

/-- Overlap: the REX.W MOVSXD row keeps the capstone `kern` arm. -/
theorem pin_ixKap_sxd64 :
    kapDecode [natByte 72, natByte 99, natByte 193] =
      some (.kern ⟨.movsx64From32 .rax .rcx, 3⟩, []) := by
  decide

/-- Overlap pin: the REX.W MOVZX row takes the capstone arm of the
    extended chain, never the family arm. -/
theorem pin_ixKapHw_movzx64 :
    decodeIntExtendKap
      [natByte 72, natByte 15, natByte 182, natByte 193] =
      some (.kap (.kern ⟨.movzx64From8 .rax .rcx, 4⟩), []) :=
  decodeIntExtendKap_prefers_kap _ _ _ pin_ixKap_movzx64

/-- Overlap pin: the REX.W MOVSXD row takes the capstone arm. -/
theorem pin_ixKapHw_sxd64 :
    decodeIntExtendKap [natByte 72, natByte 99, natByte 193] =
      some (.kap (.kern ⟨.movsx64From32 .rax .rcx, 3⟩), []) :=
  decodeIntExtendKap_prefers_kap _ _ _ pin_ixKap_sxd64

/-! ## 13. Machine adapter: the family on the coherent machine.

    The producer plug instantiates `HwAdapter IxDecodiert` with the
    accepted API: a successful family step re-embeds core data over
    the shared memory; refusals admit no successor state. Memory
    forms and past-width counts never reach a successor. -/

/-- The family plug: one checked family event step on the coherent
    machine. `none` = refusal, never a silent successor. -/
def adapterIntExtend : HwAdapter IxDecodiert :=
  ⟨fun m c d =>
    match ixSchritt d (projZustand m c) with
    | .ok s' =>
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
    | .misslungen => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterIntExtend_wf (m : HwMaschine) (c : Nat)
    (d : IxDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterIntExtend).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterIntExtend at h
  simp only at h
  cases hsch : ixSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | misslungen =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the accepted
    family step succeeds, with the successor core data re-embedded. -/
theorem adapterIntExtend_ok (m : HwMaschine) (c : Nat)
    (d : IxDecodiert) (s' : Zustand)
    (h : ixSchritt d (projZustand m c) = .ok s') :
    (adapterIntExtend).schritt m c d =
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterIntExtend
  simp only [h]

/-- The successor core sees the accepted successor registers over
    the shared memory. -/
theorem adapterIntExtend_proj (m : HwMaschine) (c : Nat)
    (d : IxDecodiert) (s' : Zustand)
    (h : ixSchritt d (projZustand m c) = .ok s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne c).register =
      s'.register ∧
    (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).mem = m.mem ∧
    s'.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c _,
    setKernVonFp_speicher m c _, ?_⟩
  have hmem := ixSchritt_speicher d (projZustand m c) s' h
  have hproj : (projZustand m c).speicher = m.mem := rfl
  rw [hproj] at hmem
  exact hmem

/-- A bad decode length admits no adapter step. -/
theorem adapterIntExtend_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : IxDecodiert)
    (h : laengeOk d.laenge = false) :
    (adapterIntExtend).schritt m c d = none := by
  have hstep := ix_laenge_misslungen d (projZustand m c) h
  unfold adapterIntExtend
  simp only [hstep]

/-- A memory operand admits no adapter step: memory moves through
    the TSO issue path, never through the register plug. -/
theorem adapterIntExtend_verweigert_bei_mem (m : HwMaschine)
    (c : Nat) (r : IxShiftRichtung) (b : Breite) (q : IxZaehler)
    (base : Register) (dd : BitVec 32) (l : Nat)
    (hok : laengeOk l = true) :
    (adapterIntExtend).schritt m c
        ⟨.shift ⟨r, b, q, .mem base dd⟩, l⟩ = none := by
  have hstep := ixSchritt_mem_verweigert r b q base dd l
    (projZustand m c) hok
  unfold adapterIntExtend
  simp only [hstep]

/-- A past-width double-shift count admits no adapter step. -/
theorem adapterIntExtend_verweigert_bei_weit (m : HwMaschine)
    (c : Nat) (links : Bool) (w : IxZielBreite) (q : IxDoppelZaehler)
    (dst src : Register) (l : Nat)
    (hok : laengeOk l = true)
    (hweit : (ixZielBreite w).bits <
      schiebeZaehler (ixZielBreite w)
        (ixDoppelZaehlerWert q (projZustand m c))) :
    (adapterIntExtend).schritt m c ⟨.shld links w q dst src, l⟩ =
      none := by
  have hstep := ixSchritt_shld_weit_verweigert links w q dst src l
    (projZustand m c) hok hweit
  unfold adapterIntExtend
  simp only [hstep]

/-! ## 14. Machine outcome: one family step on a core. -/

/-- One family machine step on core `c`: the accepted family step
    on the core projection, re-embedded on success. -/
def ixHwRegSchritt (m : HwMaschine) (c : Nat)
    (d : IxDecodiert) : HwRegAusgang :=
  match ixSchritt d (projZustand m c) with
  | .ok s' =>
    .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
  | .misslungen => .verweigert

/-- Selection: a successful family step continues on the machine. -/
theorem ixHwRegSchritt_weiter (m : HwMaschine) (c : Nat)
    (d : IxDecodiert) (s' : Zustand)
    (h : ixSchritt d (projZustand m c) = .ok s') :
    ixHwRegSchritt m c d =
      .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  have e : ixHwRegSchritt m c d =
      match ixSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: family refusal is machine refusal. -/
theorem ixHwRegSchritt_verweigert (m : HwMaschine) (c : Nat)
    (d : IxDecodiert)
    (h : ixSchritt d (projZustand m c) = .misslungen) :
    ixHwRegSchritt m c d = .verweigert := by
  have e : ixHwRegSchritt m c d =
      match ixSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- A machine continue preserves well-formedness. -/
theorem ixHwRegSchritt_weiter_wf (m : HwMaschine) (c : Nat)
    (d : IxDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : ixHwRegSchritt m c d = .weiter m') :
    HwWf m' := by
  have e : ixHwRegSchritt m c d =
      match ixSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .misslungen => .verweigert := rfl
  rw [e] at h
  cases hsch : ixSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | misslungen =>
    rw [hsch] at h
    simp only at h
    cases h

/-! ## 15. Joint witness: two cores, family steps, buffered store.

    Core 0 sign-extends `0xFF` to all ones, core 1 byte-swaps the
    witness word and shifts `1` by one and by CL; afterwards core 0
    issues a buffered byte store that only the owner observes by
    forwarding, and the drain changes actual shared memory from 0 to
    42. A memory operand and a bad length refuse beside the run.
    Non-degenerate: registers and shared memory observably change. -/

/-- Witness registers for core 0: RCX holds `0xFF`. -/
def ixHwWitReg0 : Register → Wort := fun q =>
  if q = Register.rcx then 0xFF
  else BitVec.ofNat 64 0

/-- Witness registers for core 1: RAX/RCX feed the shifts, RDX the
    swap. -/
def ixHwWitReg1 : Register → Wort := fun q =>
  if q = Register.rax then 1
  else if q = Register.rcx then 2
  else if q = Register.rdx then bswapZeugenWort
  else BitVec.ofNat 64 0

/-- Witness cores over both register files: both cores run at 4096. -/
def ixHwWitKern : Nat → HwKern
  | 0 => ⟨ixHwWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨ixHwWitReg1, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon. -/
def ixHwWitStart : HwMaschine :=
  ⟨zeugeSpeicher, ixHwWitKern, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem ixHwWitStart_wf : HwWf ixHwWitStart := by
  intro c f _
  cases f <;> rfl

/-- Core 0 sign-extends through the machine outcome. -/
def ixHwOutMovsx : HwRegAusgang :=
  ixHwRegSchritt ixHwWitStart 0 ⟨.ext .sx8 .w64 .rax .rcx, 4⟩

/-- Core 1 byte-swaps through the machine outcome. -/
def ixHwOutBswap : HwRegAusgang :=
  ixHwRegSchritt ixHwWitStart 1 ⟨.bswap true .rdx, 3⟩

/-- Core 1 shifts by one through the machine outcome. -/
def ixHwOutShl1 : HwRegAusgang :=
  ixHwRegSchritt ixHwWitStart 1
    ⟨.shift ⟨.shl, .b32, .eins, .reg .rax⟩, 2⟩

/-- Core 1 shifts by CL through the machine outcome. -/
def ixHwOutShlCl : HwRegAusgang :=
  ixHwRegSchritt ixHwWitStart 1
    ⟨.shift ⟨.shl, .b64, .cl, .reg .rax⟩, 3⟩

/-- Read a core register out of a machine outcome. -/
def ixHwRegOut (o : HwRegAusgang) (c : Nat) (q : Register) :
    Option Wort :=
  match o with
  | .weiter m => some ((m.kerne c).register q)
  | _ => none

/-- Core 0 sign extension: RAX holds all ones. -/
theorem ixHw_movsx_rax :
    ixHwRegOut ixHwOutMovsx 0 Register.rax =
      some 0xFFFFFFFFFFFFFFFF := by
  decide

/-- Core 1 byte swap: RDX holds the reversal. -/
theorem ixHw_bswap_rdx :
    ixHwRegOut ixHwOutBswap 1 Register.rdx =
      some (BitVec.ofNat 64 0x0807060504030201) := by
  decide

/-- Core 1 shift by one: RAX holds 2. -/
theorem ixHw_shl1_rax :
    ixHwRegOut ixHwOutShl1 1 Register.rax = some 2 := by
  decide

/-- Core 1 shift by CL: RAX holds 4. -/
theorem ixHw_shlcl_rax :
    ixHwRegOut ixHwOutShlCl 1 Register.rax = some 4 := by
  decide

/-- Witness data address. -/
def ixHwWitAdr : Adresse := BitVec.ofNat 64 8192

/-- Witness TSO start: canonical memory, empty buffers. -/
def ixHwWitTso0 : TSOZustand := ⟨zeugeSpeicher, fun _ => []⟩

/-- Core 0 issues byte 42 at the data cell. -/
def ixHwWitTso1 : Option TSOZustand :=
  issueByte ixHwWitTso0 0 ixHwWitAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def ixHwWitEigen : Option (Option Byte) :=
  match ixHwWitTso1 with
  | some s => some (loadByte s 0 ixHwWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def ixHwWitFremd : Option (Option Byte) :=
  match ixHwWitTso1 with
  | some s => some (loadByte s 1 ixHwWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def ixHwWitTso2 : Option TSOZustand :=
  match ixHwWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def ixHwWitNachFlush : Option (Option Byte) :=
  match ixHwWitTso2 with
  | some s => some (some (s.mem.bytes ixHwWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def ixHwWitFremdNach : Option (Option Byte) :=
  match ixHwWitTso2 with
  | some s => some (loadByte s 1 ixHwWitAdr)
  | none => none

/-- The data cell starts zeroed. -/
theorem ixHw_anfang_null :
    zeugeSpeicher.bytes ixHwWitAdr = BitVec.ofNat 8 0 := by
  rfl

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem ixHw_weiterleitung :
    ixHwWitEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem ixHw_fremd_alt :
    ixHwWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem ixHw_spuelung_aendert_speicher :
    ixHwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem ixHw_fremd_neu :
    ixHwWitFremdNach = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- A memory operand refuses the machine step. -/
theorem ixHw_mem_verweigert :
    ixHwRegSchritt ixHwWitStart 0
      ⟨.shift ⟨.shl, .b32, .cl,
        .mem .rax (BitVec.ofNat 32 0)⟩, 7⟩ = .verweigert := by
  have hok : laengeOk 7 = true := by decide
  have hstep := ixSchritt_mem_verweigert .shl .b32 .cl .rax
    (BitVec.ofNat 32 0) 7 (projZustand ixHwWitStart 0) hok
  exact ixHwRegSchritt_verweigert _ _ _ hstep

/-- A bad decode length refuses the machine step. -/
theorem ixHw_schlechte_laenge_verweigert :
    ixHwRegSchritt ixHwWitStart 0
      ⟨.ext .zx8 .w32 .rax .rcx, 0⟩ = .verweigert := by
  have hbad : laengeOk 0 = false := by decide
  have hstep := ix_laenge_misslungen
    (⟨.ext .zx8 .w32 .rax .rcx, 0⟩ : IxDecodiert)
    (projZustand ixHwWitStart 0) hbad
  exact ixHwRegSchritt_verweigert _ _ _ hstep

/-- The joint witness: a reached two-core family run (sign
    extension on core 0, byte swap and two shifts on core 1) beside
    a buffered store that only the owner forwards and a drain that
    changes actual shared memory from 0 to 42 -- with the memory and
    length refusals and the LOCK refusal beside it. -/
theorem ixHw_zeuge :
    ixHwRegOut ixHwOutMovsx 0 Register.rax =
        some 0xFFFFFFFFFFFFFFFF ∧
      ixHwRegOut ixHwOutBswap 1 Register.rdx =
        some (BitVec.ofNat 64 0x0807060504030201) ∧
      ixHwRegOut ixHwOutShl1 1 Register.rax = some 2 ∧
      ixHwRegOut ixHwOutShlCl 1 Register.rax = some 4 ∧
      ixHwWitEigen = some (some (BitVec.ofNat 8 42)) ∧
      ixHwWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      ixHwWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      ixHwWitFremdNach = some (some (BitVec.ofNat 8 42)) ∧
      zeugeSpeicher.bytes ixHwWitAdr = BitVec.ofNat 8 0 ∧
      HwWf ixHwWitStart ∧
      ixHwRegSchritt ixHwWitStart 0
        ⟨.shift ⟨.shl, .b32, .cl,
          .mem .rax (BitVec.ofNat 32 0)⟩, 7⟩ = .verweigert ∧
      ixHwRegSchritt ixHwWitStart 0
        ⟨.ext .zx8 .w32 .rax .rcx, 0⟩ = .verweigert ∧
      decodeIntExtendHw [natByte 240, natByte 208, natByte 227] =
        none := by
  refine ⟨ixHw_movsx_rax, ixHw_bswap_rdx, ixHw_shl1_rax,
    ixHw_shlcl_rax, ixHw_weiterleitung, ixHw_fremd_alt,
    ixHw_spuelung_aendert_speicher, ixHw_fremd_neu,
    ixHw_anfang_null, ixHwWitStart_wf, ixHw_mem_verweigert,
    ixHw_schlechte_laenge_verweigert, ixHw_weist_lock_zu⟩

/- CUTS:
    Proved here: the extension/swap/shift/double-shift family over
    the accepted evaluators (`extendNarrow`/`mergeRegNarrow`,
    `bswap32`/`bswap64`, `shlB`/`shrB`/`sarB` with the ShiftLogic
    evidence, the IntRotate prefix/width parsers) connected to the
    coherent machine and both byte dispatchers -- both dispatchers
    prefer the accepted chains (no pilot, extension, or capstone row
    is shadowed; the REX.W extension rows keep the capstone `kern`
    arm owned by `decodeCore`), one family step selects the accepted
    values exactly, success never touches memory, the `HwAdapter
    IxDecodiert` plug preserves `HwWf` with exact agreement and
    planted refusals (LOCK, REX.R over groups, rotate digits,
    memory-mode extension rows, AH without REX, 66h on MOVSXD/BSWAP,
    truncation, past-width double-shift counts), OF is defined
    exactly at masked count one with the incoming bit kept where
    free, and a reached two-core run with owner-only forwarding and
    a memory-changing drain stands beside the refusals.
    NOT proved here, and not claimed:
    - No hardware correspondence: encodings are the accepted
      canonical subsets with self-consistency only, not x86 truth.
      Silicon assumptions named: MOVZX/MOVSX/MOVSXD opcode rows and
      the /4 /5 (/6 alias) /7 digit choice, 66h invalid on MOVSXD,
      no 16-bit BSWAP, AH/BH/CH/DH refusal without REX, SHLD/SHRD
      count masking with past-width undefined, the SHLD/SHRD
      one-count sign-change OF sentence, CF-out rows and the
      kept-undefined-flag modelling are stated, not verified
      against silicon.
    - No 8-bit high-register sources without REX (refused), no
      memory-addressed extension/double-shift/swap forms (extension
      and double-shift memory modes refuse at decode; shift memory
      refuses at the register plug), no LOCK path (refused), no
      66h-BSWAP row.
    - No source/IR/ABI/loader/entry/budget link, no per-access
      target-to-W/GX simulation, no whole-word atomicity beyond
      byte drains, no timing/power behaviour.
    - The REX.W extension rows decode twice (capstone `kern` arm and
      the family decoder) by construction, never executed twice:
      both dispatchers take the capstone arm first.
-/

#print axioms ixExtWert_zx8
#print axioms ixZielSchreiben_b32
#print axioms probe_ixMovsxdWert
#print axioms ixShiftWert_routen
#print axioms ixShiftSnap_gueltig_shl
#print axioms shldFlags_gueltig
#print axioms shrdFlags_gueltig
#print axioms ixEncode_laenge
#print axioms ixRoundtrip_ext
#print axioms ixRoundtrip_shld_cl
#print axioms ixRoundtrip_shld_imm
#print axioms pin_ix_movzx16
#print axioms decodeIntExtendHw_prefers_ext
#print axioms ext_weist_ixShl1_zurueck
#print axioms pin_ixHw_shld16
#print axioms ix_weist_lock_zu
#print axioms kap_weist_ixBswap_zurueck
#print axioms pin_ixKap_sxd32
#print axioms pin_ixKap_movzx64
#print axioms ixSchritt_speicher
#print axioms ixSchritt_mem_verweigert
#print axioms ixSchritt_shld_weit_verweigert
#print axioms ixSchritt_shift_reg
#print axioms adapterIntExtend_wf
#print axioms adapterIntExtend_ok
#print axioms ixHwRegSchritt_weiter_wf
#print axioms ixHwWitStart_wf
#print axioms ixHw_zeuge

end Gabbro.Grammatik.X86
