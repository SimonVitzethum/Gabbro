/-
  File:      Grammatik/X86/ValidatorKapLength.lean
  Subject:   Per-row consumed length for the capstone decoder chain.

  Lane 1331 (follow-up of lane 1323 `ValidatorKapDecoder`, which lists
  as open that no per-row consumed-length theorem exists -- progress is
  guarded by `keinFortschritt`, not proved -- and that the accepted
  `dekodiereAvx2` matches whole lists only, so a VEX row is covered
  only at a section tail while mid-section VEX refuses with
  `keinDekoder`):
  - the measured consumed length of one chain step (`kapVerbraucht`)
    and the declared row length where the row carries checked length
    data (`kapZeilenLaenge`; the addressed-LOCK row carries no length
    field, so the length function refuses it with `none` -- a row
    whose length cannot be fixed is refused, never guessed);
  - progress for every chain arm whose decoder has an accepted
    arbitrary-input consumed-length lemma (compact, core, the width
    dispatcher arm over the unified sub-arms with lemmas and over the
    width rows);
  - a prefix-style VEX decode (`dekodiereAvx2Prefix`, equal to the
    accepted `dekodiereAvx2` on exact lists and prefix-closed) with
    its own progress, lifted into `kapDecodePrefix` so a VEX row
    admits trailing bytes;
  - the coverage-check advance (`kapDeckt_schritt_verbraucht`): one
    covered step recurses on exactly the decoder's rest, and the
    consumed length plus the rest is the input.
  Accepted definitions are reused unchanged, never redefined. No
  silicon fact beyond the accepted pins; undefined or model-specific
  behaviour stays out of the model (rule 17).
-/
import Grammatik.X86.HwKapsteinDecoder
import Grammatik.X86.ValidatorKapDecoder
import Grammatik.X86.Avx2Join
import Grammatik.X86.ISA
import Grammatik.X86.ShiftCodec
import Grammatik.X86.DecoderSoundness
import Grammatik.X86.NarrowCodec
import Grammatik.X86.MulDivCodec
import Grammatik.X86.MulDivWidthHardwareForms
import Grammatik.X86.HwMulDivWidth
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.ScalarFloat32HardwareForms
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.CompactForms
import Grammatik.X86.IntegerCore

namespace Gabbro.Grammatik.X86

/-! ## 1. Consumed length: measured and declared. -/

/-- Measured consumed length of one chain step: available bytes minus
    remaining bytes. -/
def kapVerbraucht (bs rest : List Byte) : Nat :=
  bs.length - rest.length

/-- A full rest consumes nothing. -/
theorem kapVerbraucht_voll (bs : List Byte) :
    kapVerbraucht bs [] = bs.length := by
  unfold kapVerbraucht
  simp

/-- Declared row length where the row carries checked length data.
    The addressed-LOCK row (`lockAdr`) carries no length field: its
    tail parser `parseAdrTail` consumes a mode-dependent suffix
    (ModRM plus an optional SIB plus a displacement), and the parsed
    `AdrForm` alone does not fix whether a SIB byte was consumed (a
    form with no index and scale 1 arises both with and without SIB),
    so the length function refuses it with `none`. The decoder still
    accepts the row; its length is measured (`kapVerbraucht`), never
    guessed. -/
def kapZeilenLaenge : KapDekodiert → Option Nat
  | .breit w => some (wdHwLen w)
  | .s32 d => some d.laenge
  | .mxcsr d => some d.laenge
  | .lock a => some (lockLaenge a)
  | .lockAdr _ _ => none
  | .kompakt d => some d.laenge
  | .kern d => some d.laenge
  | .avx2 z => some z.laenge

/-- The length function fixes every row except the addressed-LOCK
    row, by construction: each non-`lockAdr` constructor reduces to
    its checked length, and `lockAdr` is the `none` case. -/
theorem kapZeilenLaenge_fixiert (d : KapDekodiert) :
    (∃ n, kapZeilenLaenge d = some n) ∨
      (∃ r f, d = .lockAdr r f) := by
  cases d with
  | breit w => exact Or.inl ⟨_, rfl⟩
  | s32 s => exact Or.inl ⟨_, rfl⟩
  | mxcsr m => exact Or.inl ⟨_, rfl⟩
  | lock a => exact Or.inl ⟨_, rfl⟩
  | lockAdr r f => exact Or.inr ⟨r, f, rfl⟩
  | kompakt c => exact Or.inl ⟨_, rfl⟩
  | kern k => exact Or.inl ⟨_, rfl⟩
  | avx2 z => exact Or.inl ⟨_, rfl⟩

/-- The length function refuses exactly the addressed-LOCK row. -/
theorem kapZeilenLaenge_lockAdr_verweigert (r : Register)
    (f : AdrForm) :
    kapZeilenLaenge (.lockAdr r f) = none := rfl

/-! ## 2. Prefix-style VEX decode.

  The accepted `dekodiereAvx2` matches whole lists only
  (`Avx2Join.lean`, four pinned rows). The prefix decoder below
  matches the same four rows as a PREFIX and returns the untouched
  suffix; anything else refuses with `none`. Lengths 5/5/6/6 are the
  accepted `Avx2Zeile.laenge` values, restated not re-decided. -/

/-- Prefix-closed VEX decoder over the four accepted pinned rows.
    A row whose length cannot be fixed (anything but the four pinned
    prefixes) is refused with `none`, never guessed. -/
def dekodiereAvx2Prefix (bs : List Byte) :
    Option (Avx2Join.Avx2Zeile × List Byte) :=
  if bs.take 5 == [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2] then
    some (⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩, bs.drop 5)
  else if bs.take 5 == [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2] then
    some (⟨.vpxorRR .ymm0 .ymm1 .ymm2, 5⟩, bs.drop 5)
  else if bs.take 6 == [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00] then
    some (⟨.vmovdquLd .ymm0 .rax 0x00, 6⟩, bs.drop 6)
  else if bs.take 6 == [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00] then
    some (⟨.vmovdquSt .rax .ymm0 0x00, 6⟩, bs.drop 6)
  else none

/-- The prefix decoder takes the pinned VPADDQ row exactly. -/
theorem avxPrefix_paddq :
    dekodiereAvx2Prefix [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2] =
      some (⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩, []) := by
  decide

/-- The prefix decoder takes the pinned VPXOR row exactly. -/
theorem avxPrefix_pxor :
    dekodiereAvx2Prefix [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2] =
      some (⟨.vpxorRR .ymm0 .ymm1 .ymm2, 5⟩, []) := by
  decide

/-- The prefix decoder takes the pinned VMOVDQU load exactly. -/
theorem avxPrefix_movdquLd :
    dekodiereAvx2Prefix [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00] =
      some (⟨.vmovdquLd .ymm0 .rax 0x00, 6⟩, []) := by
  decide

/-- The prefix decoder takes the pinned VMOVDQU store exactly. -/
theorem avxPrefix_movdquSt :
    dekodiereAvx2Prefix [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00] =
      some (⟨.vmovdquSt .rax .ymm0 0x00, 6⟩, []) := by
  decide

/-- The prefix decoder refuses the VEX.128 shape, like the accepted
    decoder (`dekodiere_vex128_verweigert`). -/
theorem avxPrefix_vex128_verweigert :
    dekodiereAvx2Prefix [(0xC4 : Byte), 0xE1, 0x74, 0xD4, 0xC2] =
      none := by
  decide

/-- The prefix decoder refuses non-VEX bytes, like the accepted
    decoder (`dekodiere_fremd_verweigert`). -/
theorem avxPrefix_fremd_verweigert :
    dekodiereAvx2Prefix [(0x66 : Byte), 0x0F, 0xD4, 0xC2] = none := by
  decide

/-- AGREEMENT ON EXACT LISTS: wherever the accepted decoder takes a
    row, the prefix decoder takes the same row with no remainder.
    Every premise is used: `h` drives the four-way case split and
    feeds each branch its row. -/
theorem avxPrefix_genau (bs : List Byte) (z : Avx2Join.Avx2Zeile)
    (h : Avx2Join.dekodiereAvx2 bs = some z) :
    dekodiereAvx2Prefix bs = some (z, []) := by
  unfold Avx2Join.dekodiereAvx2 at h
  by_cases h1 : bs == [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2]
  · rw [if_pos h1] at h
    simp only [Option.some.injEq] at h
    obtain ⟨rfl⟩ := h
    have hb : bs = [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2] :=
      beq_iff_eq.mp h1
    rw [hb]
    decide
  · rw [if_neg h1] at h
    by_cases h2 : bs == [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2]
    · rw [if_pos h2] at h
      simp only [Option.some.injEq] at h
      obtain ⟨rfl⟩ := h
      have hb : bs = [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2] :=
        beq_iff_eq.mp h2
      rw [hb]
      decide
    · rw [if_neg h2] at h
      by_cases h3 :
        bs == [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00]
      · rw [if_pos h3] at h
        simp only [Option.some.injEq] at h
        obtain ⟨rfl⟩ := h
        have hb :
            bs = [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00] :=
          beq_iff_eq.mp h3
        rw [hb]
        decide
      · rw [if_neg h3] at h
        by_cases h4 :
          bs == [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00]
        · rw [if_pos h4] at h
          simp only [Option.some.injEq] at h
          obtain ⟨rfl⟩ := h
          have hb :
              bs = [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00] :=
            beq_iff_eq.mp h4
          rw [hb]
          decide
        · rw [if_neg h4] at h
          simp at h

/-- PREFIX PROGRESS: every successful prefix decode consumes exactly
    its stated length within 1..15. The length equation comes from the
    take/drop split of the input; the bound is the accepted row
    length. Every premise is used: `h` drives the four-way case split
    and feeds each branch its row and remainder. -/
theorem avxPrefix_verbraucht (bs : List Byte) (z : Avx2Join.Avx2Zeile)
    (rest : List Byte) (h : dekodiereAvx2Prefix bs = some (z, rest)) :
    z.laenge + rest.length = bs.length ∧ 1 ≤ z.laenge := by
  unfold dekodiereAvx2Prefix at h
  by_cases h1 : bs.take 5 == [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2]
  · rw [if_pos h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hz, hrest⟩ := h
    rw [← hz, ← hrest]
    show 5 + (bs.drop 5).length = bs.length ∧ 1 ≤ 5
    have htake :
        bs.take 5 = [(0xC4 : Byte), 0xE1, 0x75, 0xD4, 0xC2] :=
      beq_iff_eq.mp h1
    have e5 : (bs.take 5).length = 5 := by simp [htake]
    rw [List.length_take] at e5
    have h5 : 5 ≤ bs.length := by omega
    rw [List.length_drop]
    omega
  · rw [if_neg h1] at h
    by_cases h2 : bs.take 5 == [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2]
    · rw [if_pos h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hz, hrest⟩ := h
      rw [← hz, ← hrest]
      show 5 + (bs.drop 5).length = bs.length ∧ 1 ≤ 5
      have htake :
          bs.take 5 = [(0xC4 : Byte), 0xE1, 0x75, 0xEF, 0xC2] :=
        beq_iff_eq.mp h2
      have e5 : (bs.take 5).length = 5 := by simp [htake]
      rw [List.length_take] at e5
      have h5 : 5 ≤ bs.length := by omega
      rw [List.length_drop]
      omega
    · rw [if_neg h2] at h
      by_cases h3 :
        bs.take 6 == [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00]
      · rw [if_pos h3] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hz, hrest⟩ := h
        rw [← hz, ← hrest]
        show 6 + (bs.drop 6).length = bs.length ∧ 1 ≤ 6
        have htake :
            bs.take 6 =
              [(0xC4 : Byte), 0xE1, 0x7E, 0x6F, 0x40, 0x00] :=
          beq_iff_eq.mp h3
        have e6 : (bs.take 6).length = 6 := by simp [htake]
        rw [List.length_take] at e6
        have h6 : 6 ≤ bs.length := by omega
        rw [List.length_drop]
        omega
      · rw [if_neg h3] at h
        by_cases h4 :
          bs.take 6 == [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00]
        · rw [if_pos h4] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hz, hrest⟩ := h
          rw [← hz, ← hrest]
          show 6 + (bs.drop 6).length = bs.length ∧ 1 ≤ 6
          have htake :
              bs.take 6 =
                [(0xC4 : Byte), 0xE1, 0x7E, 0x7F, 0x40, 0x00] :=
            beq_iff_eq.mp h4
          have e6 : (bs.take 6).length = 6 := by simp [htake]
          rw [List.length_take] at e6
          have h6 : 6 ≤ bs.length := by omega
          rw [List.length_drop]
          omega
        · rw [if_neg h4] at h
          simp at h

/-! ## 3. Prefix-closed chain: a VEX row admits trailing bytes.

  `kapDecodePrefix` is `kapDecode` with the exact-list VEX arm
  replaced by the prefix arm. The first seven arms are untouched, so
  all accepted agreement, refusal and witness facts keep holding for
  them; only the VEX arm changes. -/

/-- The prefix-closed capstone chain: the first seven arms are
    `kapDecode` unchanged; the VEX arm takes a pinned prefix with its
    untouched suffix. -/
def kapDecodePrefix : List Byte → Option (KapDekodiert × List Byte) :=
  fun bs =>
    match decodeMulDivWidth bs with
    | some (w, rest) => some (KapDekodiert.breit w, rest)
    | none =>
      match s32Decode bs with
      | some (d, rest) => some (KapDekodiert.s32 d, rest)
      | none =>
        match mxcsrDecode bs with
        | some (d, rest) => some (KapDekodiert.mxcsr d, rest)
        | none =>
          match decodeLock bs with
          | some (a, rest) => some (KapDekodiert.lock a, rest)
          | none =>
            match decodeLockAdr bs with
            | some (r, f, rest) =>
              some (KapDekodiert.lockAdr r f, rest)
            | none =>
              match decodeC bs with
              | some (d, rest) =>
                some (KapDekodiert.kompakt d, rest)
              | none =>
                match decodeCore bs with
                | some (d, rest) => some (KapDekodiert.kern d, rest)
                | none =>
                  match dekodiereAvx2Prefix bs with
                  | some (z, rest) =>
                    some (KapDekodiert.avx2 z, rest)
                  | none => none

/-- The prefix chain agrees with the accepted chain on exact VEX
    rows: where every earlier arm refuses and the accepted VEX decoder
    takes its row, the prefix chain takes it with no remainder. Every
    premise is used: the seven `none`s route past the seven
    untouched arms, `h8` feeds the prefix agreement. -/
theorem kapDecodePrefix_genau (bs : List Byte) (z : Avx2Join.Avx2Zeile)
    (h1 : decodeMulDivWidth bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none)
    (h4 : decodeLock bs = none) (h5 : decodeLockAdr bs = none)
    (h6 : decodeC bs = none) (h7 : decodeCore bs = none)
    (h8 : Avx2Join.dekodiereAvx2 bs = some z) :
    kapDecodePrefix bs = some (KapDekodiert.avx2 z, []) := by
  unfold kapDecodePrefix
  rw [h1, h2, h3, h4, h5, h6, h7]
  have hp := avxPrefix_genau bs z h8
  rw [hp]

/-- MID-SECTION VEX at the prefix arm: the VPADDQ row followed by the
    LOCK witness decodes to the row with the LOCK bytes untouched.
    (Chain-level mid-section coverage additionally needs the seven
    earlier arms to refuse the VEX-led list; see CUTS.) -/
theorem avxPrefix_mitte_lock :
    dekodiereAvx2Prefix (kapW_avx2 ++ kapW_lock) =
      some (⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩, kapW_lock) := by
  decide

/-- MID-SECTION VEX at the prefix arm: the VPADDQ row followed by one
    stray byte decodes to the row with the stray byte untouched. -/
theorem avxPrefix_mitte_streu :
    dekodiereAvx2Prefix (kapW_avx2 ++ [natByte 6]) =
      some (⟨.vpaddRR .b64 .ymm0 .ymm1 .ymm2, 5⟩, [natByte 6]) := by
  decide

/-- Progress of the prefix VEX arm: positive, at most the available
    bytes. Reuses `avxPrefix_verbraucht`; the hypothesis feeds it. -/
theorem kapPrefix_avx2_fortschritt (bs : List Byte)
    (z : Avx2Join.Avx2Zeile) (rest : List Byte)
    (h : dekodiereAvx2Prefix bs = some (z, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  obtain ⟨heq, hlo⟩ := avxPrefix_verbraucht bs z rest h
  unfold kapVerbraucht
  omega

/-! ## 4. Per-arm progress over the accepted chain.

  One wrapper per chain arm whose decoder has an accepted
  arbitrary-input consumed-length lemma. Each reuses exactly that
  lemma; the hypothesis feeds it, and `omega` turns the length
  equation into positivity plus the bound. Arms without an accepted
  arbitrary-input lemma (s32, MXCSR, LOCK, addressed-LOCK, the
  unified FP/vector sub-arms) stay open; see CUTS. -/

/-- Progress of the compact arm (reuses `decodeC_verbraucht`). -/
theorem kapFortschritt_kompakt (bs : List Byte) (d : CompactDecodiert)
    (rest : List Byte) (h : decodeC bs = some (d, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  obtain ⟨heq, hlo, _⟩ := decodeC_verbraucht bs d rest h
  unfold kapVerbraucht
  omega

/-- Progress of the core arm (reuses `decodeCore_verbraucht`). -/
theorem kapFortschritt_kern (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h : decodeCore bs = some (d, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  obtain ⟨heq, hlo, _⟩ := decodeCore_verbraucht bs d rest h
  unfold kapVerbraucht
  omega

/-- Progress of the width rows of the dispatcher arm (reuses
    `decodeWd_len_ok`). -/
theorem kapFortschritt_breit_wd (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (h : decodeWd bs = some (d, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  obtain ⟨heq, hlo, _⟩ := decodeWd_len_ok bs d rest h
  unfold kapVerbraucht
  omega

/-- Progress of the pilot sub-arm (reuses
    `decode_verbraucht_praefix`). -/
theorem kapFortschritt_breit_pilot (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  obtain ⟨heq, _, hlo, _⟩ := decode_verbraucht_praefix bs d rest h
  unfold kapVerbraucht
  omega

/-- Progress of the narrow sub-arm (reuses
    `decodeNarrow_consumes`). -/
theorem kapFortschritt_breit_narrow (bs : List Byte) (d : NarrowDec)
    (rest : List Byte) (h : decodeNarrow bs = some (d, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  obtain ⟨heq, hlo, _⟩ := decodeNarrow_consumes bs d rest h
  unfold kapVerbraucht
  omega

/-- Progress of the multiply/divide sub-arm (reuses
    `decodeMulDiv_len_ok`). -/
theorem kapFortschritt_breit_muldiv (bs : List Byte)
    (d : MulDivDecodiert) (rest : List Byte)
    (h : decodeMulDiv bs = some (d, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  obtain ⟨heq, hlo, _⟩ := decodeMulDiv_len_ok bs d rest h
  unfold kapVerbraucht
  omega

/-- Progress of the shift sub-arm (reuses `decodeShift_laenge`; the
    bound per form is the accepted `shiftLaenge`). -/
theorem kapFortschritt_breit_shift (bs : List Byte) (f : ShiftForm)
    (rest : List Byte) (h : decodeShift bs = some (f, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  have heq := decodeShift_laenge bs f rest h
  cases f with
  | imm _ _ _ =>
    simp only [shiftLaenge] at heq
    unfold kapVerbraucht
    omega
  | cl _ _ =>
    simp only [shiftLaenge] at heq
    unfold kapVerbraucht
    omega

/-- Progress of the SETcc sub-arm (reuses `decodeSetCC_verbraucht`;
    the consumed length is the accepted 4). -/
theorem kapFortschritt_breit_setcc (bs : List Byte)
    (v : Bedingung × Register) (rest : List Byte)
    (h : decodeSetCC bs = some (v, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  have heq := decodeSetCC_verbraucht bs v rest h
  unfold kapVerbraucht
  omega

/-- Progress of the CMOVcc sub-arm (reuses `decodeCmov_verbraucht`;
    the consumed length is the accepted 4). -/
theorem kapFortschritt_breit_cmov (bs : List Byte)
    (v : Bedingung × Register × Register) (rest : List Byte)
    (h : decodeCmov bs = some (v, rest)) :
    0 < kapVerbraucht bs rest ∧ kapVerbraucht bs rest ≤ bs.length := by
  have heq := decodeCmov_verbraucht bs v rest h
  unfold kapVerbraucht
  omega

/-! ## 5. The coverage check advances by exactly the consumed length.

  Lane 1323 guards progress with `keinFortschritt` instead of proving
  it. With a proved shrink hypothesis the guard discharges and one
  covered step recurses on exactly the decoder's rest, with consumed
  length plus rest equal to the input. -/

/-- COVERAGE ADVANCE: one covered chain step recurses on exactly the
    decoder's rest, and the consumed length plus the rest is the
    input. Every premise is used: `hdec` selects the step, `hprog`
    discharges the progress guard and feeds the length equation. -/
theorem kapDeckt_schritt_verbraucht (n : Nat) (b : Byte)
    (bs rest : List Byte) (d : KapDekodiert)
    (hdec : kapDecode (b :: bs) = some (d, rest))
    (hprog : rest.length < (b :: bs).length) :
    kapDecktFuel (n + 1) (b :: bs) = kapDecktFuel n rest ∧
      kapVerbraucht (b :: bs) rest + rest.length =
        (b :: bs).length := by
  refine ⟨?_, ?_⟩
  · rw [kapDecktFuel_schritt, hdec]
    simp only [if_pos hprog]
  · unfold kapVerbraucht
    omega

/-! ## 6. Witnesses: every chain arm consumes a positive length. -/

/-- JOINT WITNESS: every one of the eight accepted chain witnesses
    consumes a positive measured length, and consumed length plus the
    (empty) rest is the witness. Closed evaluations; no arm is
    empty. -/
theorem kapVerbraucht_zeuge :
    (kapVerbraucht kapW_wd [] + ([] : List Byte).length = kapW_wd.length ∧
      0 < kapVerbraucht kapW_wd []) ∧
    (kapVerbraucht kapW_s32 [] + ([] : List Byte).length = kapW_s32.length ∧
      0 < kapVerbraucht kapW_s32 []) ∧
    (kapVerbraucht kapW_mxcsr [] + ([] : List Byte).length = kapW_mxcsr.length ∧
      0 < kapVerbraucht kapW_mxcsr []) ∧
    (kapVerbraucht kapW_lock [] + ([] : List Byte).length = kapW_lock.length ∧
      0 < kapVerbraucht kapW_lock []) ∧
    (kapVerbraucht kapW_lockAdr [] + ([] : List Byte).length = kapW_lockAdr.length ∧
      0 < kapVerbraucht kapW_lockAdr []) ∧
    (kapVerbraucht kapW_kompakt [] + ([] : List Byte).length = kapW_kompakt.length ∧
      0 < kapVerbraucht kapW_kompakt []) ∧
    (kapVerbraucht kapW_kern [] + ([] : List Byte).length = kapW_kern.length ∧
      0 < kapVerbraucht kapW_kern []) ∧
    (kapVerbraucht kapW_avx2 [] + ([] : List Byte).length = kapW_avx2.length ∧
      0 < kapVerbraucht kapW_avx2 []) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The LOCK witness consumes exactly its 9 accepted bytes
    (`pinXadd`, nine literal bytes). -/
theorem kapVerbraucht_lock_neun :
    kapVerbraucht kapW_lock [] = 9 := by
  decide

/-- The addressed-LOCK witness consumes exactly its 7 accepted bytes
    (seven literal bytes). -/
theorem kapVerbraucht_lockAdr_sieben :
    kapVerbraucht kapW_lockAdr [] = 7 := by
  decide

/-- The VEX witness consumes exactly its 5 accepted bytes (five
    literal bytes). -/
theorem kapVerbraucht_avx2_fuenf :
    kapVerbraucht kapW_avx2 [] = 5 := by
  decide

/-! ## 7. Overlap lengths on the chain side.

  The §5 overlaps of `HwKapsteinDecoder` keep the earlier chain level.
  No chain-side length conflict is exhibited: each overlap row below
  is consumed whole (empty rest) by the chain with the stated length,
  matching the accepted length of the winning arm (3/3/4 for the
  unified rows, 2 for the new width divide row). Whether the SHADOWED
  decoder would consume a DIFFERENT length on these rows is unmeasured
  (see CUTS): a row whose consumed length differs between two
  decoders of an overlap is a finding, and none is recorded here. -/

/-- Overlap row (width vs unified, 64-bit multiply): the chain
    consumes 3 bytes. -/
theorem kapUeber_laenge_mul64 :
    kapVerbraucht [natByte 73, natByte 247, natByte 224] [] = 3 := by
  decide

/-- Overlap row (width vs unified, 64-bit divide): the chain consumes
    3 bytes. -/
theorem kapUeber_laenge_div64 :
    kapVerbraucht [natByte 73, natByte 247, natByte 251] [] = 3 := by
  decide

/-- Overlap row (width vs unified, two-operand multiply): the chain
    consumes 4 bytes. -/
theorem kapUeber_laenge_imul2 :
    kapVerbraucht [natByte 77, natByte 15, natByte 175, natByte 207] [] =
      4 := by
  decide

/-- New width divide row: the chain consumes 2 bytes. -/
theorem kapUeber_laenge_div32 :
    kapVerbraucht [natByte 247, natByte 241] [] = 2 := by
  decide

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    decoder lifted, never redefined):
    - measured consumed length `kapVerbraucht` (available minus rest)
      with `kapVerbraucht_voll`, and declared row length
      `kapZeilenLaenge` with its exact refusal characterisation
      (`kapZeilenLaenge_fixiert`, `kapZeilenLaenge_lockAdr_verweigert`:
      every row but the addressed-LOCK row is fixed; the addressed-LOCK
      row is refused because its `AdrForm` does not fix SIB presence);
    - prefix-style VEX decode `dekodiereAvx2Prefix` with exact-list
      agreement (`avxPrefix_genau`), prefix-closed mid-section decodes
      at the prefix arm (`avxPrefix_mitte_lock`, `avxPrefix_mitte_streu`),
      its own progress (`avxPrefix_verbraucht`,
      `kapPrefix_avx2_fortschritt`), and the prefix-closed chain
      `kapDecodePrefix` with exact-row agreement
      (`kapDecodePrefix_genau`);
    - per-arm progress for the compact, core, width-dispatcher-width
      and six unified sub-arms with accepted arbitrary-input lemmas
      (§4, each reusing exactly one accepted length equation);
    - coverage advance by exactly the consumed length
      (`kapDeckt_schritt_verbraucht`): under a proved shrink
      hypothesis the `keinFortschritt` guard discharges and the walk
      recurses on the decoder's rest;
    - joint witness `kapVerbraucht_zeuge` (every chain arm consumes a
      positive length) with three pinned lengths, and chain-side
      overlap lengths (§7, no chain-side conflict exhibited).
    NOT proved here, and not claimed:
    - arbitrary-input consumed-length (hence chain progress) for the
      s32, MXCSR, LOCK and addressed-LOCK arms and for the unified FP
      (`fpDecode`) and packed-integer (`decodeVector`) sub-arms: no
      accepted arbitrary-input length lemma exists for any of them
      (only encoder round trips and refusals), so §4 has no wrapper
      for them and full `kapDecode` progress over arbitrary input
      stays OPEN;
    - chain-level mid-section VEX coverage: the prefix arm takes a
      VEX-led list with its suffix (§3), but the seven earlier arms'
      refusal of a VEX-led list with trailing bytes is unmeasured
      (the accepted refusal matrix is on exact VEX lists only);
    - cross-decoder length comparison on the §5 overlap rows: whether
      the shadowed decoder (e.g. `decodeWd` on the REX.W rows the
      unified arm wins) consumes the SAME length is unmeasured; a
      differing row would be a finding and none is recorded;
    - no silicon re-check: encodings, fault classes and ordering
      rules are inherited unchanged from the accepted decoders; no
      new hardware fact is stated, Intel or AMD; undefined or
      model-specific behaviour stays out of the model (rule 17);
    - no W/GX bridge; no source, checker, contract, entry, ABI,
      loader, budget or liveness claim.
-/

#print axioms kapVerbraucht_voll
#print axioms kapZeilenLaenge_fixiert
#print axioms kapZeilenLaenge_lockAdr_verweigert
#print axioms avxPrefix_paddq
#print axioms avxPrefix_pxor
#print axioms avxPrefix_movdquLd
#print axioms avxPrefix_movdquSt
#print axioms avxPrefix_vex128_verweigert
#print axioms avxPrefix_fremd_verweigert
#print axioms avxPrefix_genau
#print axioms avxPrefix_verbraucht
#print axioms kapDecodePrefix_genau
#print axioms avxPrefix_mitte_lock
#print axioms avxPrefix_mitte_streu
#print axioms kapPrefix_avx2_fortschritt
#print axioms kapFortschritt_kompakt
#print axioms kapFortschritt_kern
#print axioms kapFortschritt_breit_wd
#print axioms kapFortschritt_breit_pilot
#print axioms kapFortschritt_breit_narrow
#print axioms kapFortschritt_breit_muldiv
#print axioms kapFortschritt_breit_shift
#print axioms kapFortschritt_breit_setcc
#print axioms kapFortschritt_breit_cmov
#print axioms kapDeckt_schritt_verbraucht
#print axioms kapVerbraucht_zeuge
#print axioms kapVerbraucht_lock_neun
#print axioms kapVerbraucht_lockAdr_sieben
#print axioms kapVerbraucht_avx2_fuenf
#print axioms kapUeber_laenge_mul64
#print axioms kapUeber_laenge_div64
#print axioms kapUeber_laenge_imul2
#print axioms kapUeber_laenge_div32

end Gabbro.Grammatik.X86
