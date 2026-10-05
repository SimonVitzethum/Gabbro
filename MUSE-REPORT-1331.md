# MUSE-REPORT-1331: Per-row consumed length for the capstone decoder chain

Lane 1331, follow-up of lane 1323 (`ValidatorKapDecoder.lean`, merged).
Clone `/home/simon/Dokumente/gabbro-muse/a1331`, branch `muse/1331`.

## Status: GREEN — probe 0 errors, full build exit 0, committed

- `./lean-probe grammatik/Grammatik/X86/ValidatorKapLength.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (first run 30 errors,
  repaired in two rounds: 30 → 4 → 0, details §5).
- `./lean-bau` (whole `grammatik/` including the new import):
  `== exit 0; 0 error line(s) in the COMPLETE output`.
- `#print axioms`: no `sorryAx` anywhere; every theorem depends only on
  subsets of the standard `propext` / `Classical.choice` / `Quot.sound`
  (most `decide`/`rfl` facts on no axioms at all).
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in the new file.
- `grammatik/Grammatik.lean` carries the one owned import line.
- Rule 13 (inhabitation): no theorem quantifies over program syntax —
  premises range over `List Byte` and decoded rows — so no `_zeuge`
  companion is required; `kapVerbraucht_zeuge` is the joint witness anyway.

## What was delivered

`grammatik/Grammatik/X86/ValidatorKapLength.lean` (655 lines), reusing
all accepted definitions unchanged:

**§1 Consumed length.** `kapVerbraucht (bs rest) := bs.length - rest.length`
with `kapVerbraucht_voll`; `kapZeilenLaenge : KapDekodiert → Option Nat`
(`breit → wdHwLen`, `s32/mxcsr/kompakt/kern → .laenge`,
`lock → lockLaenge`, `avx2 → .laenge`, `lockAdr → none`) with
`kapZeilenLaenge_fixiert` and `kapZeilenLaenge_lockAdr_verweigert`.
The `lockAdr → none` is the task's "refuse any row whose length cannot be
fixed": the row's `AdrForm` does not fix SIB presence (verified against
`parseAdrTail` in `AddressEncoding.lean`).

**§2 Prefix-style VEX decode.** `dekodiereAvx2Prefix` (four pinned rows as
prefix, `none` otherwise); `avxPrefix_paddq/pxor/movdquLd/movdquSt`,
`avxPrefix_vex128_verweigert`, `avxPrefix_fremd_verweigert` (`decide`);
`avxPrefix_genau` (exact-list agreement, four-way `by_cases` +
`beq_iff_eq`); `avxPrefix_verbraucht` (stated length within 1..15,
take/drop equations + `omega`).

**§3 Prefix-closed chain.** `kapDecodePrefix` (only the VEX arm changed);
`kapDecodePrefix_genau` (same shape as accepted `kapDecode_avx2`);
`avxPrefix_mitte_lock`, `avxPrefix_mitte_streu` (mid-section VEX at the
prefix arm, `decide`); `kapPrefix_avx2_fortschritt`.

**§4 Per-arm progress** (each reuses exactly one accepted
arbitrary-input length lemma + `omega`): `kapFortschritt_kompakt`,
`kapFortschritt_kern`, `kapFortschritt_breit_wd`,
`kapFortschritt_breit_pilot`, `kapFortschritt_breit_narrow`,
`kapFortschritt_breit_muldiv`, `kapFortschritt_breit_shift`,
`kapFortschritt_breit_setcc`, `kapFortschritt_breit_cmov`.

**§5 Coverage advance.** `kapDeckt_schritt_verbraucht`: under a proved
shrink hypothesis the `keinFortschritt` guard discharges and the walk
recurses on exactly the decoder's rest.

**§6 Witnesses.** `kapVerbraucht_zeuge` (all eight arms positive),
`kapVerbraucht_lock_neun`, `kapVerbraucht_lockAdr_sieben`,
`kapVerbraucht_avx2_fuenf`.

**§7 Overlap lengths (chain side).** `kapUeber_laenge_mul64/div64/imul2/div32`
(3/3/4/2, `decide`); no chain-side conflict exhibited; cross-decoder
comparison stays open (CUTS).

## Probe repair history (30 → 4 → 0)

1. Self-review before first probe: fixed a false `kapZeilenLaenge_fixiert`
   statement (claimed non-`lockAdr` by disequality against one fixed row —
   false) and two arity bugs (`kapVerbraucht` called with one argument).
2. First probe (30 errors): bare `[].length` in the witness statement has no
   element type → ascribed `([] : List Byte)` (23 knock-on errors incl. the
   missing `kapVerbraucht_zeuge` constant); in `avxPrefix_verbraucht` the
   branch value is `some (pair)`, so `Prod.mk.injEq` alone made no progress —
   added `Option.some.injEq` first (accepted `blatt_laenge` pattern); in
   `kapDeckt_schritt_verbraucht` simp rewrote the guard to `True` without
   applying `if_true` — restructured to `rw` + `simp only [if_pos …]`
   (accepted `valKap_deckung` pattern).
3. Second probe (4 errors): `rw [htake]` leaves `[lit…].length = 5`
   unclosed (rw's auto-rfl does not compute it) → `simp [htake]`.
4. Third probe: 0 errors. Full `./lean-bau`: exit 0, 0 error lines.

## Open (for follow-up lanes, unchanged)

- Arbitrary-input consumed-length for s32, MXCSR, LOCK, addressed-LOCK,
  unified FP (`fpDecode`) and packed-integer (`decodeVector`) arms: no
  accepted arbitrary-input lemma exists (only round trips/refusals).
- Chain-level mid-section VEX (seven earlier arms' refusal of VEX-led
  lists with trailing bytes unmeasured).
- Cross-decoder length comparison on the §5 overlap rows (a differing
  row would be a finding; none recorded).
- No silicon re-check; no W/GX bridge; no source/checker/contract/entry/
  ABI/loader/budget/liveness claim. Vendor-neutral (rule 17).

## Note on the lane file

The MECHANISM paragraph (§28, `HwAdapter` over `HwMaschine`) is generic
boilerplate conflicting with the specific TASK (§25, per-row lengths +
VEX prefix); the specific task was implemented. No existing file was
changed except the one owned import line in `grammatik/Grammatik.lean`.
