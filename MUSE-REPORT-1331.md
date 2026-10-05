# MUSE-REPORT-1331: Per-row consumed length for the capstone decoder chain

Lane 1331, follow-up of lane 1323 (`ValidatorKapDecoder.lean`, merged).
Clone `/home/simon/Dokumente/gabbro-muse/a1331`, branch `muse/1331`.

## Status: GREEN after independent review — REPAIR items R1/R2 closed, committed

- `./lean-probe grammatik/Grammatik/X86/ValidatorKapLength.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
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

## Independent review (lane 1332) and repair

Reviewer 1332 (exact review of pinned HEAD `f1f50818`) returned VERDICT:
REPAIR with two bounded items, both closed in this turn:

- **R1 (§7 overlap theorems were vacuous).** `kapVerbraucht bs [] =
  bs.length` holds by definition, so the old `kapUeber_laenge_*` proved
  list-length arithmetic without running any decoder. Fixed per option
  (a): each of the four overlap theorems is now a chain-tied triple —
  `kapDecode <row> = some (<winning row>, [])` reusing the accepted
  `kapUeber_wd_ext_mul64 / _div64 / _imul2 / _neu_div32` evaluations
  verbatim, plus measured length = stated length (3/3/4/2, `decide`)
  and positive progress (`decide`). This also discharges chain progress
  for those four rows.
- **R2 (CUTS gaps + unproved agreement).** (i) CUTS now names the missing
  top-level breit-arm wrapper explicitly (`kapFortschritt_breit_wd`
  covers only the `decodeWd` sub-decoder; `decodeMulDivWidth`/
  `decodeExt` have no accepted arbitrary-input length lemma). (ii)
  Declared-vs-measured agreement is now PROVED in new §8 for all ten
  arms with an accepted equation: `kapLaenge_stimmt_kompakt`,
  `kapLaenge_stimmt_kern`, `kapLaenge_stimmt_breit_wd`,
  `kapLaenge_stimmt_breit_pilot`, `kapLaenge_stimmt_breit_narrow`,
  `kapLaenge_stimmt_breit_muldiv`, `kapLaenge_stimmt_breit_shift`,
  `kapLaenge_stimmt_breit_setcc`, `kapLaenge_stimmt_breit_cmov`,
  `kapLaenge_stimmt_prefix_avx2` (each: declared `= some stated`,
  stated `+ rest = input`, measured `= stated`; each reuses exactly one
  accepted equation). CUTS lists the remaining agreement gaps
  (s32/MXCSR/LOCK/lockAdr/FP/vector/top-level breit).

## What was delivered

`grammatik/Grammatik/X86/ValidatorKapLength.lean` (~830 lines), reusing
all accepted definitions unchanged:

**§1 Consumed length.** `kapVerbraucht` with `kapVerbraucht_voll`;
`kapZeilenLaenge : KapDekodiert → Option Nat` with
`kapZeilenLaenge_fixiert` and `kapZeilenLaenge_lockAdr_verweigert`
(`lockAdr → none`: its `AdrForm` does not fix SIB presence, verified
against `parseAdrTail`).

**§2 Prefix-style VEX decode.** `dekodiereAvx2Prefix`;
`avxPrefix_paddq/pxor/movdquLd/movdquSt`,
`avxPrefix_vex128_verweigert`, `avxPrefix_fremd_verweigert` (`decide`);
`avxPrefix_genau` (exact-list agreement); `avxPrefix_verbraucht`
(stated length within 1..15).

**§3 Prefix-closed chain.** `kapDecodePrefix`;
`kapDecodePrefix_genau`; `avxPrefix_mitte_lock`,
`avxPrefix_mitte_streu`; `kapPrefix_avx2_fortschritt`.

**§4 Per-arm progress** (one accepted lemma + `omega` each): nine
`kapFortschritt_*` wrappers (kompakt, kern, breit-wd, ext
pilot/narrow/muldiv/shift/setcc/cmov).

**§5 Coverage advance.** `kapDeckt_schritt_verbraucht`.

**§6 Witnesses.** `kapVerbraucht_zeuge` (all eight arms positive),
three pinned lengths.

**§7 Chain-tied overlap rows** (R1 repair, see above).

**§8 Declared-vs-measured agreement** (R2 repair, see above).

## Probe repair history

- Pre-probe self-review: fixed a false `kapZeilenLaenge_fixiert` and two
  arity bugs.
- First probe 30 errors → fixed `[]` ascription (23 knock-ons), added
  `Option.some.injEq` before `Prod.mk.injEq` (branch value is
  `some (pair)`), restructured the coverage step to `rw` +
  `simp only [if_pos …]`.
- Second probe 4 errors → `simp [htake]` for literal lengths.
- Repair turn (R1/R2): probe 0 errors, full build exit 0, no new error
  classes (new theorems reuse the same checked patterns).

## Open (unchanged, in CUTS)

Arbitrary-input progress for s32/MXCSR/LOCK/lockAdr/FP/vector arms and
the top-level width dispatcher; chain-level mid-section VEX (seven
earlier arms' refusal of VEX-led lists with trailing bytes unmeasured);
cross-decoder length comparison on overlap rows (a differing row would
be a finding; none recorded). No silicon re-check; no W/GX bridge; no
source/checker/contract/entry/ABI/loader/budget/liveness claim.
Vendor-neutral (rule 17).

## Note on the lane file

The MECHANISM paragraph (§28, `HwAdapter`) is generic boilerplate
conflicting with the specific TASK (§25); the specific task was
implemented. No existing file was changed except the one owned import
line in `grammatik/Grammatik.lean`.
