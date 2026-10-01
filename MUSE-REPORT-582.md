# MUSE-REPORT-582: Independent exact-candidate connection review of 564

## Reviewed commit

CANDIDATE: 564 2093306903709469257dd761503566651a462316

## What was done

- Verified clone path `/home/simon/Dokumente/gabbro-muse/a582`, branch `muse/582`.
- Read `.tmp/review/SNAPSHOT.json` (base `8596f83e`, 3 files), the lane task
  `lanes/564.md`, the report `MUSE-REPORT-564.md`, and the full new file
  `grammatik/Grammatik/X86/ShiftCodec.lean` (726 lines) from the pinned commit.
- Checked every producer name resolves to real accepted definitions:
  `shlB`/`shrB`/`sarB`, `schiebeZaehler`, `SchiebeGueltig` (`Ganzzahl.lean`);
  `shlNachweis`/`shrNachweis`/`sarNachweis`, `shiftOpWert`,
  `shlUeberlauf`/`shrUeberlauf`/`sarUeberlauf` (`ShiftLogic.lean`);
  `encode`/`decode`, `codeReg`/`regCode`, `regHigh`/`regLow`, `rexByte`,
  `natByte`/`byteNat` (`Codec.lean`); `schritt`/`schrittRegister`/`ripNach`/
  `laengeOk` (`Ausfuehrung.lean`); `read64` (`Speicher.lean`).
- Producer files are byte-identical between the reviewed base `8596f83e`
  and this clone's HEAD; only additive umbrella imports differ. Reproduction
  below is therefore faithful to the reviewed commit.
- Grepped the new file for `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
  discarded premises and `Prop`-typed premises: clean (only benign
  substrings such as "admitted" in comments).
- Reproduced through queued wrappers with the reviewed file placed
  temporarily in-tree (removed afterwards; final tree owns only this report):
  - `./lean-probe grammatik/Grammatik/X86/ShiftCodec.lean`:
    `== 0 error(s) in the COMPLETE output; exit 0`.
  - `./lean-bau`: `Build completed successfully (430 jobs).`
  - `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
    `gabbro_ziel` and all siblings still depend only on
    `[propext, Classical.choice, Quot.sound]` (unchanged).
- Tree restored to clean afterwards (`git status` empty, HEAD unchanged).

## Semantic findings

- ISA rows are right: `REX.W C1 /r ib` (len 4) and `REX.W D3 /r` (len 3),
  digits /4 SHL, /5 SHR, /7 SAR, register-direct mod=3, B-bit extension to
  r8-r15. Refusing REX.R rows 76/77 is a safe under-approximation of admitted
  rows, disclosed in the file; no false hardware claim is proved (CUTS
  explicitly disclaims silicon correspondence).
- Count handling matches hardware: CL form reads the low byte of `rcx`
  (`% 256`) composed with `schiebeZaehler` (`% 64` at `.b64`); imm8 65 masks
  to 1 through bytes (`probe_gross_ueber_byte`). Zero masked count advances
  RIP with flags/registers untouched (`shiftSchritt_null`,
  `shiftSchritt_null_flags`); only nonzero counts install the evidence
  snapshot. AF stays `none`; OF collapse (`getD false`) for wider counts is
  covered only by the weak `SchiebeGueltig`, which constrains nothing there,
  so downstream readers must not treat `of` as hardware truth past count 1.
- Real reuse, no duplication: values route to `shiftOpWert`
  (`richtungWert_routen`, 4th arg `0` is the genuinely unused slot),
  evidence reuses `shl/shr/sarNachweis` with `shiftFlags_gueltig` pinning
  overflow exactly at masked count one, steps reuse `schrittRegister`/
  `ripNach`. Neither decoder is rewritten: both dispatch theorems close by
  computation (`rfl`) generically over all forms / all 14 pilot `Befehl`
  constructors with arbitrary suffix, so refusal is operand- and
  suffix-independent.
- Joint witness is non-vacuous: `shift_kette_dekode` decodes actual program
  bytes to `shl rax, 1`; `shift_kette_schritt` steps 1 to 2 with RIP 4096 to
  4100 and CF false; `shift_kette_speicher` chains the existing pilot
  `store64` so the data cell observably changes 0 to 2, plus a planted
  length-5 refusal. No source-syntax quantification exists in the file, so no
  rule-13 `_zeuge` is owed; the witness covers its intent.
- Two minor notes, neither blocking: (1) the lane report understates axioms
  (roundtrips depend on `[propext, Classical.choice, Quot.sound]`, not only
  propext/Quot.sound) — still within the standard goal set; (2) no single
  chaining lemma states decode-then-step in one theorem; both sides are pinned
  on identical concrete bytes instead, which is sufficient for the bounded
  claim but is the natural next strengthening.

## Accepted bounded claim

Canonical byte codec plus execution connection for 64-bit register-direct
`shift r64, imm8` and `shift r64, CL` over admitted REX.W rows 72/73 with
mod-3 ModRM digits /4, /5, /7; two-sided dispatch against the 14-form pilot
decoder; `ShiftLogic` value/evidence reuse at `.b64` with zero-count flag
preservation; count-0/1/large, mutation and truncation pins; one joint
decoded-shift-into-pilot-store witness with observable memory change and a
planted refusal. No hardware, source, TSO, image, cost, entry or relocation
claim (per CUTS).

## Producer/consumer interface and next integration

Producers: `encodeShift`, `roundtripShiftImm`/`roundtripShiftCl` (+`_len_ok`),
`pilot_verweigert_shift`. Consumers: `decodeShift`, `shiftSchritt`,
`shift_verweigert_pilot`, `shiftSchritt_nachweis_gueltig` (with
`shiftSchritt_flags`/`_wert`). Measurable next step: a `fetchDekodiert`-style
executable-memory fetch feeding `decodeShift`/`shiftSchritt`, with a consumer
that dispatches REX-C1/D3 rows here while keeping the two refusal theorems as
the dispatch contract.

## What remains open

Per CUTS: hardware correspondence, source correspondence, TSO bridge,
whole-image coverage, cost transfer, entry/ABI/relocation, narrow widths,
memory-operand shifts, rotates, flag subtleties beyond `SchiebeGueltig`,
termination-style claims. Nothing in the lane task text looks wrong.

## New definitions/theorems added by this review

None. Review-only lane; no Lean or Rust changes.

## Last build result

`Build completed successfully (430 jobs).` (with reviewed file in-tree;
final tree is clean and owns only this report).

VERDICT: ACCEPT
