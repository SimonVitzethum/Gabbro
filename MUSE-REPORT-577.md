# MUSE-REPORT-577: Independent exact-candidate connection review of 559

Lane 577, clone `/home/simon/Dokumente/gabbro-muse/a577`, branch `muse/577`.
Owns only this report (report-only review, no Lean changes committed).

CANDIDATE: 559 35b21332edf71967278a4eb46d2ac97c3882d556
VERDICT: ACCEPT

## What was reviewed

- Snapshot `.tmp/review/SNAPSHOT.json`: author 559, pinned HEAD
  `35b21332edf71967278a4eb46d2ac97c3882d556`, base `8596f83e` (present in
  this clone), files `MUSE-REPORT-559.md`, `grammatik/Grammatik.lean` (one
  additive import), `grammatik/Grammatik/X86/DecoderSoundness.lean` (343 lines).
- Owner task (lane 559): arbitrary-input pilot decoder soundness over
  `Codec.decode` — generic consumed-length/suffix agreement with 1..15
  bounds, connection to `Byteschritt.fetchDekodiert`, all pilot branches
  with hand-written non-roundtrip input plus trailing bytes, truncated/
  corrupted refusals, no second decoder, no assumed soundness.
- Actual candidate inspected at `.tmp/review/author-559/` (`PATCH.diff` +
  full file copies); candidate file applied to this clone for verification,
  then fully reverted (working tree clean, no import residue).

## Verification performed (queued wrappers, this clone)

- `grep` over the candidate: no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe`, no `intro _`, no `have _ :=` premise discard. Clean.
- `./lean-probe grammatik/Grammatik/X86/DecoderSoundness.lean` with the
  candidate applied: `== 0 error(s) in the COMPLETE output; exit 0`.
  All 34 theorems/definitions elaborate; `#print axioms` lines confirm:
  `laengeOk_grenzen` axiom-free; `decode_verbraucht_praefix`,
  `fetch_verbraucht_praefix` and both `_zeuge` on `[propext, Quot.sound]`;
  all 20 probes and 9 refusals on `[propext]` — all within the standard
  goal axioms (`propext`, `Classical.choice`, `Quot.sound`).
- `./lean-bau` with the candidate applied:
  `Build completed successfully (428 jobs).` Whole project green, matching
  the author's build evidence (428 jobs).
- Producer names resolved against master: `Codec.decode`/`natByte`,
  `Ausfuehrung.laengeOk`/`schritt`, `Byteschritt.geholt`/
  `fetchDekodiert`/`fetchDekodiert_entspricht`/`fetch_nutzt_nur_praefix`/
  `ausgangByte`/`byteschritt`/`fetchCap`/`ausfuehrbarN`,
  `DecodingCoverage.decode_abdeckung`/`decode_fenster_kongruenz` and witness
  states `dcStart`/`dcAbholStart` all exist with the used signatures.
- Branch coverage checked against `decktAb` (8 disjunct groups, 14 pilot
  constructors): ret; push low(1)/high(2); pop low(1)/high(2); movImm64
  rax/r8 (10); mov/add/sub/xor/cmp reg (3) plus extended add; load/store
  ohne SIB (7); load/store SIB (8); call32/jump32 (5); jumpIf32 (6). Every
  group is hit with literal `natByte` bytes (never `encode` output), each
  with a trailing byte proving suffix passthrough. The 9 refusals
  (truncated REX/imm/SIB/call, forged SIB, bad opcode, mod=1 load,
  pseudo-branch, bad push/pop extension) are all `rfl` facts the probe run
  confirms.
- Witnesses: `decode_verbraucht_praefix_zeuge` and
  `fetch_verbraucht_praefix_zeuge` jointly instantiate decode/fetch
  agreement with concrete bytes and prove real memory change 0 → 42 via
  `schritt`/`byteschritt` (`by decide` passes, so the execution is real,
  not asserted). Rule-13 source-syntax obligation does not trigger (no
  `Vertrag`/`Stmt` premises, no `ZEUGE:` targets); the witnesses exceed
  the mechanical minimum anyway.
- No vacuity: the generic theorems quantify over arbitrary `bs`/`s` with a
  success hypothesis, and the 20 positive probes plus 2 witnesses prove the
  hypothesis is inhabited on every branch; the 9 refusals prove the decoder
  is not trivially-accepting. No copied premise as conclusion, no second
  decoder, no guessed ISA bytes (all probe bytes verified by `decide`
  against the actual `decode`), no contract-duty weakening (no contracts
  involved), no hardware/source/TSO claim — CUTS block states exactly
  these exclusions.

## Honest thinness note (not a defect)

The core arbitrary-input proof already exists as
`DecodingCoverage.decode_abdeckung` + `decode_fenster_kongruenz` (lane 435);
the two main theorems repackage them with explicit numeric 1..15 bounds and
a single combined decode/fetch statement. The author discloses this overlap
in their report §findings-1. The task explicitly asked for this packaging
plus full literal branch coverage, refusals and joint witnesses, which is
what was delivered — so the thinness is faithful execution, not decoration.
No decoder defect was hidden: all literal probes decode as stated.

## Exact accepted bounded claim

- `laengeOk_grenzen`: `laengeOk` unfolds to numeric 1..15.
- `decode_verbraucht_praefix`: for arbitrary `bs`, successful `decode`
  consumes exactly `d.laenge` (length equation + drop-suffix) within
  1..15 — decoder self-consistency only.
- `fetch_verbraucht_praefix`: a successful `fetchDekodiert` carries the
  same agreement into the fetched window plus window fit, 15-byte cap fit
  and executable consumed prefix.
- 20 literal branch probes, 9 refusal probes, 2 joint memory-changing
  witnesses (0 → 42). NOT accepted: hardware correspondence, full x86
  coverage, source/TSO/concurrency/cost/ABI/entry/relocation, whole-image
  validation, termination.

## Producer/consumer interface and next integration

- Stable entry points for lanes 560/561/575: `fetch_verbraucht_praefix`
  (one hypothesis yields window equation, bounds, cap fit, executable
  prefix) and `decode_verbraucht_praefix` at pure-decode level.
- Measurable next step: lane 560 replaces its length-side derivation with
  `decode_verbraucht_praefix`; success = fewer decoder case splits with
  identical `eintritt_abdeckung` conclusions.
- Note for lane 575 (from author finding 3, confirmed real): the private
  `.tmp/foreign-typen-diff.patch` adding `callReg64`/`jmpReg64`/
  `callMem64`/`jmpMem64` to `Typen.lean` is uncommitted foreign work; if it
  lands, this module's per-branch coverage needs extension. Not this
  candidate's problem.

## Repairs required

None. No minimal repairs; nothing in the task statement was found wrong.

## Build result

`./lean-bau` with candidate applied: `Build completed successfully
(428 jobs).` `./lean-probe` on the candidate file:
`== 0 error(s) in the COMPLETE output; exit 0.` Candidate reverted after
verification; this commit is report-only.
