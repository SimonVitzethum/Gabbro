# MUSE-REPORT-307: Independent review of candidate 291 (X86/Relokation.lean)

Lane 307, independent candidate review. Reviewed ONLY the pinned snapshot
`.tmp/review/author-291/` (SNAPSHOT.json: author 291, HEAD
`4d1e4f6d5f2a42dbcf6da37f181cb704e6177993`, base
`f49581505cda367b97d4f3d89faa1b2f33413497`, clean true) and its
BUILD-EVIDENCE.json tool log. No other clone read, no code or central file
edited. This report is the only owned deliverable.

Owner task (OWNER-TASK.md): `grammatik/Grammatik/X86/Relokation.lean` —
canonical address-relative rel32 calculation (target minus actual next-RIP),
signed-32 fit/refusal with generic sign-extension target equation under exact
no-wrap/address premises, abs64 values, finite `List Byte` operand/data-field
patching with range/disjoint checks, exact patched bytes + outside-site
preservation, concrete negative/boundary/out-of-range/overlap refusal
witnesses. Reuse canonical Byte/Wort, wortByte, address arithmetic; no second
model. Code-operand vs data-site admissibility belongs to the checked
image+decoder proof; caller-claimed starts/kinds untrusted. Helper
arithmetic/patching green but complete relocation acceptance explicitly
OPEN/refused. No loader/linker assumption, no final-byte source claim.

## What was checked

- Read the full snapshot file (675 lines): all definitions, theorem
  statements AND proofs, CUTS block, `#print axioms` lines.
- Read MUSE-REPORT-291.md and PATCH.diff (3 files: report, one additive
  `import Grammatik.X86.Relokation` in `grammatik/Grammatik.lean`, the new
  file). No Rust, no diagnostic/gift/example/CLI/MARKE numbers.
- Read BUILD-EVIDENCE.json end to end (final `./lean-bau`: exit 0,
  0 errors, 369 jobs; final `./lean-probe`: 0 errors with axiom output;
  intermediate red iterations are normal development, not evidence against).
- Ran `./lean-probe .tmp/review/author-291/grammatik/Grammatik/X86/Relokation.lean`
  independently: first line `== 0 error(s) in the COMPLETE output`, axiom
  lines identical to the author's (every theorem: no axioms or subset of
  `[propext, Quot.sound]`; no `Classical.choice`).
- Grepped the snapshot for forbidden tactics (`sorry|admit|axiom|
  native_decide|unsafe` as code): no hits (only `#print axioms` lines and
  the English word "axiom" in a doc comment). No `Prop`-typed premise, no
  `intro _` / `have _ :=`, no N-codes, MARKE, example or name-specific
  rules anywhere in the file.
- Verified canonical reuse against this clone's sources: `wortByte`/
  `bytesWort`/`bytesWort_wortByte` are `Speicher.lean` (lines 18/36/309),
  `sext` is `Wort.lean` (line 60). Imports are exactly
  `Typen`/`Speicher`/`Wort`. No second image/register/ISA model;
  `RelArt` is an admissibility class, not a model.

## Claim-by-claim cross-check (all hold)

- Site admissibility: `RelArt` + `relAnnahmeEndgueltig` constantly `false`
  + `relAnnahme_offen` proved by `cases` — honest by construction, refuses
  final validation at helper level. Not a restated premise.
- rel32: `rel32Passt` exact signed-32 bounds; `rel32_rundgang` generic
  over all in-range `d`, both premises load-bearing in the `omega` closes.
- Address equations: `rel32_adress_gleichung` needs no wrap premises
  (modular `ofNat` addition is wrap-consistent; author documents this as a
  finding after the linter caught dead premises — credible). Exact no-wrap
  premises live only in `rel32_next_rip`, each used by the rewrite.
  `rel32Fuer` refuses out-of-range with `none` (`rel32Fuer_verweigert`);
  in-range hits decode back (`rel32Fuer_trifft` via the generic round-trip).
- abs64: `abs64Bytes` via `wortByte`, `abs64Wort` via `bytesWort` (wrong
  width `none`), `abs64_rundgang` is exactly `bytesWort_wortByte` — no
  second codec, as claimed.
- Patching: `patchAt` refuses overrun including empty-patch-past-end;
  `patchAt_bereich`/`_laenge`/`_stelle`/`_rahmen` all present and generic.
  `patchZwei` refuses overlap on lengths of the actual patch lists (no
  caller-claimed register), `patchZwei_erhaelt_erste` keeps the first site.
  `patchRel32`/`patchAbs64` corollaries + width facts (4/8) present.
- Probes recomputed by hand: -5 = `FB FF FF FF` LE correct; boundaries
  `2^31-1`/`-2^31` fit with exact bytes, `±2^31` refused; `rel32Fuer 0
  2^31 = none`, `rel32Fuer 10 0 = some (rel32Bytes (-10))` correct;
  `0x1005 -> 0x1000` address equation and next-RIP probe correct;
  abs64 `0x0102030405060708` LE bytes correct; overlap `[1,2)` vs `[2,2)`
  refused, disjoint sites exact, 2-byte patch at offset 2 of 3-byte image
  refused. `sonde_abs64_rund` is an instance of the generic theorem, not
  just `decide` — stronger than required.
- Boundaries: no source/target/cost/TSO/hardware claim is made; CUTS
  lists site admissibility, loader/linker, load bias, entry states,
  per-instruction correspondence, control-target, ABI, concurrency and
  cost as OPEN/separate. Matches the owner task's explicit OPEN/refused
  requirement. No final-byte source claim anywhere.
- Inhabitation: no premise quantifies over program syntax and the task
  names no `ZEUGE:` target, so no `_zeuge` is owed; the §6 probes are real
  operand/byte values over the actual helpers, as the owner task requires
  for target helpers.

## Notes (not defects, no action required)

- `rel32Byte` maps every index >= 3 to the top byte, but it is only ever
  called with 0..3 via `rel32Bytes`. Unreachable through the delivered API.
- Only the first site's survival is stated for double patches; the second
  follows directly from `patchAt_stelle` + the second patch hypothesis.
- `#print axioms` covers the 18 main theorems; the remaining `decide`
  probes print nothing, which is fine.

No counterexample reproduced because no finding was made; every probe value
above was hand-verified correct against two's-complement/little-endian arithmetic.

## Verdict

The bounded delivered claim — checked relocation arithmetic and byte
patching helpers with generic round-trip/range/frame/disjointness theorems,
concrete probes, and complete relocation acceptance explicitly OPEN — is
true. Actual needed checks green (independent `./lean-probe`: 0 errors,
standard axioms), proof/witness gates hold, no material defect remains.
ACCEPT does not mean whole-compiler or binary validation is complete; the
file itself states that boundary.

CANDIDATE: 291 4d1e4f6d5f2a42dbcf6da37f181cb704e6177993
VERDICT: ACCEPT
