# MUSE-REPORT-1282: exact re-review with independent probe

CANDIDATE: 1281 5a342c81653b1cf6c784526f6a7810ba178c0c39
VERDICT: ACCEPT

## Materials and procedure

Clone `/home/simon/Dokumente/gabbro-muse/a1282`, branch `muse/1282`, verified.
Reviewed the pinned snapshot only (`.tmp/review/SNAPSHOT.json`: head as in
the candidate line above, base `738366545afbddf7ac664db92804703db24f8868`,
`clean: true`): `PATCH.diff` (same three owned files, single import line),
the full `IntSignXchg.lean` (1779 lines, read end to end across turns),
`MUSE-REPORT-1281.md` with repair and integration-gate sections,
`OWNER-TASK.md`, `BUILD-EVIDENCE.json` (final green `./lean-bau`, 659 jobs,
`propext` / `propext + Quot.sound`). No `git show/log/diff` against the
author HEAD was attempted (unreadable by design; never treated as a finding).
Own tree `grammatik/` untouched; reviewer added no definitions. Last
`./lean-bau` on this clean tree: `Build completed successfully (672 jobs).`

## Independent probe (new evidence this turn)

Per the review correction, the candidate file was to be copied into this
clone's `grammatik/Grammatik/X86/` for probing. The shell copy was rejected
twice by the permission classifier, so instead the delivered file was probed
in place at its snapshot path (identical bytes; imports resolve through the
project `LEAN_PATH`, so location is immaterial):
`./lean-probe .tmp/review/author-1281/grammatik/Grammatik/X86/IntSignXchg.lean`
prints `== 0 error(s) in the COMPLETE output; exit 0`, with only the already
declared benign `unusedSimpArgs` linter warnings. This independently confirms
the author's build evidence AND cross-checks a newer base: the file elaborates
cleanly against this clone's accepted dependencies (newer HEAD than the author
base), so there is no base-drift breakage either. Nothing was copied, no
import line was added, `git status` stays clean apart from this report.

## Assessment (unchanged substance, re-confirmed)

The Lean deliverable is the repaired content accepted in the previous turn:
every `90H` resolving to the RAX self decodes to `.nop` under every prefix
(verified code plus five `decide` pins); no `90H` byte encodes a
zero-extension (encoder canonicalizes RAX-self to the `87` forms, backed by
the step-equivalence theorems and honestly premised `r ≠ .rax` round-trips);
CUTS cites the NOP-alias NOTE with 19 no-shadow rows; adapter, witness,
refusal table and lift theorems all stand as previously checked. Forbidden
constructs absent (re-scanned), premises used (spot-checked, no discards),
accepted evaluators lifted not copied, no file outside the three owned ones
touched. The integration-gate note in the author report describes merge
apparatus outside this lane's reach; it changes no Lean content and its
toolchain diagnosis is noted, not certified, here.

## Carried nits (non-blocking)

Stale counts and the superseded redundant-REX sentence in the author report
body (its CUTS is the consistent record); two CUTS over-refusal bullets that
read like refusals which no longer occur (decoder correctly accepts those
valid inputs). Suggest rewording on a later touch.

## Open (unchanged)

No silicon proof beyond cited rows, no W/GX bridge, timing, or
source/loader/entry/budget link. None claimed.
