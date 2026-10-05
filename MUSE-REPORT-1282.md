# MUSE-REPORT-1282: exact re-review, report-only delta after repair

CANDIDATE: 1281 5a342c81653b1cf6c784526f6a7810ba178c0c39
VERDICT: ACCEPT

## Materials and procedure

Clone `/home/simon/Dokumente/gabbro-muse/a1282`, branch `muse/1282`, verified.
Reviewed the NEW pinned snapshot only (`.tmp/review/SNAPSHOT.json`: head as in
the candidate line above, base `738366545afbddf7ac664db92804703db24f8868`,
`clean: true`). The author chain since the last accepted snapshot is one
report-only commit (`0df79741` repair report → `5a342c81` integration-gate
note); the Lean deliverable is byte-identical in length and repair markers
(1779 lines; nop-first `bb == 0 && lo == 0` in `decodeSx90`; NOTE citation in
CUTS; new NOP pins, `hne`-premised round-trips, step-equivalence theorems and
new no-shadow rows all present). `PATCH.diff` touches the same three owned
files with the single import line. Forbidden-token re-scan is clean (only
English "admit*" in comments). `BUILD-EVIDENCE.json` shows a fresh green
`./lean-bau` (659 jobs, unchanged `propext` / `propext + Quot.sound` axioms)
after the repair commit. Own tree `grammatik/` untouched; reviewer added no
definitions. Last `./lean-bau` on this clean tree (no changes since):
`Build completed successfully (672 jobs).`

## What the delta contains

The new commit adds only the "Integration gate failure" report section: the
merge build failed with no error in the owned module (standard axiom `info:`
lines for the candidate, single `error:` naming an unreadable toolchain file
`FunInd.olean.private` at an early `Grammatik.lean` import line far from the
lane's appended hunk), plus a fresh local green build at the same commit.
The author draws the apparatus conclusion (broken merge-checkout toolchain,
nothing to repair in the deliverable, no guarantee traded for green) and asks
the coordinator to repair or replace that toolchain installation.

## Assessment

The Lean candidate is the repaired content this review already accepted: every
prior finding stays fixed, no proof was changed adversely, no new claim is
made in Lean. The report delta is consistent with its presented evidence (the
quoted error text names toolchain apparatus, not candidate code; the module
half is backed by a fresh green build in evidence). The toolchain diagnosis
itself is NOT independently verifiable from this clone — the merge checkout
lies outside this lane's directory and is untouchable under HARD RULES — so
this acceptance certifies the candidate diff only, not the state of the merge
apparatus. Recommended coordinator action matches the author's: fix the
toolchain installation, then re-run the merge build unchanged.

## Carried nits (non-blocking, unchanged)

Stale counts and the superseded redundant-REX sentence in the author report
body (the file's CUTS is the consistent record); two CUTS over-refusal
bullets that read like refusals which no longer occur ("non-`0x48` REX on
`98`/`99`", "REX without W on `87` outside `66`" — the decoder correctly
accepts those valid inputs). Suggest rewording on a later touch.

## Open (unchanged)

No silicon proof beyond cited rows, no W/GX bridge, timing, or
source/loader/entry/budget link. None claimed.
