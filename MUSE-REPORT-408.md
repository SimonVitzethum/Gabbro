# Muse report 408 — adversarial implementation audit: WEAK-MEMORY

- Branch `muse/408`, base `0b3132b7`. Owns ONLY
  `dokumente/x86/AUDIT-WEAK-MEMORY.md` (new) and this report.
- No Lean file added or changed; no model, goal, checker, emitter or
  ledger change. Docs-only audit lane.

## What was done

Read the accepted weak-memory implementations in full at this HEAD —
`X86/TSO.lean` (622 lines), `X86/Zugriffe.lean` (696), `X86/AccessList.lean`
(280), `X86/LockedOps.lean` (521), `X86/OverlapRefusal.lean` (415),
`X86/SpillPrivate.lean` (399) — plus `TSO-GX-BRUECKE.md`, `REVIEW-TSO.md`,
`WORK-ALLOCATION.md`, the `SchrittW`/`schwach_ist_gX` source legs, and the
DIRECT-COMPILER record. Verified every cited file:line by reading, and
re-checked the pilot `Befehl` set (still 14, still 64-bit-only) and the
absence of `NarrowOps`/`FenceDrain`/`TableLayout`/`ScalarFloat` modules.

Ran one private probe file `.tmp/WEAK-PROBE.lean` (NOT committed, stays in
private `$TMPDIR`) through `./lean-probe`: 0 errors. It proves the F2
finding is real behaviour, not prose: `lockSchritt` and `casSchritt` with
one pending own-buffer byte both evaluate to `none`, while the same LOCK
on the empty buffer succeeds.

Produced `dokumente/x86/AUDIT-WEAK-MEMORY.md`: verdict (all six modules
correct within their stated claims; no DRF-SC and no word-atomicity
claims exist — both must-nots verified by inspection), per-module
evidence with file:line references, 11 prioritized findings F1–F11 (all
consumer gaps, none a bug in a proved claim), explicit non-findings, and
CUTS.

## New definitions/theorems

None. No Lean work; nothing to witness and no `#print axioms` owed.

## Last build result

No `./lean-bau` run: no Lean file was touched, so no build was needed.
`./lean-probe .tmp/WEAK-PROBE.lean`: 0 errors in the complete output,
exit 0.

## What remains open

The audit itself is complete and committed. Its findings F1–F11 are bridge
work for other owners (combined TSO+LOCK machine, D-lower drain
scheduling, unified footprint extraction, alignment-lemma unification,
`GetrenntK` rename, TableLayout C1, NarrowOps A1, OBS-5, word atomicity
lane 421). Lanes 344 (FenceDrain) and 350 (AtomicPayload) are unmerged
candidates this audit deliberately does not pre-judge.

## What I believe is wrong in the task or surroundings

Nothing in the task is wrong. One planning note: DIRECT-COMPILER.md
already schedules lane 421 (WordAtomicity); finding F10 was scoped to
avoid overlapping it. The `GetrenntK` name clash (F5) is worth fixing
soon because it can misroute an O-spill discharge silently.
