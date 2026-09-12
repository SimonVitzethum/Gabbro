# MUSE-REPORT-17

Lane 17, SATZKARTE draft B of 2. No Lean changes (task-ordered).

## What I did

Wrote `dokumente/SATZKARTE-B.md` (English): for
`ziel_nutzer_last_aus_pc_Q` (`grammatik/Grammatik/Ziel.lean:2324`)
one plain-English sentence per conjunct of the 12-way conclusion
(`:2394-2416`), then one table row per premise with name,
one-sentence meaning, class (OWN-LOGIC / NAMED-HW / GABBRO-DUTY /
OPEN), and the exact Lean discharger or "none". Every claim verified
by reading the Lean; every row cites `file:line`. Flagged 12
applicability problems in §3 (guard existence for all carriers,
global watch undischarged, `GeteiltGedeckt` excluding racy programs,
`InvariantForm` excluding functional contracts, per-firing `hBlattAll`,
ensures-at-entry, `J`-wiring with only a single-thread discharger,
mark separation excluding same-function threads, single-deadline probe
with per-use spacing, event-emitting oracles, lowering fragment
boundary, two-access single-table order narrowing).

## New definitions/theorems

None. No Lean file touched (`git status` shows only
`dokumente/SATZKARTE-B.md` and this report as new files).

## Last `./lean-bau` result line

`Build completed successfully (29 jobs).` (full project green; no Lean
changes were made, so this was a confirmation run, not a repair).

## What remains open

Nothing assigned remains: the card is written and committed. Open
*content* (not my task to close): the 12 applicability flags in
`dokumente/SATZKARTE-B.md` §3 — each names a premise or conclusion
shape that keeps the theorem from applying to ordinary programs
(lock-free data, globals, racy code, functional contracts,
same-function threads, multi-deadline probes, event-emitting oracles).

## What I believe is wrong in the task

Two small things, neither blocking:

1. The task names `QRequires`/`QEnsures` as "(around line 1432)" of
   `Extraktion.lean`; they are at `:1437`/`:1442` (`QExpr` is at
   `:1432`). The card cites the exact lines.
2. The task says "one table row per PREMISE" but the theorem also takes
   ~30 subject inputs (`P`, `O`, `J`, `t₀`, `hw₁`, …) that are no
   one's duty to discharge. I listed those once as classless subjects
   and gave table rows to the actual obligations plus the three
   fragment inputs (`hne`, `hw₁`, `hw₂`); forcing every binder into
   the four-class scheme would have mislabeled inputs as OPEN
   obligations.
