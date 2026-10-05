# MUSE-REPORT-1280: Exact re-review of repaired candidate 1279 (repair R1-R4)

CANDIDATE: 1279 841552736804ae4ea154591764d957b6f3c6b377
VERDICT: ACCEPT

All four findings of the previous REPAIR (head b7ffb7c9) are
verified fixed in the new head: the silicon statement is now true
to the supplied extract with FREE honestly marked beyond-evidence,
the fabricated rule citation is gone, the author report describes
exactly one candidate, and the counts/theorem coverage are exact.
The executed machine never moved and stays Intel-exact; the
admissibility relation is extra, honestly labeled, and claims
nothing beyond self-consistency. The previous REPAIR is superseded
and stale, not carried over.

Clone `/home/simon/Dokumente/gabbro-muse/a1280`, branch `muse/1280`
(`.git/HEAD` reads `ref: refs/heads/muse/1280`; verified first, no mismatch).
Owned file: only this report. No Lean or Rust code added or changed by
this lane.

## Review basis

New pinned `.tmp/review/SNAPSHOT.json` (author 1279, head
`841552736804ae4ea154591764d957b6f3c6b377`, base
`738366545afbddf7ac664db92804703db24f8868`, same three files, clean
true). The author clone was not touched (HARD RULES 1). Read in full:
the new 1868-line `IntBitScan.lean`, the complete new `PATCH.diff`
(same three files, one import line at `PATCH.diff` line 202), the
new `MUSE-REPORT-1279.md` (187 lines, incl. the "Re-review fixes
(R1-R4)" section), the new `BUILD-EVIDENCE.json` (final probe 0
errors with all 29 axiom prints, final bau exit 0/659 jobs, commit
`84155273` last), the unchanged `OWNER-TASK.md`, the SDM extract,
`REFERENCES.json`, and this clone's `AGENTS.md`.

## Repair verification (R1-R4)

- R1 fixed: the `BsScanZulaessig` doc comment
  (`IntBitScan.lean:823-832`) now states the Intel-defined facts
  with exact extract lines (destination unmodified ll.
  42739/42822; full flag row ll. 42755-42758/42838-42840), marks
  FREE an explicitly beyond-evidence portability abstraction, and
  disclaims vendor differences (`REFERENCES.json`: AMD URLs 404).
  No false silicon claim remains; no AMD behavior is asserted.
- R2 fixed: no AGENTS.md standing-rule citation anywhere in the
  file or the author report. CUTS states plainly that the FREE
  modeling "cites no AGENTS.md rule (none exists in this tree)
  and no AMD reference (none is supplied per `REFERENCES.json`)",
  verified true against this tree.
- R3 fixed: `MUSE-REPORT-1279.md` marks the superseded corrections
  historical ("described commit cf407e52; superseded by the repair
  section above, which governs the current head") and both the
  report and the file CUTS now describe exactly one candidate.
- R4 fixed: 29 `#print axioms` lines
  (`IntBitScan.lean:1838-1866`: 21 old plus 8 new, now including
  `bsScan_rahmen_allgemein`); 16 `bs_nichts_*` decode refusals as
  stated; `popNull` is now used in code by two kernel-checked
  concrete pins (`pin_popnull_scanZF_voll/null`, both `decide`,
  no general equivalence claimed).

## Re-verified standing properties

- Same three owned files, one import line; no other existing file
  touched.
- No forbidden tactics or declarations in the new file (only
  English "admitted"/"admits" in comments).
- Author evidence: final probe 0 errors with all 29 axiom prints
  inside `propext`/`Classical.choice`/`Quot.sound`; final bau
  exit 0, 659 jobs, committed as `84155273` with only the
  add-and-commit after.
- Accepted evaluator still lifted, never copied (new reuse
  `regSet_fremd` verified at `Ausfuehrung.lean:144`); every
  premise of every new theorem used; executed step, adapter and
  machine outcome unchanged from the reviewed version.
- Planted refusals still refuse; dispatcher selection exact;
  witness `bsHw_zeuge` still non-degenerate (two cores, index 4
  and count 8, in-place swap, owner-only forwarding of byte 42,
  drain changing shared memory 0 to 42, zero-source ZF, refusals
  beside it).
- Unchanged silicon parts still match the extract; mem-row
  round-trip composition still openly cut with the same stated
  obstruction; no W/GX or hardware-correspondence claim.

## Why ACCEPT now

The defect was never the machine (always Intel-exact) but the
spec-level relation plus its false justification and the
contradictory report. All three are repaired and the repairs are
verified above, not taken on word. What remains is a named,
honestly bounded modeling choice -- FREE as an explicitly
beyond-evidence abstraction beside the exact executed reference
-- which the owner task's own wording ("free/unchanged ... a
named choice") permits, with the Intel facts stated correctly
alongside. Nothing proved was weakened: every Intel-exact
statement of the previous candidate still holds in the new one.

## Reviewer build

`./lean-bau` re-run in this review clone (report-only lane, no Lean
code touched): `Build completed successfully (676 jobs).` Green.
The candidate file is not part of this tree (snapshot only); the
merge gate rebuilds `grammatik/` mechanically before committing.
