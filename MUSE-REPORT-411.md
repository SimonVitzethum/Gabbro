# MUSE-REPORT-411: Adversarial implementation audit: DYNAMIC-REGIONS

## What was done

Wrote the owned audit `dokumente/x86/AUDIT-DYNAMIC-REGIONS.md` (8 sections).
No Lean, Rust, or central file was added or changed; no second IR, toy
machine, or vacuous theorem was built. Read-only verification only.

Files actually read (all with file/theorem/line anchors in the audit):
`grammatik/Grammatik/X86/Regionen.lean` (full), `X86/Speicher.lean`,
`X86/OverlapRefusal.lean`, `X86/AccessList.lean` (header + CUTS),
`Grammatik/ArenaDyn.lean` (ceiling + `Form`), `Zielsatz/Spec.lean`
(arena-runtime block, premises (d) reserve/commit, M10, DynForm note),
`Grammatik/SchablonenOhneLibc.lean` §4 (`tor.region`),
`crates/gabbro-check/src/saetze.rs` (C186/N571/N463/M140 sentences),
`X86/Typen.lean`, `Parser/UebersetzeAllg.lean` (`fieldRangeO`/`typAt`/
`declOf`), `dokumente/x86/WORK-ALLOCATION.md` (B1/B2/C1/C2/C5 rows).

## Findings (summary; full evidence in the audit)

Correct within stated claim (no action): `Regionen` ceiling/freshness/
disjointness/`initialisiere` with real positive/negative/joint probes;
`Speicher` read-back/frames; `OverlapRefusal` conservative
unknown-overlap-refuses policy with counterexample-C; `M140`/LG002
int-to-pointer refusals; `tor.region` stub soundness; ceiling-free model's
bounded-loss statement.

Open joints, prioritised as R1-R5: (R1) `reserviere` freshness/disjointness
never cites the gate-contract sentence of `region_zugriff`; (R2) no
`reserviere`/`initialisiere`-to-`Bild`-section wiring; (R3) C1
`TableLayout.lean` missing (no generic carrier-to-region map;
`wortTraeger` is a witness, not a rule); (R4) target-side `Zugriffe.zugriff`
completeness against `AccessList` unproved; (R5) certified region
end-to-end program blocked on OFFEN O37. Explicit non-tasks recorded so no
later lane "repairs" a correct helper.

`natAdresse` reviewed: target-internal offset arithmetic, not a language
int-to-pointer path; flagged as a precondition on R1/R3, not a finding.

## Checks

- `./lean-probe grammatik/Grammatik/X86/Regionen.lean`: first line
  `== 0 error(s) in the COMPLETE output; exit 0`; axioms are subsets of
  `[propext, Classical.choice, Quot.sound]` (e.g. `ausricht_monoton`:
  propext + Quot.sound).
- `./lean-bau`: `Build completed successfully (392 jobs).` Whole tree
  green; no Lean change made by this lane, so nothing could have reddened.

## What remains open

The R1-R5 bridge tasks belong to future author lanes (C1 layout, accepted
287 IR interface, image/loader work, TSO bridge), not to this audit.
Full source-to-final-bytes validation remains OPEN. Line numbers in the
audit are as-read and may drift.

## Task-correctness note

Nothing in the task was found to be wrong: the scope (heap ceiling, fresh
disjoint regions, generic layout, proof-free bridge, int-to-pointer
refusals) matches the actual modules, and the "do not invent a bug where
an OPEN bridge is OPEN" instruction was load-bearing (applied to
`Regionen` CUTS, `tor.region` NOT-proved list, O37).
