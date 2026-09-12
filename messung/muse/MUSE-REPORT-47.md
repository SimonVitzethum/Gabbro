# MUSE-REPORT-47: SATZKARTE section 6 (wave-1 merges) — docs only, no Lean

Lane 47, branch `muse/47`. No Lean changes: the only modified file is
`dokumente/SATZKARTE.md` (new section 6, +84 lines). No new definitions or
theorems; nothing added to `grammatik/Grammatik.lean`.

## What I did

Added section 6 "What the wave-1 merges established" to `dokumente/SATZKARTE.md`:
one row per merged wave-1 result with exact Lean names and `file:line` citations
(R1 QLeer, R2 BlattGegenbeispiel, R3 VertragOrtB, R4 KetteMehrfadenC, R5–R7 audits
muse/23 F2/F4/F5, R8–R9 audit muse/24 F9/F11, R10 audit muse/26 F7), then a
flag-by-flag verdict for every flag in §§3 and 5 stating whether a merged result
PROVES it (with theorem citation) or it stays a reading of the definitions.

## Verdicts (summary)

- PROVED: §3.1 (`hSeedAll` at entry — instantiated via `qSeedAll_unmoeglich_req/ens`),
  §3.6 + §5 B5 (`hBlattAll` for writing leaves — refuted via
  `hblattall_falsch_schreibend`), §3.5 partially (`hJw`/`hJsf` derived as theorems
  for the two-thread lock-only fragment via `kette_zwei_aus_lauf`; N-thread and
  leaf steps open).
- Stay readings: §3.2 (`hForm`), §3.3 (`hReturn`/`hWatch`), §3.4 (`hGuardEx`),
  §3.7 (`hDeck`), §3.8 (C4/C12 narrowing), §3.9 (`hO`), §3.10 (`hspace`),
  §5 B8 (`hMSep`), §5 B11 (lowering), §5 B12 (C12 scope) — each with the adjacent
  sharpening (if any) named explicitly.
- The audit rows (R5–R10) are checked `./lean-probe` demonstrations under
  `messung/muse-audit/`, not `Grammatik` theorems; the section says so per row so
  no reader mistakes a demo for a library lemma.

## Citation verification

Every `file:line` in section 6 was verified with `grep -n` against the `muse/47`
working tree before writing, including: `QLeer.lean:133/142/154/170`,
`BlattGegenbeispiel.lean:242/262/286`, `VertragOrtB.lean:114/120/137/406/444`,
`KetteMehrfadenC.lean:115/766/879/909`, `InterferenzAllgemein.lean:498/1502/1597/1816`,
`Extraktion.lean:1437/1442/2421/2428/3609/3621/3829/3840`,
`Unterbrechung.lean:103/120`, and the six audit demo files. The section notes that
its line numbers refer to `muse/47` while §§1–5 numbers refer to `muse/16` per the
file header. Correction made during writing: the audit-file F11 demo is an
`example` at `Audit24.lean:107-112`, cited as such (not as a named theorem);
the named F9 demos are `audit_QRequires_unfold` (`:80`) / `audit_QEnsures_unfold` (`:85`).

## Last `./lean-bau` result line

`Build completed successfully (33 jobs).` (Lean untouched; docs-only lane.)

## What remains open

Nothing in this lane: the task asked for no Lean changes and all ten flags plus
B-flags have verdicts. Open work belongs to the cited lanes' own CUTS
(two-thread → N-thread chain discharge, contract-at-place wiring into the goal
theorem, `hBlattCall` replacement premise).

## Anything in the task I believe is wrong

Nothing material. One scoping note: the task lists "the HIGH audit findings
(muse/23 F2, F4, F5; muse/24 F9, F11; muse/26 F7)". I treated muse/24 F9 as HIGH
per MUSE-REPORT-24 (it is marked HIGH there); muse/23 F5's filed theorem is
`hinv_aus_disziplin` with `interferenceFree_wo_frei` as the affected consumer —
both are cited in row R7.
