# MUSE-REPORT-118: repository cleanup (files lane, no Lean, no checker logic)

## What was done

Root now contains exactly the keep-list (`README.md`, `LICENSE`,
`LIZENZ-ZUSATZ.md`, `CLAUDE.md`, `TUTORIAL.md`, `TODO.md`, `DONE.md`,
`Cargo.toml`, `Cargo.lock`, `commit.sh`, `.gitignore`). Five commits on
`muse/118`, each revertable on its own:

1. `7bccf676` — `messung/AUFRAEUMEN-2026-09-12.md`: census of all 83 tracked
   `.py` files (name, whole-tree references, last commit date, grep per row),
   written BEFORE any deletion.
2. `ca6faba3` — `git mv fallen-klassifikation.tsv messung/fallen-klassifikation.tsv`
   plus the 3 live reference fixes (`zaehle-fallen.sh` `D=` path,
   `dokumente/PLAN.md:80` and `dokumente/WERKZEUGKASTEN.md:8` relative links).
   Verified: `zaehle-fallen.sh` prints `n=100`, RC=0.
3. `e3245cfd` — `git mv halde.gab beispiele/halde.gab` (basename kept:
   no number, so no collision with parallel lanes and the `.gab` comments naming
   it stay true). Pre-checked: `gabbro pruefe` 0 errors 0 hints, zeugnis has no
   `UNZUGEORDNET`. Stage-9 marks with decomposed comments: `MARKE_EMIT` 75→77
   (+halde move, +`beispiele/80-bibliothek-erklaert.gab` lane-91 drift named with
   address, house rule: no silent absorption), `MARKE_EMIT_X` 1→0.
4. `dc22276f` — deleted `Claude outputs/` (15 files: 7 emitting scratch copies
   of committed files incl. byte-identical `19-traversierung.gab`, stale
   `.rs`/`.lean` copies, `PLAN.md`, build note, 150 KB `.tgz`). Zero live
   references (`git grep "Claude outputs/"` found only 3 historical doc mentions,
   left standing).
5. `8b5e35bb` — deleted 2 zero-reference scripts: `messung/gabbrov/ziehung.py`
   (one-off blind draw; hardcoded dead worktree path; draw recorded verbatim in
   `GABBROV-AUFTRAG.md` §2.1 without naming the script) and
   `messung/gegenrechnung/rumpflaengen.py` (analyzes a foreign `kernel/` tree
   absent from this repo). 81 of 83 scripts stay.

Stayed deliberately, with evidence: `messungen/` (emission ratchet
`MARKE_EMIT_N=2` + docs), `sonden/` (`SONDEN_MIT_PROGRAMM`, `pruefe-sonden.sh`,
`SONDENDECKUNG.md`), `passlogik/` (137-theorem Lean tree, `PLAN-SICHERHEIT.md`).
Dated measurement logs (`ABNAHME-STELLEN.md`, `REICHWEITE-DER-REGEL.md`,
`WILDCARD-ZWEIGE.md`, `.gab` comments) were NOT rewritten: their quotes were
true at measurement time.

## Verification (before → after, same conditions)

- `./lean-bau` last result line: `== 0 error line(s) in the COMPLETE output`
  (green before and after; this lane touches no Lean).
- `./cargo-pruef`: `== exit 0; failing tests: 0` before and after.
- `./emission-pruef` (full `pruefe-emission.sh`): RC=1 both times, but strictly
  less red — finding lines before: B-FUND (76 vs 75), M-FUND (132 vs 73),
  GIFT-DECKE (8 vs 2), X-WURZEL (8 vs 1), UMG (2 vs 4); after: only M, GIFT, UMG
  with IDENTICAL numbers. My two marks (B=77, X=0) are green.
- Fast `abnahme.py`: before `36 von 63 measured — 23 gruen, 11 ROT, 2 TEILMESSUNG`
  (21 ABBRUCH); after `43 von 63 — 27 gruen, 13 ROT, 3 TEILMESSUNG`. All 11
  pre-existing ROTs byte-identical (modulo durations). The 7 newly measuring
  guardians flipped ABBRUCH→gruen/ROT/TEIL solely because the `cargo-pruef`
  baseline rebuilt the binary at 21:21, before the first mutation (21:25) —
  timeline in `.tmp/*.log` and `git log`. Their findings (manifest register,
  p6 proofs, Lean export) touch files this lane never moved.

## Open / for Simon

- Stage 9 still red on M (132 vs 73), GIFT (8 vs 2), UMG (2 vs 4): multi-lane
  drift from waves 4/5, not mine to book.
- `messung/gabbrov/ziehung.py` is the riskiest deletion (a spent instrument
  whose output survives verbatim in the doc). Revert `8b5e35bb` partially if
  the instrument itself must stay.
- This report sits in the root per rule 9, against the keep-list's "exactly":
  rules 9 and A conflict here; rule 9 (newer, lane-binding) won.

Co-Authored-By: muse-agent-118 <muse-agent-118@noreply.invalid>
