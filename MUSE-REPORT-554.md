# MUSE-REPORT-554: Shorter, clearer and current English README

Lane 554, 2026-10-01. Clone `/home/simon/Dokumente/gabbro-muse/a554`, branch
`muse/554` verified before any edit. Owned files only: `README.md`,
`dokumente/PROJECT-STATUS.md` (new), `AGENTS.md` (one reference line),
`MUSE-REPORT-554.md` (this file).

## What was done

- Rewrote `README.md`: 358 lines down to 149. Leads with what Gabbro is and
  the goal (user proves application logic plus named hardware assumptions;
  language/model safety generic, multicore with DMA). Keeps: quick start with
  real MSRV 1.86 and `cc`-at-build-time note, working C11 backend, Lean goal
  proof over G/GX with shared-atomic rely, planned direct x86 backend with
  `-O3`-like invariant optimisation and OS/freestanding profiles, named
  hardware assumptions vs user logic (no OS/kernel trust), compact
  architecture/status table, runnable quickstart, two-command proof-check
  recipe from the actual `grammatik/NachpruefungZiel.lean` imports (Beweis,
  Proben, ProbenW1, BeweisAtomar), the three-axioms-fidelity explanation,
  real tutorial/example links, and the AI-authorship plus AGPL/addendum close
  with the licence meaning preserved.
- States explicitly that full Rust backend validation, final-byte validation
  and hardware/concurrency correspondence remain OPEN; never calls the compiler
  or a binary verified. Notes Lean X86 helper modules exist but are not the
  complete hardware model. No percentages, no performance promises, no dates
  for completion, no cold build benchmarks (dropped the 2026-09-15 timing
  block and the stale 942-test / 386-of-413 mutation figures).
- New `dokumente/PROJECT-STATUS.md`: evidence doctrine (proved / measured /
  argued / open), register links, proof-history identifiers, limit pointers.
  No second copy of the live numeric ledger.
- `AGENTS.md`: only the §5 reference line changed into a link to the real
  named section `README.md#proved-and-not-proved`. No other AGENTS policy
  touched. `DIRECT-COMPILER.md` untouched. No guardian, Rust or Lean source
  touched.

## Guarded metrics — all refreshed from measurement, none guessed

`pruefe-todo.py readme_muster()` values taken 2026-10-01: 481 diagnostics,
188 EBNF rules, 242/242 terminals, 34 templates of which 23 machine-checked,
56 guardians, 157 clean examples, 856 poison files, blind spots
73/175/24/12 of 285 pairs, 15 theories with 3512 Isar lines. Added the two
previously unhit guarded wordings with measured values: usability
`**may fall** — 2431 and 110 clause sites` (312 of 2431 teaching, 14 of 110
real-code, from `zaehle-zeremonie.py`) and `**75 of 89 instruments carry all
five requirements**` (from `pruefe-waechter.py`). Kept the guarded mutation
wording with the freshly measured anchor total (`damage one rule at a time:
422 mutations`, from `mutiere-pruefer.py --anker` output
`== 33 von 422 Ankern greifen ins Leere ==`).

## Checks run (this clone, docs-only, no Lean build)

- `git diff --check`: clean.
- Local markdown link check over README/PROJECT-STATUS/AGENTS: all resolve,
  including `dokumente/x86/TARGET-PORTABILITY.md`.
- `python3 instrumente/pruefe-todo.py`: README section now
  `Kennzahlentafel deckt sich mit dem Gegenstand` (was 6 stale figures);
  speech tests Gift/Sauber/EN all ok.
- `python3 instrumente/pruefe-zahlen.py`: the four previously blind README
  patterns (2 ceremony, 2 instruments) now hit; the only remaining README
  entry is the pre-existing tool-side failure `Mutationen im Katalog —
  der Befehl druckt die Zahl nicht mehr (... --anker) — der Suchweg ist ab`,
  which fails identically on master and is out of this lane's scope
  (guardians must not be edited). Other `pruefe-zahlen.py` findings
  (KENNZAHLEN, ZEREMONIE, SONDENDECKUNG staleness) are pre-existing baseline
  failures in files this lane does not own — reported, not hidden.
- No `cargo`/`lake` invoked directly; guardians ran directly per HARD RULES
  (their internal measuring subprocesses are the guardians' own).

## Repair after independent review (lane 555, verdict REPAIR)

The review found one blocking defect: the rewrite dropped numbered `## N.`
sections, leaving the five out-of-scope `README §5` references dangling
(`LICENSE-ADDENDUM.md:51`, `dokumente/DESIGN.md:124`,
`dokumente/GABBRO-ATS-SPARK.md:12,156`,
`dokumente/AUFTRAG-GABBROV-VERIFIKATION.md:110`). Accepted without dispute.
Fixed by numbering the sections 1–6 with the proof boundary as
`## 5. Proved and not proved` (own wording kept, `5.` prefix added);
`## 6. Documents` follows. Internal README link and the `AGENTS.md` link now
point at `#5-proved-and-not-proved` (GitHub slug of the new heading).
No figure, claim or link target otherwise changed; line count stays 149.
Re-ran `python3 instrumente/pruefe-todo.py` after the fix: README section
still `Kennzahlentafel deckt sich mit dem Gegenstand`, speech tests ok.
The `TODO.md` stale figure remains as reported (not owned).

## What remains open / notes for the merger

- `TODO.md` has one pre-existing stale figure (`unbewachte fettgedruckte
  Zahlen steht als 152, heute 153`) — not owned by this lane.
- The over-long `lake build` recipe line (four modules) is one line; kept
  exact module names over short lines.
- `gabbro build beispiele/172-prozess-ohne-libc.bau` in the quickstart uses a
  real committed `.bau`; no build was executed in this lane (docs-only).
