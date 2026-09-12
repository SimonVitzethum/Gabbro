# MUSE-REPORT-89 — guardian consolidation (lane 89)

Python + docs lane. No Lean changes, no Rust changes. Seven lane commits on
`muse/89` (pieces 1-6 plus this report as piece 7), then the master merge
below as a separate commit.

## Result table: guardian, before, after, cause, action

| Guardian | Before | After | Cause (measured) | Action |
|---|---|---|---|---|
| `pruefe-emission.sh` st.9 | `beispiele/` 73 vs 70; `messung/*/` 132 vs 73; gift 8 vs 2; sonst 8 vs 1; reverse 2 vs 4 | exit 0, all six marks hold | 3 new clean examples (71/72/73); 59 new emitting messung probes (emission-140..155, absenkung, singles), all compiling under cc+clang; 6 new hint probes reaching the emitter; 7 tracked files under `Claude outputs/`; N041 (lane 73) now refuses 2 entry probes at the checker | Re-booked 70→73, 73→132, 2→8, 1→8, 4→2, each with dated reason at the mark. F-EMIT-1 reported (stale `-- erwartet: cc` headers on the 2 caught probes) |
| `pruefe-saetze.py` | green (55 without sentence = mark) | exit 0, unchanged | — | None (verified) |
| `pruefe-vergabe.py` | 22 vs 20; 77 vs 68 | exit 0 | New candidates `W003` (lane C) and `P008` (lane 60), measured by diffing `--liste` against `d3d9ff4`; 9 correct new probes on old ambiguities (706/707, 720/729/759, 728, 783, 799/800); 671/672 renumbered to 673/674 | Re-booked 20→22, 68→77 with dated reasons |
| `zaehle-gifttreffer.py` | verdeckt 19 vs 8 | ALL PASS (458 clean, 0 FEHLT) | 3 old probes under new rules (141/H020, 150/H022, 220/H021); 8 new probes under known cover (724/725/726, 728, 740, 758/776/777). `411` healed to clean, not lifted past | Re-booked 8→19; 11 new rows in `GIFT-GEGEN-ZUSAGE.md` §10 (heading frozen for `pruefe-zahlen.py`) |
| `pruefe-grammatiktafel.py` | UNGEDECKT abi/errors; mark 1 vs 0 | exit 1, mark fixed | `deadline` gained lane-59 carriers (mark 1→0, as ordered). `abi`/`errors` are lane-S1 syscall-surface terminals: no lowering, no refusal text names them | Mark booked; F-TAFEL-1 reported (needs checker/emitter S5–S7; no identifier-gaming) |
| `pruefe-englisch.py` | comments 7905 vs 7881; instruments 1085 vs 1069; sink 1 vs 0 | exit 1, no RATSCHE lines | Per-file delta vs booking commit: H/C/sugar lanes (+24), new `pruefe-gestalt.py` (+13 of +16); sink is the real bilingual-policy flag `--proved\|--mit-beweis` (tested, `fahnen.rs:201`) | Re-booked 7881→7905, 1069→1085 (English-only notes, own count steady at 20), 0→1 as policy debt. F-ENG-1 reported (no green state exists for a booked sink hit; rename breaks policy, exception is owner call) |
| `pruefe-zahlen.py` | 22 BEFUND lines | exit 2, 3 findings | 19 figures re-measured and re-booked (table below); 3 search paths dead (F-ZAHL-1/2/3) | 19 doc numbers updated; F-ZAHL-1..4 reported |
| `pruefe-widerruf.py` | ALL PASS | exit 0, unchanged | — | None (verified) |
| `pruefe-todo.py` | README 5, TODO 7 (counted 12) | exit 1, 3 lines | All README/DONE/TODO digits fixed; remaining 3 are `heute ?` collateral of the zahlen abort | Fixed; collateral reported under F-ZAHL-1/2/3 |

Re-booked doc figures (19): codes 295→305, sentences 111→119 (PASSREGISTER),
ceremony 1376→1404 (×2: README + ZEREMONIE) and 88→92, instruments 64→65 and
65→66, checker comments 7892→7905, ambiguous probes 73→77, examples 71→73 (×2:
README head + table), gift 550→556 (README + DONE), EBNF 163→165 (×2: rule +
today-bracket), sentences-over-passes 111→119, foreign bodies 117→120,
carrying 132→139, unclear 108→107, continuations 3733→4017, widerruf files
299→377, map looks 47→49, unqualified 42→44, abort-capable guardians 60→61
(of 65→66), exit sites 369→376.

## Findings (named, not fixed — out of lane scope)

- **F-EMIT-1** (stale probe headers): `messung/proben/probe-eintritt-privat.gab`
  and `probe-eintritt-zwei.gab` still read `-- erwartet: cc` but fall at the
  checker with `N041` since lane 73. Owning lane: re-head them.
- **F-TAFEL-1** (uncoverable terminals): `abi`, `errors` (SYNTAX.md §12.1,
  lane S1) have no lowering and no refusal text names them (`P042` names only
  the `syscall` item). Coverage needs S5–S7. I did not game it with
  identifier-occurrences.
- **F-ENG-1** (booked sink hit): `--mit-beweis` in `hilfe()` text
  (`crates/gabbro-cli/src/main.rs:768`, counted at `:713`). Real flag, tested,
  bilingual policy (`--unit|--einheit`, `--model|--modell`). This guardian has
  no green state for a booked sink hit (any hit returns 1); rename breaks
  policy, a flag-name exception is an owner call. Already analysed the same
  way in MUSE-REPORT-67.
- **F-ZAHL-1/2** (dead `--anker` path): `./instrumente/mutiere-pruefer.py
  --anker` aborts in its own `baumstand()` speech test in this environment and
  never prints `== N von M Ankern greifen`. Root cause measured: `$TMPDIR`
  points inside the repo (`.tmp/`), so `tempfile.TemporaryDirectory()`
  isolation fails — `git status` finds the parent repo and the
  Nicht-Repository probe reads `sauber` instead of `unbekannt`. Re-ran with a
  private scratch dir outside the repo: the tool proceeds. Fix belongs to the
  tool (e.g. `GIT_CEILING_DIRECTORIES`) or the environment, not this lane.
  (Deeper state seen on the way past: the anchor catalog itself reports dead
  anchors — the mutation lane's business, not the register's.)
- **F-ZAHL-3** (dead klauseln path): `pruefe-klauseln.py` prints no
  `ZUSAGE <n>` summary line, so the `ZUSAGE-Klauseln ohne Leser` entry
  (PLAN.md books 0, reached) cannot be recomputed. Owner: re-add a
  machine-readable line or retire the entry.
- **F-ZAHL-4** (probe weakness, guardian design): `pruefe-zahlen.py`'s
  perturb-check passes vacuously in a dirty tree — it requires ANY entry to
  report `der Lauf sagt`, not the perturbed one, so a dead search path hides
  behind neighbours' stale figures. My cleanup proved it: the 3 stumm entries
  appeared only after all other figures went green. Owner: require the
  perturbed entry itself to change its verdict.
- **F-TODO-1** (collateral): `pruefe-todo.py`'s 3 remaining lines
  (`Kennzahlen mit Befehl` ×2, `unbewachte Zahlen`, all `heute ?`) are fallout
  of the zahlen abort — the booked 88/88/180 were measured at session start
  and are unaffected by my edits (no EINTRAEGE touched, no unguarded cell
  added/removed). They clear when F-ZAHL-1/2/3 clear.

## Incidents during the work (own mistakes, repaired)

- I first booked the Ruempfe/Saetze chains in shapes the register patterns
  reject (`**~~117~~ 120…`, double `~~110~~ ~~111~~`), breaking 2 entries'
  speech-test audibility. Repaired to pattern-compatible chains; speech test
  back to 91/91.
- I created a git worktree under `$TMPDIR` (inside the repo) for old-vs-new
  comparison; corpus-wide greps (`walk`/`group` counts) doubled. Removed the
  worktree; counts back. Same class as the `.claude/worktrees` exclusion the
  register already carries — `.tmp/` inside the repo is a standing pollution
  vector for every `.`-rooted count, and `mktemp -d` (emission) also lands
  there.

## What I believe is wrong in the task

- Nothing load-bearing. Two notes: (1) `pruefe-saetze.py` and
  `pruefe-widerruf.py` were already green at session start, not red —
  the red list had aged. (2) The emission figures in the task (72/70) had
  already moved to 73/70 by the time I measured; I booked what I measured
  (73), not what the task quoted.

## New definitions/theorems

None — Python + docs lane, no Lean work. No existing theorems touched.

## Build state

- `./lean-bau` last line: `Build completed successfully (50 jobs).`
  (plus `✔ [49/50] Built Grammatik (155ms)`; only axiom-dependency info lines
  above — no Lean files touched by this lane).
- `./emission-pruef`: `== exit 0` (222 of 222 compile, both compilers).
- `./cargo-pruef` was NOT run for the lane work (no Rust changes; binary reused
  from the emission build for read-only `pruefe`/`emit` probes). It WAS run
  once for the master merge (which brought Rust changes): `== exit 0;
  failing tests: 0`. See the merge section below.

## Open / for owning lanes

F-EMIT-1, F-TAFEL-1, F-ENG-1, F-ZAHL-1..4, F-TODO-1 (above). Observed but
unregistered (no guardian covers them, left untouched): README emission
`128 of 128` (now 222 of 222) and `28 run`, README pass register
`94 sentences / 227 codes`, DONE `451 tests · 55 translation units`,
`beispiele/73` header reading `-- 72 --`. (PASSREGISTER `87 measured` from
the old list was resolved by the merge to the measured 112.)

## After master merge (2026-09-12, commit 030a3033)

Reviewer-started merge of master-neu (lane 64 library calls + N057; lanes
85, 81, 82) into `muse/89`; conflicts in `TODO.md` + `PASSREGISTER.md`
resolved by re-measuring on the merged tree with a fresh binary
(`./cargo-pruef`: exit 0, 0 failing tests — run this time because the merge
brought Rust changes). Neither side survived the union:

| Figure | Lane 89 | Master | Merged (measured) |
|---|---|---|---|
| Sentences over passes | 119 | 118 | **120** (`SENTENCES: 120 over 12 passes -- 112 measured, 2 ARGUED, 6 CONJECTURED`) |
| PASSREGISTER measured | 87 | 110 | **112** (`--je-satz` tags) |
| Codes | 305 | 304 | **306** (`pruefe-kennungen.py`) |
| Claimed by a sentence | 250 | 249 | **251** (306 − 55; both sides' rows were stale) |
| Without sentence | 55 | 53 | **55** (Zahn 2 mark already 55 via the merge — green) |
| Gruende tragend | 139 | 139 | **140** (`N057` adds one; lane E1's note kept and extended) |

Follow-up drift from the merged lanes, re-booked with dated reasons in the
same pass: diagnostics 305→306, EBNF rules 165→167 (226 terminals hold),
gift 556→560 (new probes 802–805, N057 lane), continuations 4017→4036,
widerruf files 377→381. The merge also moved the saetze mark 53→55 itself
(`«SS-1» over a tree that already moved` note) — nothing for this lane to do.

Post-merge guardian states: emission exit 0 (all six marks hold — the four
new probes fall at the checker under N057, so no mark moves); vergabe,
gifttreffer (560 files, verdeckt still 19, 0 FEHLT), saetze, gruende exit 0;
tafel still abi/errors (F-TAFEL-1); englisch 7905/1085 hold, still the one
booked sink hit (F-ENG-1); zahlen aborts on exactly F-ZAHL-1/2/3 with zero
stale figures left — the second clean-tree confirmation of F-ZAHL-4;
todo keeps only the 3 `heute ?` collateral lines (F-TODO-1).
`./lean-bau`: `Build completed successfully (53 jobs).`

No guardian file of this lane was touched by the merge (no conflicts there);
all lane marks verified intact after it.
