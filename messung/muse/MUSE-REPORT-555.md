# MUSE-REPORT-555: Independent exact-candidate review of 554 (concise README)

Lane 555, 2026-10-01. Clone `/home/simon/Dokumente/gabbro-muse/a555`, branch
`muse/555` verified before any work (re-verified on re-review). Owned file
only: `MUSE-REPORT-555.md` (this file). No Lean, Rust, guardian, or docs
source touched; working tree was clean before and after (`git status --short`
empty, `git diff --check` clean).

CANDIDATE: 554 9c8c9ceeac957e1b76b7f931c7e5564dc17fb49b

VERDICT: ACCEPT

## Round 4: re-review of repaired candidate — all findings closed

Re-reviewed the NEW pinned HEAD (`9c8c9cee`, base `2185a17f`, 5 files incl.
`instrumente/pruefe-zahlen.py`, `clean: true`). The author repaired all three
round-3 defects; each repair verified against the real definitions below.
Method: full read of new README (150 lines), PROJECT-STATUS (75 lines),
PATCH hunks, BUILD-EVIDENCE (11 entries); regex checks of every guardian
pattern against the candidate texts; tree-level corroboration of the chain
scope; `py_compile` of the edited guardian. No Lean/cargo builds run
(review-only lane); heavy live instruments not re-run (see caveats).

**1. Intro now states the boundary honestly.** Duty is `NutzerPflichtA`
(bodies at every budget, every shared-atomic-read value, plus start duties);
OS-as-user-logic is "the direction", while "loader, runtime thread creation
and foreign behaviour are still named assumed premises (c)/(d), their
correspondence unproved". Matches `Spec.lean` header 18–21 (duty),
868–885 ((c) foreign code), 896–898 (loader), 934ff/949 (thread creation),
70–80 (unproved correspondence). The `LogikPflicht` misattribution and the
"never assumed / checked implementations" overclaims are gone.

**2. Instrument sentence now truthful, guardian edit minimal and safe.**
README cell: "**75 of 89 instruments carry the four static requirements**
(work quantity is measured per run)". PATCH changes exactly the two
README-side regexes (`pruefe-zahlen.py` hunk @@ -445,14 +445,14); commands,
tool-side `vier STATISCHEN` patterns, descriptions, figures (75/89) and
entry structure intact; edited file compiles; new patterns hit the new text
(75, 89); legacy "all five" needed no retention — the only other occurrences
are dated history in `messung/` files no entry reads, and no other
`pruefe-zahlen.py` pattern depends on that wording.

**3. Printed-line table now describes only printed output.** The
`schlusssatz`/`kette_104/108`/K124 row is deleted from README; C evidence
sits at `dokumente/PROJECT-STATUS.md#translation-chain` (anchor verified).
Its content is tree-corroborated: CHAIN-INSTANCE markers for 104, 108;
CHAIN-GENERIC for 130, 69, 73 (2 + 3 = 5 instances); population
`beispiele/*.gab` = 157 files; concurrent-124 record exists
(`Schlusssatz124`/`Korpus124` stage (b) per §8 register).

**Kept from before:** `## 5. Proved and not proved` retained (all five
external §5 references still resolve); 150 lines, in band; every local link
resolves post-merge (the two PROJECT-STATUS misses are the new file itself);
only the 5 owned files touched; AGENTS diff still one reference line.

**Caveats (honest, non-blocking):** the "5 of 157 CLOSED on 2026-10-01"
figure is the author's dated live `zaehle-kette.py --lean` figure —
structurally corroborated (5 markers, 157 population) but not independently
re-measured here; the merger re-measures all figures at merge time per
policy. BUILD-EVIDENCE lists no explicit command lines for the claimed
`pruefe-todo`/`pruefe-zahlen`/`zaehle-kette` re-runs; my independent
pattern-level checks (all 17 `readme_muster` + all 5+2 README `zahlen`
patterns hit with the recorded values) cover the README side of those
claims. Pre-existing out-of-scope baseline findings (tool-side mutation
entry, TODO/KENNZAHLEN staleness) unchanged and still not this lane's.

## Round 3: coordinator factual questions — three real defects, precise repairs

Re-reviewed the pinned candidate (`c910e94b`, unchanged) against real
definitions. All three coordinator concerns are REAL; regexes matching the
numbers does not save them. Evidence below is quoted from this clone, which
is at the candidate's base for these files (candidate touches none of them).

**1. Intro overclaims the proof boundary (README lines 12–16) — REAL.**
The intro says the user owes "the application logic (`LogikPflicht`, at every
budget, against every value a shared atomic read may return)" and "OS,
runtimes, thread startup and locks are never trusted or assumed — they are
user/binding logic with checked contracts and implementations."
`grammatik/Grammatik/Zielsatz/Spec.lean` says otherwise:
- The duty is `NutzerPflichtA E` (header lines 18–21): bodies at every budget
  AND against every shared-atomic-read value, which is `LogikPflichtA`, "the
  rely; on a unit without one it is `LogikPflicht`" — plus `StartPflicht`.
  Attributing the rely clause to `LogikPflicht` names the wrong obligation
  (on atomic units the two are not equivalent: `hP_rely_nicht`, lines
  110–117). Use `NutzerPflichtA`/`LogikPflichtA` or plain language.
- "Never assumed" is false: (c) `GutO O` assumes every foreign body
  (`extern fn`, `prim fn`, `asm`, `entry`, `entrust`) writes only its declared
  frame and keeps held locks — "Foreign code is not Gabbro code: nothing in
  the language can check it" (lines 868–871); (c) `AxVertragO` assumes every
  fitting axiom answer meets its declared `ensures` — "the contract of
  foreign code or a device, which the user writes and nothing checks" (lines
  883–885); (d) `Laufzeit.lader` assumes the loader establishes `E.sp0` — "A
  toolchain/loader fact" (lines 896–898); (d) `Laufzeit.start`/`.einmal`
  assumes the runtime starts exactly the declared starts and run-time thread
  creation (lines 934ff, 949). Loader, runtime thread startup and foreign
  code ARE assumed premises.
- "Already have checked implementations" conflates checked contracts with
  proved implementation correspondence. Contracts are checker-checked, but
  the header's STILL TRUSTED/NOT CLAIMED list (lines 70–80) names as
  unproved: the exporter is unverified; G-being-the-meaning-of-emitted-C is
  an assumption except chain-instances 104/108 (`zaehle-kette.py --lean`
  measures 2 of 129 CLOSED); C forms stand 51 lemma / 4 assumption / 27 no
  semantics. Runtime/OS implementation correspondence is not proved;
  source-to-byte closure is OPEN.
Repair: rewrite the intro paragraph to separate intended architecture (OS
as user/binding logic with declared contracts — Simon's 2026-09-30
requirement, a direction, not a boundary) from the present proof boundary
(loader, runtime thread creation and foreign behavior are named assumed
premises (c)/(d); their implementations' correspondence is unproved), and
fix the duty name. Keep it to the same ~7 lines; no new claims.

**2. `75 of 89 instruments carry all five requirements` is false — REAL.**
`instrumente/pruefe-waechter.py:1524` prints `== N von M tragen die vier
STATISCHEN ==`, and lines 1525–1528 state "Es sind seit dem 2026-08-31
FUENF … Der Wortlaut `vier` bleibt, weil `pruefe-zahlen.py` diese Zeile
woertlich nachrechnet". `statisch()` (lines 739–760) checks only the static
source-text requirements; the fifth family — work quantity beside the
verdict (W17) — "steht in der Ausgabe und nicht im Quelltext … wird in
`--lauf` gemessen, sonst gar nicht" (lines 1529–1530). The 75/89 figure
counts the FOUR STATIC requirements, and the README presents it as "all
five". The tool-side `pruefe-zahlen.py` patterns already say "vier
STATISCHEN" (lines 450, 457) while the two README-side patterns say "all
five" (lines 448, 455) — the unfaithfulness is baked into the register.
Repair (author 554 is authorised for exactly this narrow edit):
- README status-table cell: truthful wording, e.g. "**75 of 89 instruments
  carry the four static requirements**" (keep figures; one clause noting
  the fifth — work quantity — is measured per run, not statically, if it
  fits one line; do not relitigate the guardian cell's five-attribute list).
- `instrumente/pruefe-zahlen.py` lines 447–459: update ONLY the two
  README-side regexes to the new truthful wording (patterns BEFORE the
  text); keep both entries' commands (`pruefe-waechter.py`), tool-side
  patterns, captured figures (75 and 89), mismatch-vs-missing-hit behavior
  and poison/clean coverage intact; no other entry touched, no guard
  deleted, no diagnostic masked. Stale baseline ledgers elsewhere are out
  of scope and stay as they are.

**3. `Printed line` table describes output the recipe never prints — REAL.**
`grammatik/NachpruefungZiel.lean` (22 lines: imports Beweis, Proben,
ProbenW1, BeweisAtomar; `#check`/`#print axioms` for `GabbroZiel`,
`gabbro_ziel`, `gabbro_ziel_sc`, `gabbro_ziel_sc_aus`,
`gabbro_ziel_verbund`, `gabbro_ziel_verbund_sc_aus`, `gabbro_ziel_zeuge`,
`probeA/probeD_widerlegt_gilt`, `w1_abgelehnt`) prints NO `schlusssatz`,
`kette_104/108` or K124 lines. The candidate table row 71
("`schlusssatz…`, `kette_104/108…`, `K124…` | existing C-backend translation
validation …") therefore documents lines the two-command recipe cannot
produce — a reader running it will wait for lines that never come.
Repair: delete that row from the `Printed line` table (the table must only
describe what the recipe prints) and, if one line fits without repetition,
point the C-backend evidence at the provenance page
(`dokumente/PROJECT-STATUS.md`, which should name the actual chain:
generic closing theorem, instances 104/108, concurrent 124, with the
2-of-129-closed scope from `zaehle-kette.py --lean`; no new numbers beyond
what the instruments print).

The round-2 §5 repair remains necessary and is kept; it is not sufficient.
No new test results are claimed: guardian outputs cited above are the
tools' own printed words and my earlier pattern-hit checks, re-confirmed
on the pinned text. No Lean or cargo build run (review-only lane).

## Re-review after author repair (new pinned HEAD)

The previous verdict (REPAIR on `679e4868`, committed as `6d56709f`) found one
blocking defect: the rewrite dropped numbered `## N.` sections, leaving the
five out-of-scope `README §5` references dangling (`LICENSE-ADDENDUM.md:51`,
`dokumente/DESIGN.md:124`, `dokumente/GABBRO-ATS-SPARK.md:12,156`,
`dokumente/AUFTRAG-GABBROV-VERIFIKATION.md:110`). The author accepted without
dispute and repaired in commit `c910e94b` ("numbered README sections so §5
resolves again"), now the pinned HEAD of `.tmp/review/SNAPSHOT.json`
(base `2185a17f`, same 4 files, `clean: true`).

Independently re-verified on the NEW candidate text:

- `## 5. Proved and not proved` exists (sections numbered 1–6, earlier
  sections 1–4 per the lane requirement); all five external `README §5`
  references resolve to the proof-boundary section again. GitHub anchor
  `#5-proved-and-not-proved` is the correct slug; the internal README link
  (line 22) and the `AGENTS.md` link (line 52) both point at it.
- Repair diff is minimal: `PATCH.diff` touches only the 4 owned files
  (`AGENTS.md`, `MUSE-REPORT-554.md`, `README.md`,
  `dokumente/PROJECT-STATUS.md`); README still 149 lines (in the 100–150
  band); all guarded figure wordings byte-identical to the reviewed version.
- All 17 `readme_muster()` patterns re-matched against the new README text:
  none missing. The 5 `pruefe-zahlen.py` README patterns re-matched: none
  missing. Author's BUILD-EVIDENCE re-run claim (`pruefe-todo.py`: README
  section still `Kennzahlentafel deckt sich mit dem Gegenstand`, speech
  tests ok) is consistent with these pattern hits; heading renumbering
  cannot move any guarded figure line.
- No new claims, figures, links, or licence wording introduced by the repair;
  nothing else in the candidate changed. Round-1 findings below therefore
  stand unchanged, with the single blocking defect now closed.

## Round-1 review (HEAD `679e4868`) — retained as history

## What was reviewed

Exact candidate from `.tmp/review/SNAPSHOT.json` (author 554, head pinned above,
base `2185a17f`, files `AGENTS.md`, `MUSE-REPORT-554.md`, `README.md`,
`dokumente/PROJECT-STATUS.md`), against author task
`.tmp/review/author-554/OWNER-TASK.md` and the review criteria in my lane task.
Candidate texts read in full: `README.md` (149 lines), `PROJECT-STATUS.md`
(63 lines), `AGENTS.md` reference line, `MUSE-REPORT-554.md`, `PATCH.diff`
headers, `BUILD-EVIDENCE.json`.

## Independent checks run (this clone, review-only, no Lean/cargo builds)

- `git status --short`: clean; `git diff --check`: clean (nothing to check, no edits).
- All 17 `readme_muster()` patterns from `instrumente/pruefe-todo.py` matched
  against the candidate README text: Compiler `12 passes` / `9 carried`,
  `481 diagnostics`, `188 EBNF rules`, `242 / 242` terminals, `34` templates of
  which `23 machine-checked`, `56 Guardians`, `157 clean examples`,
  `856 poison files`, blind `73 / 175 / 24 / 12 (of 285 pairs)`, `15 theories`,
  `hold 3512 lines of Isar`. All hit; values cross-checked where cheaply
  countable: `beweise/*.thy` = 15 files / 3512 lines, `beispiele/*.gab` = 157,
  `beispiele/gift/*.gab` = 856, `instrumente/pruefe-*` = 56. Match.
- All 5 `pruefe-zahlen.py` README patterns matched against candidate text:
  `may fall — 2431 and 110 clause sites` (both), `75 of 89 instruments carry
  all five requirements` (both), `damage one rule at a time: 422 mutations`.
  The 4 previously blind patterns (2 ceremony, 2 instruments) now hit, as the
  author claims. The 5th (mutations) hits as wording; its *measurement* leg
  (`mutiere-pruefer.py --anker` parse) fails tool-side on master too
  (`der Suchweg ist ab`), honestly reported by the author as pre-existing and
  out of scope. Agreed: not a candidate defect.
- `python3 instrumente/pruefe-todo.py` and `python3 instrumente/pruefe-zahlen.py`
  run on BASE (this clone, without candidate applied) to establish the baseline:
  base README has 6 stale figures; base pruefe-zahlen shows the 4 pattern-miss
  README findings the candidate fixes plus the 1 pre-existing tool-side
  mutation failure. Consistent with the author's report; no wider hidden
  README regression claimed.
- Local markdown link audit over candidate README / PROJECT-STATUS / AGENTS:
  every link resolves post-merge (`Spec.lean`, `DIRECT-COMPILER.md`,
  `DIRECT-COMPILER-DESIGN.md`, `grammatik/OPTIMIZER.md`,
  `dokumente/x86/TARGET-PORTABILITY.md`, `TUTORIAL.md`, `TODO.md`, `REGISTER.txt`,
  `FRAGMENTE.md`, `LICENSE`, `LICENSE-ADDENDUM.md`, `beweise/`). The only
  misses against the base tree are `dokumente/PROJECT-STATUS.md` links, which
  resolve post-merge since that file ships in the candidate. No invented
  syntax, no external URLs beyond the repo + `leanprover/elan` + GitHub clone.
- Proof-recipe check: candidate's two-command recipe
  (`lake build …Beweis …Proben …ProbenW1 …BeweisAtomar`, then
  `lake env lean NachpruefungZiel.lean`) matches the actual imports of
  `grammatik/NachpruefungZiel.lean` (Beweis, Proben, ProbenW1, BeweisAtomar)
  exactly. Axiom table (`propext, Classical.choice, Quot.sound`, sorryAx warning,
  witness/probe/C-chain rows) and the fidelity disclaimer are accurate.
- Truth spot-checks: `DIRECT-COMPILER.md` confirms implementation and full
  validation chain OPEN with designs as requirements (no validated-x86-binary
  claim in candidate — correct); `grammatik/Grammatik/X86/` helper modules
  exist (candidate does not call them a complete model — correct);
  `beispiele/172-prozess-ohne-libc.bau` and `beispiele/01-tabelle.gab` exist;
  `f64::next_up/next_down` used in `m1.rs`/`typen.rs` (MSRV 1.86 plausible);
  licence close matches `LICENSE-ADDENDUM.md` meaning (AGPL-3.0, own program /
  generated C / binaries under any licence, notice condition only on
  verified/secure claims). No percentages, no performance promises, no
  completion dates, no cold-cache benchmarks. OS/runtimes/locks stated as
  user/binding logic, never hardware assumptions. `GabbroZiel` location
  (`BeweisAtomar.lean`, `gabbro_ziel`), GX/G/W reuse and open x86-TSO bridge
  consistent with AGENTS §1 and DIRECT-COMPILER record.

## Why REPAIR (single blocking defect)

The candidate drops all numbered `## N.` sections. Its headings are `Quick
start`, `Proof check in two commands`, `How the guarantee is meant to work`,
`Status`, `Proved and not proved`, `Documents` — there is no `§5` anywhere.

But `LICENSE-ADDENDUM.md:51` (`README.md §5 states exactly that`), plus
`dokumente/DESIGN.md:124` (`gabbro_ziel`, README §5), `dokumente/GABBRO-ATS-SPARK.md:12,156`,
`dokumente/AUFTRAG-GABBROV-VERIFIKATION.md:110` (README §5) and the current
`AGENTS.md` §1 contract all point at README §5 for the proof boundary. After
this merge every one of those references dangles: the boundary section exists
(`Proved and not proved`) but is unnumbered and unreachable as "§5".

My lane task makes this an explicit repair trigger: retain a concise `## 5.`
proof-boundary heading (with earlier sections numbered 1–4) so licence and
design references stay true, and require repair if renumbering leaves them
pointing at the wrong section. The author's `AGENTS.md` change (link to
`#proved-and-not-proved`) repairs only the one in-repo reference the lane
owned; it cannot fix the licence addendum or the design documents, which the
lane correctly did not touch.

Requested repair (small, no licence or unrelated-doc changes): number the
candidate's `##` sections so the proof-boundary section is `## 5. …`
(prefer `## 5. Verification status` per my task, or keep the author's
`Proved and not proved` wording with the `5.` prefix), number the earlier
sections 1–4, and point the `AGENTS.md` link at the resulting anchor. Then
`README.md §5` resolves again everywhere.

## Everything else: accept-quality (no second defect found)

Conciseness (149 lines, in the 100–150 band), readability, backend-vs-plan
honesty, atomic-goal/model-boundary accuracy, quickstart executability,
licence/transparency fidelity, guardian coverage with no weakened or bypassed
patterns, and PROJECT-STATUS.md as provenance-without-duplicate-ledger all
pass. The `152 vs 149` line-count difference between BUILD-EVIDENCE's `wc -l`
and the snapshot file is immaterial (both in band). No new Lean
definitions/theorems in this review lane; none required. No `./lean-bau`
run: docs-only review, and no build is claimed.

## Open / notes for the repair lane and merger

- Pre-existing, out of scope (author-reported, confirmed on base):
  `pruefe-zahlen.py` tool-side failure `README.md / Mutationen im Katalog …
  der Suchweg ist ab` (also on master); `TODO.md` stale `152 vs 153`
  unguarded-bold figure; other `pruefe-zahlen.py` baseline findings in
  `KENNZAHLEN`/`ZEREMONIE`/`PLAN` files this candidate does not own.
- After the §5 repair, re-run `python3 instrumente/pruefe-todo.py` speech
  tests and the pattern-hit checks above; numbering a heading does not move
  any guarded figure, but the merger re-measures anyway.
