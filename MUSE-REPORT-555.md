# MUSE-REPORT-555: Independent exact-candidate review of 554 (concise README)

Lane 555, 2026-10-01. Clone `/home/simon/Dokumente/gabbro-muse/a555`, branch
`muse/555` verified before any work. Owned file only: `MUSE-REPORT-555.md`
(this file). No Lean, Rust, guardian, or docs source touched; working tree was
clean before and after (`git status --short` empty, `git diff --check` clean).

CANDIDATE: 554 679e4868843560fdd80407fdd4deddd519621c8e

VERDICT: REPAIR

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
