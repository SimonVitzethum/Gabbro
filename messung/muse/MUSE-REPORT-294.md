# Muse report 294 — Independent optimiser and full-binary obligation review

## Isolation

- `pwd`: `/home/simon/Dokumente/gabbro-muse/a294`, toplevel same, branch
  `muse/294`. Match: work proceeded.
- Owned files only: `dokumente/x86/REVIEW-OPT-BINAER.md` (new),
  `MUSE-REPORT-294.md` (this file). No other file touched; `git status`
  before commit must show only these two.
- No network, no push, no `cargo`/`lake` direct calls, no builds (docs-only
  task: "no code or gratuitous builds"). No credentials read. No
  delegation/model launching. No new diagnostic/gift/example/CLI/MARKE
  numbers. No canonical Typen/Spec/goal/emit/central-doc edits. English
  only.

## Task (lane 294, per LEAN-ZUERST.md)

Independently audit reviewed `IR-VALIDIERUNG.md`, `IMAGE-ABI.md`,
`QUELLBRUECKE.md` plus actual Lean source contracts/costs/FP/call-log
semantics. Check all starter families (constant/copy, DCE, CSE, inlining,
allocation, peepholes, LICM, unrolling, SIMD) and extra invariant
optimisations for preservation of values/faults/concurrency/FP/source call
logs/budget timing. Check the final validator binds the entire source unit
plus final relocated decoded executable bytes, runtime/entries/ABI and
loaded mapping; no mnemonic-only or assumed-simulation shortcut. Concrete
counterexample for any unsound admission; distinguish desired schema from
proved implementation.

## What was done

- Read `WELLE-A.md`, `LEAN-ZUERST.md`, `IR-VALIDIERUNG.md` (full),
  `IMAGE-ABI.md` (full), `QUELLBRUECKE.md` (full), `TSO-GX-BRUECKE.md`
  (full, for the concurrency obligations optimiser certificates depend
  on), `EMITTER-INVENTAR.md` (§§1/9/12), `BYTE-PILOT.md`,
  `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5.
- Read Lean ground directly: `X86/Typen.lean` (full, 87 lines),
  `X86/Wort.lean` (header + low-width arithmetic), `X86/Speicher.lean`
  (header + permission-checked access), `Budget.lean`
  (`Op.cost`/`totalCost`/`runOps`/within/exceeds + premises P1 and cuts
  C1/C5), `Folge.lean` (`Folge`/`fNach`/`fB`/`FolgeOk`/`FolgeLog`/
  `FolgeG`). Remaining Lean names cited through the lane-274/277 audits
  and labelled as such (Spec legs, Sicht/MaschineW/AtomarW, KostenG,
  Gleitkomma, einpassen).
- Verified tree state at `f4958150`: `X86/` holds only
  Typen/Wort/Speicher; lanes 272/279/282–293 unmerged; the three audited
  docs are merged wave-A designs with review repairs.
- Wrote `dokumente/x86/REVIEW-OPT-BINAER.md`: per-family preservation
  audit (§2), extra invariant-optimisation audit (§3), full-binary
  closure audit (§4), six concrete counterexamples CE-1…CE-6 (§5),
  findings (§6), claim ledger (§7), desired-vs-proved table (§8), CUTS.

## Exact names of new definitions/theorems

None. Docs-only lane: no Lean file added or changed, no theorem, no
definition. Deliverable is the review document
`dokumente/x86/REVIEW-OPT-BINAER.md` (plus this report).

## Results

- **Verdict: no unsound admission found** in the reviewed text. All nine
  starter families plus both cross-cutting obligations refuse every
  unsound instance constructed (CE-1 budget-stop shift, CE-2 fault hoist,
  CE-3/CE-3b publication/visibility crossing, CE-4/CE-4b asm-store and
  in-writer invariant shapes, CE-5 spill fusion/tear, CE-6
  strength-reduction flag/fault change).
- **Two total refusals correctly shaped:** all SIMD validation refused
  until a generic vector-correspondence rule (fault order, visibility,
  tearing, FP control status) is actually proved; budget-exhaustion-stop
  preservation OPEN until a ghost source-budget accounting correspondence
  (or proved separation with transfer) is proved.
- **Full-binary closure correctly stated, unproved:** full-unit binding
  (`E = einheitAllg`, no free metadata), decoded bytes with re-decode
  after patch, whole-image coverage, entries/ABI/loader contract with the
  three-conjunct external-body rule, no mnemonic-only and no
  assumed-simulation shortcut (delivered theorem derives refinement via
  generic `valX86_sound`).
- **Desired vs proved:** only pilot vocabulary + word/memory helpers are
  proved; execution, codec, SCFG, lowering, TSO bridge, image checker,
  FP/time mapping, all optimiser rules, and the closing theorem are
  specified-only (table in review §8).

## Last `./lean-bau` result line

None — no Lean change, no build run (docs-only; baseline untouched).
`git status` scoped to the two owned files; no green-build claim beyond
the untouched baseline.

## What remains open

- Everything in review §8 marked NO (execution, codec, SCFG/certs/rules,
  lowering, TSO bridge, image checker, FP/time, optimiser proofs,
  closing theorem) — owned by lanes 272/279/282–293, not this lane.
- Findings §6 (explicitness, not soundness): (2) name the asm-body
  `lowerOk` refusal in `IR-VALIDIERUNG.md`; (3) cite `Budget.lean` C1/C5
  so the ghost-budget gap is not misread as execution arithmetic;
  (4) cross-reference `N571` for spill-address escape via gates;
  (5) keep the fragment-default scope boundary in status reporting.

## What in the task is believed wrong

Nothing structural. One calibration, stated plainly per HARD RULES 4:
the task asks to "produce concrete counterexample for any unsound
admission" — the audit found no unsound admission in the reviewed text,
so §5 counterexamples are witnesses that the refusals are necessary
(admitted under naive readings, refused under actual clauses), not
evidence of a hole. The report does not inflate this into a finding.
