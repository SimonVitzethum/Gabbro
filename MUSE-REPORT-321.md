# MUSE-REPORT-321: Independent review of the central direct-compiler progress document

Lane 321 (review). Branch `muse/321`. Model: opencode-go/muse-spark-1.3-contributor.
No delegation, no model calls. Owned file only: this report. No source file modified.

## Reviewed candidate

- BASE commit: `1990abb2b651a634f5415dc9af67a85ea5e38c95`
- Document blob: `git rev-parse HEAD:dokumente/DIREKTER-COMPILER.md`
  = `ea10465dd8060a4668db568ee3c9174e50b1868b`
- Scope: `dokumente/DIREKTER-COMPILER.md` (209 lines) as a work/progress
  document only. Not a review of any Lean proof or Rust code.

## What was checked

1. Intended result section: direct x86-64 machine bytes incl. linking,
   relocations, entries, runtime; Lean-first then Rust; Rust output as
   untrusted evidence; end condition generic full source-to-final-byte
   validation for every admitted program; explicit non-claims (no
   validated executable yet, no per-example rules, mnemonic list /
   round-trip / isolated helper / assumed simulation do not suffice).
2. Optimisation section: `-O3`-like scope plus invariant-derived rules;
   preservation list covers values, faults, memory observations, IEEE,
   control state, contracts, call logs, concurrency, progress, budget/time;
   source/target/hardware timing kept separate; SIMD refused where unproved;
   no GCC/Clang `-O3` equivalence claimed; no guarantee weakened.
3. Sequence/closure section: 9-step Lean-first order; W/GX and `gabbro_ziel`
   named as existing source framework with the target refinement still
   required; tearing/LOCK/fences/retries/access-grouping listed as proved
   correspondence still needed; enabledness not fairness; OS/runtime/binding
   as user logic, only silicon/device/timing as hardware assumptions; all
   executed support bytes covered; lane 280 stopped with draft retained;
   whole chain OPEN.
4. Workflow section: 20-process cap matches snapshot manifest
   (`max_active: 20`); exact-candidate ACCEPT with green build and
   `propext, Classical.choice, Quot.sound`; non-degenerate witnesses;
   coordinator fallback and no automatic acceptance. Consistent with
   `.tmp/COORDINATOR-SNAPSHOT.json` states and peer-review mapping.
5. Ledger rows vs snapshot states: every row marked "Merged after
   review/checks" has its merge commit present in this base (all 29
   cited short hashes resolve via `git cat-file`) and its evidence
   report present under `messung/muse/` (all 29 checked present).
   Rows marked candidate/working/waiting (279/297, 287, 288, 290/306,
   291/307, 309/310/313/314, 311/315, 312/316, 317/318, 319/320, 280)
   match snapshot statuses; none is claimed merged. Task files
   `lanes/279,290,291,309,310,311,312,317,319.md` exist.
6. Historical numbers: 1468 passed / 0 failed / 1 ignored Rust suite and
   338/338 + 53 comparisons + 2 reverse probes trace to
   `dokumente/x86/WELLE-A.md` and `messung/muse/MUSE-REPORT-273.md`;
   the document labels them historical foundation regression, explicitly
   not a source-to-x86 validation result, with fresh whole-tree checks
   pending. No stale number is presented as current validation.
7. Lean module coverage in this base: `grammatik/Grammatik/X86/` holds 10
   modules (Typen, Wort, Ganzzahl, FlagBeweis, Speicher, SpeicherKommutation,
   Ausfuehrung, TSO, Bild, Gleitprofil); each carries a `CUTS:` block;
   `grep` finds no `sorry`/`admit`/`axiom` outside comments. The document
   claims only reviewed helpers with retained CUTS, never a complete
   compiler or closed chain.
8. Links: README lines 16-22, TODO section 2, AGENTS.md section 3 all
   point at the document with matching scope language ("not implemented",
   "no complete chain closed", "central record"). No contradiction found.

## New definitions/theorems

None. Documentation review; no Lean or Rust work done.

## Build result

`./lean-bau` not run: the task forbids gratuitous full builds for a
documentation review and no source file was touched, so no build state
could change. Working tree is clean except this report.

## Observations (not defects)

- Ledger refresh stamp is 2026-10-01 09:25 UTC; snapshot shows lanes 309
  and 310 became `report_ready` at 09:27/09:29, after the stamp. The rows
  say "Agent working", which understates rather than overstates progress.
- Snapshot records lane 307 (review of 291) as `report_ready` with a Lean
  merge-build integration failure. The 291 row says "Committed candidate;
  review/integration pending", which remains literally true (not merged),
  but the coordinator will want the repair loop, not this document, to
  carry that failure detail.

## Remaining open work

The whole source-to-final-byte acceptance theorem; IR/lowering (287),
invariant optimisation (288), stack/ABI (309), call-log (310), strength
reduction (311), regions/ceiling (312), access extraction (317),
fetch/decode/step (319); pending reviews 297, 306, 307 (repair), 313-316,
318, 320; Rust implementation after reviewed Lean models; fresh
whole-tree checks for the publication containing this document.

## Verdict

The candidate document accurately describes the bounded work and progress
at this base. It keeps planned, working, pending and merged states
distinct, bounds independent ACCEPT to exact delivered claims, reuses
cited historical measurements without promoting them, and claims no
complete compiler or full source-to-binary proof.

DOCUMENT-CANDIDATE: ea10465dd8060a4668db568ee3c9174e50b1868b
VERDICT: ACCEPT
