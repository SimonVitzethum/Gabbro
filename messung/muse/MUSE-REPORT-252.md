# MUSE-REPORT-252 — traverse exit pins, window/exit findings (TODO §-1 wave B; supersedes lane 234)

Lane 252. Scope: `crates/gabbro-check/src/emit.rs` (one doc comment) +
`crates/gabbro-check/tests/traverse_exit.rs` (new, 7 tests) + this report.
No checker, no parser/AST, no Lean, no `MARKE_EMIT*`, no corpus/gift/example
files, no OS surface, no new diagnostic codes, no gift numbers.

## 1. Verification first (the task says "verify, do not assume")

- **Lane 222's "merged AST" is not in this tree.** `parse.rs::traverse()`
  parses `from <start> count <len>` positionally and refuses it with the
  pre-existing `P001` ("the window has no lowering yet"), building no
  `Traverse`. There is no window variant on `Domaene` and no window field
  on `Traverse` in `crates/gabbro-syntax/src/ast.rs` (checked by grep).
  A windowed walk ends at parse; no downstream pass ever sees a window.
  Lane 229's report (§Finding 1) measured the same; this lane re-verified
  it against the current master (`f45974a7`).
- **Lane 229's "exit rule" is not in this tree either.** What merged
  (`e2184405`) is the traverse-*object* read rule (`E010`/`E011` in
  `wirkungen.rs`) plus a doc note in `absenkung.rs` binding the future
  window arm to the `Schleife` statement budget. No exit refusal was built
  (229's report §Finding 2 says why: no probe is expressible). The merge
  message overstates the content; the report is the accurate record.
- **`archive/234` is unreachable from this clone.** The task names
  "branch `archive/234` on origin" — this working copy has no remote and
  no such ref (only `master`, `muse/252`, `ref-csl`, `ref-wip`; `git push`
  and `git remote` are denied in this lane, so it cannot be fetched).
  Nothing below is salvaged from that branch; everything is re-derived
  from the tree and from the 222/227/229 reports. If `archive/234`
  resurfaces at merge, the comparison to run is: S001 negative pins
  (§3, rows 5–6) and early-exit-to-outer-label pins (§3, rows 1–4) against
  its `tests/traverse_exit.rs`.
- **Preamble conflict, same ruling as lane 227 (§5.1).** The wave-5
  preamble ("INDEPENDENT REVIEWER: do not change any existing file")
  contradicts this task's deliverable 1 (work in `emit.rs`, "YOURS until
  it merges"). The task wins; the conflict is recorded here.

## 2. What was built

The exit that is expressible today — `leave`/`next` naming an enclosing
`retry`/`forever` from inside a `traverse` body — already lowers
correctly, and that is now pinned rather than assumed. Three lines hold
it together: the walk body lowers with the incoming `austritt` unchanged
(no label is pushed for a traverse), the `Leave`/`Next` arm emits
`goto <marke>_ende|_weiter` with the locks taken inside released first
(never `break`/`continue` — those would take the walk itself), and
`sprungziele` descends into the walk body so the outer loop emits the
label that is jumped to.

- `crates/gabbro-check/tests/traverse_exit.rs` (new): helpers
  `fehlercodes` (parse + full `pruefe`, error codes) and
  `c_nach_pruefung` (parse + full `pruefe` clean, then `emit` clean —
  every positive row proves a checker-accepted program lowers), headers
  `KOPF` / `KOPF_SPERRE` / `KOPF_BAUM`, and 7 tests:
  - `leave_outer_lands_after_the_loop` — `leave` through a `slots` walk:
    checker silent, `goto arbeit_ende;` before `arbeit_ende: ;` before
    the continuation `return;`.
  - `next_outer_continues_the_outer_pass` — `next` through a `slots`
    walk: `goto arbeit_weiter;` before the in-loop label, and no
    `arbeit_ende:` (a label nobody jumps to must not stand,
    `-Wunused-label` under `-Werror`).
  - `leave_releases_locks_on_the_exit_path` — `locks L` around the exit:
    `L_gib();` immediately (≤2 lines) before the `goto`, label after.
  - `leave_escapes_the_descendant_walk` — `leave` from inside the
    stackless `descendants of` walk: the jump stands in the body (after
    `const uint32_t v = _k…`), the scaffold is intact, the label is
    after the whole walk.
  - `exit_naming_the_traverse_binder_falls` — `leave i` (with an outer
    label in scope) and `next i` (with none) each fall with exactly
    `["S001"]`.
  - `exit_without_any_label_falls` — `leave arbeit` with no label in
    scope falls with exactly `["S001"]`.
  - `windowed_walk_still_has_no_lowering` — `from 0 count 8` still
    refuses with `P001`. Handoff pin for the syntax lane: it goes green
    the day the window lowers instead.
- `crates/gabbro-check/src/emit.rs` (+15, doc comment on `traverse()`
  only, no code): the three-line exit contract above, the test-file
  pointer, and why there is no window arm here (P001 at parse). This is
  the whole `emit.rs` delta — the lowering itself needed no repair.

Deliberately not added: no `pruefe-cformen.py` row — the exit emits only
`goto` / `m_ende: ;` / `m_weiter: ;` / counting-`for`, i.e. the existing
rows `stmt:goto` (`scorr_leave`, `scorr_next`), `stmt:label` and
`stmt:for-counting` (`scorr_traverse`), all lemma-carrying. No silent
form is introduced. No gift files: the positives emit (snippet tests,
which never enter `MARKE_EMIT`), the negatives refuse at existing codes.

## 3. Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full suite, incl. the
  7 new tests; K003 regression caught during development — a `forever`
  function promises `per_pass`, not `costs` — fixed in the probes).
- `./emission-pruef`: `== EMISSION: ALL PASS -- 37 durchgestochen,
  286 von 286 uebersetzen, 2 umgekehrte Probe(n) ==`, exit 0.
- `python3 instrumente/pruefe-cformen.py`: exit 1 with the single
  pre-existing unclassified line (lane-221 `140-atomic-array-counter.gab`
  CAS fragment, same as lane 227 reported); zero count movement.
- `python3 instrumente/pruefe-saetze.py`: exit 0 (ratchet unchanged:
  55 ohne Satz; no new codes, no sentences owed).
- `./lean-bau`: `Build completed successfully (280 jobs)` (no Lean
  inputs changed).
- **MARKE_EMIT delta: 0** on all seven counters
  (123 / 143 / 2 / 1 / 1 / 18 / 0) — untouched, as ordered. No corpus,
  gift, `messung`, `laufzeit` or `programmlogik` file was added.

Rule-13 note (Rust lane): no Lean theorems were added, so no `_zeuge`
is owed. The witness analogue is the positive rows — non-degenerate
programs (a table each function writes inside the walked body,
checker-clean, emitted) — against the refusal pins (S001 × three
shapes, P001 window), the same split lanes 227/229 shipped.

## 4. What remains open / findings (task letter wrong in three places)

**F1 — the subrange lowering is unbuildable in this file set.** Lowering
`from <start> count <len>` needs the bounds to reach the emitter, and
the parser drops them (validates, refuses P001, builds no `Traverse`).
Adding the home means `ast.rs` + `parse.rs` (new `Domaene` variant or
`Traverse` fields — lane 222 §5 recommends
`Domaene::Window{ort,start,len}`) plus fixing every exhaustive
`Domaene` match and the `Traverse` literal in `emit.rs::zaehlstelle`,
i.e. checker files this lane must not touch. Unblock spec for the
syntax lane: carry both bound `Expr`s (never silently a whole-table
walk), lift the P001 refusal, hold start/len against `touches` AND
function effects at lane 229's two walk sites, lower as
`for (i = start; i < start+len; i += 1)` with single evaluation into
temps and clamping, inside the 18-statement `Schleife` budget
`absenkung.rs` already enforces. The C-template half is specified, not
built — building it against fields that do not exist would be dead
code, and this tree does not merge dead code.

**F2 — the traverse-labelled exit needs a grammar slot that does not
exist.** `traverse` has no label position (`SYNTAX.md` §8:
`traverse = "traverse" ident [ "of" expr ] "over" …`, no `[ ident ]`);
`schleifen.rs` registers labels only for `retry`/`forever`. Unblock
spec: optional label on `traverse` mirroring `retry`/`forever`; label
resolution stays S001 in `schleifen.rs`; the invariant-at-exit hold
(inv P at the exit point, continuation assumes at most P plus "first k
visited", never "all visited" — 229 report §deliverable-2.2) belongs
beside `touches` in `wirkungen.rs`; the lowering is a `goto` inside the
same `Schleife` budget.

**On "preserves the loop postcondition at the exit point, in C",
stated plainly.** In the emitted C there is no invariant check to
preserve — traverse `invariant P` is checked statically and emits
nothing. What the C exit owes, and what §2 rows 1–4 pin, is: control
reaches the post-loop point (label after the loop, continuation after
the label), locks taken inside are released on the exit path, the walk
binder is unusable after exit (it is `for`-local by construction), and
no bound-exceeded arm fires on the early path. Anything stronger needs
F2's syntax first.

**F3 — `retry` containing a `traverse` does not lower at all
(pre-existing, orthogonal, out of scope).** Measured with the shipped
binary: `retry … { traverse … { } }` (empty body), with a plain store
body, and with a `leave` body all pass `pruefe` 0-errors and all fall at
emit with C001 "`bounded … ops` -- the per-pass cost is not fixed";
`retry` with a non-traverse body lowers. So the refusal is about
traverse-in-retry costs, not about exits, and repairing
`retry_schranke` would be a cost-semantics change with corpus-wide
effects — the wrong lane and the wrong risk. Recorded, not repaired.

## 5. Handoff

- `emit.rs` is free after this merges: the delta is one comment, no
  open edits, no trap for lane 235 (Teil-3, never-lowering, queued
  behind this lane per TODO §-1).
- No N codes consumed (lowering lane, as planned); no gift numbers
  taken — none were needed (refusals reuse S001/P001, positives emit).
  Nothing to return, nothing owed.
- If `archive/234` is available at merge time, diff its
  `tests/traverse_exit.rs` against §2 rows 1–6; anything that holds over
  the current tree should be folded in, anything resting on pre-222/229
  syntax re-derived, not re-litigated.
