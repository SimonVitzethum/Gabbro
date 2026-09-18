# MUSE-REPORT-234 — traverse lowering for subrange + early exit (TODO §-1 wave B)

## Round 2 (reviewer verdict ROT, finding F1) — option (ii)

The reviewer confirmed the premise findings (F2, no action) and asked for
exactly one of: (i) scope expansion to parse/AST + checker, or (ii) strengthen
what is buildable within `emit.rs` + `tests/`. The dispatcher did not expand
the scope, so this round takes **option (ii)**: the two regression probes are
kept, and the negative pin the round-1 report implied but no test stated is
now stated — a `leave` naming the traverse itself is refused, proving the
traverse carries no label. No dead emitter arm, no prose about postcondition
preservation that no rule could check.

New in round 2 (`crates/gabbro-check/tests/traverse_exit.rs`, now 4 tests):

- `leave_naming_no_label_from_traverse_falls_with_s001`: `leave suche;`
  inside a traverse with no enclosing labeled loop falls with exactly
  `["S001"]`, and the refusal carries the empty-scope note ("no label is in
  scope here") — the traverse contributes no label.
- `leave_past_the_outer_label_from_traverse_falls_with_s001`: the same exit
  inside a traverse inside `forever d` falls with exactly `["S001"]`, and the
  scope note names exactly `d` ("im Geltungsbereich: d") — the set a future
  traverse label would extend, and today the traverse adds nothing to it.

Close, as instructed: **lane blocked upstream, no lowering buildable.** The
windowed `for` and the labelled exit with invariant-at-exit need the parse/AST
lane first (see "What remains open" — unchanged and still correct); re-running
this lane without that upstream work cannot produce a lowering.

## Verdict up front (round 1, stands)

The lowering the task asks for is **unbuildable from this lane's file set**,
for the same measured reason lane 229 reported: the syntax it would lower does
not exist in this tree. What is buildable — and built — is the emission probe
pinning the exit-from-inside-a-traverse routing that any future labelled
traverse exit generalises. `emit.rs` is deliberately untouched: an arm for an
unrepresentable form would be dead code, not a lowering.

## What was done

- New probe file `crates/gabbro-check/tests/traverse_exit.rs` with two
  emission tests over fully CHECKED programs (`pruefe` runs first, zero
  errors asserted — unlike the neighbouring `rechenwerk.rs` probe, which
  parses + emits only and never runs the checker):
  - `leave_from_traverse_reaches_the_outer_label`: `leave d;` inside a
    `traverse` inside `forever d` emits `goto d_ende;` INSIDE the generated
    `for (uint32_t i = 0; …)`, the `d_ende: ;` label past the `forever`, no
    `break;` anywhere (a `break` would leave the `for`, not the named loop),
    and `L_gib();` immediately (<= 2 lines) before the jump.
  - `next_from_traverse_reaches_the_outer_label`: the symmetric `next d;`
    shape — `goto d_weiter;`, `d_weiter: ;` present, no `continue;`, same
    release-before-jump.
- No other file touched. In particular `emit.rs` is byte-identical: the
  routing probed (`Leave`/`Next` → `goto` + `Austritt::schleifen` releases,
  `sprungziele` descending through `Traverse` without shadowing since a
  traverse carries no label) already lowers correctly; there was nothing to
  repair, only something to pin before the syntax lane generalises it.

## Why the asked lowering was not built (measured, twice)

1. **No subrange AST (lane 222 merged a refusal, not an AST).** `parse.rs`
   `traverse()` parses `from <start> count <len>` positionally and refuses it
   with the pre-existing `P001` (`parse.rs:4146-4174`); `ast.rs` has no
   `Domaene` window variant and no `Traverse` window field (struct fields:
   `variable, gegenstand, domaene, abstieg, mass, touches, invariante, rumpf,
   span`). A windowed walk ends at parse — no checker pass and no emitter arm
   ever sees a window. Pinned by `sprechprobe.rs`
   (`lane222_windowed_traverse_refused_by_name`).
2. **No traverse label, no exit rule (lane 229 built object-reads, not
   window/exit rules).** Merge `e2184405` = object reads against effects +
   touches (gifts 1077/1078) plus a doc note in `absenkung.rs`; its report
   states plainly that window bounds and the labelled exit were unbuildable
   and specifies what each future lane owes. `Traverse` has no `marke` field;
   `schleifen.rs:114` and `S001` confirm a `leave` inside a traverse can only
   name an enclosing `retry`/`forever`.
3. Consequence: from `emit.rs` + `tests/` alone (this lane's exclusive set —
   no `parse.rs`, no `ast.rs`, no checker files, no Lean), neither the
   windowed `for` (start/length bounds, clamping) nor the invariant-at-exit
   hold can be expressed. Stating them here would be prose wearing a test's
   clothes.

## Check results (exact lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full suite; the new
  binary runs `4 passed; 0 failed`: `leave_from_traverse_reaches_the_outer_label`,
  `next_from_traverse_reaches_the_outer_label`,
  `leave_naming_no_label_from_traverse_falls_with_s001`,
  `leave_past_the_outer_label_from_traverse_falls_with_s001`).
- `./emission-pruef`: `== EMISSION: ALL PASS -- 37 durchgestochen, 286 von 286
  uebersetzen, 2 umgekehrte Probe(n) ==`.
- `python3 instrumente/pruefe-cformen.py`: `RED: 0 new uncovered form(s),
  1 unclassified statement(s), 0 missing lemma(s), 0 missing assumption(s).`
  The 1 unclassified statement (`140-atomic-array-counter.gab`, an
  atomic-array shape from lane 221's area) is **pre-existing**: the identical
  RED reproduces with my change stashed. No new C form is emitted by this
  lane (`for`/`goto`/labels are rowed as `stmt:for-counting`/`stmt:goto`),
  so no new row is owed — nothing silent.
- `./lean-bau`: `Build completed successfully (280 jobs).` (no Lean file
  touched; build stays green for the whole project).
- `MARKE_EMIT` delta: **0**. No counter line touched, no `.gab` file added.

## What remains open (handoff, exact)

For the window + labelled-exit work, in dependency order:

1. **Parse/AST lane** (not 234): a `Domaene` window variant or `Traverse`
   window fields carrying BOTH bound `Expr`s (dropping them silently would
   repeat the whole-table misread the `P001` note guards against), an
   optional traverse label mirroring `retry`/`forever`, plus `SYNTAX.md` §8.
2. **Checker lane** (`wirkungen.rs`, per 229's spec): window bounds read;
   traverse-over-window reads/writes exactly the window; invariant P held at
   the labelled exit, continuation assuming only P + "first k visited".
3. **Emitter lane** (this lane's natural successor, with 1+2 merged): the
   windowed `for` (bounds, clamps) and the exit-as-break, inside the
   ≤18-statement `Schleife` budget `absenkung.rs` already enforces. The two
   probes here are its regression net: the outer-label routing must keep
   working when the traverse gains its own label.

## Findings for other lanes

- **Probe-contract shape (K003):** a function whose body contains a `forever`
  anywhere must OMIT `costs` (its promise is `per_pass`, `kosten.rs::ohne_summe`); a written `costs` over one is `K003`. The
  neighbouring `rechenwerk.rs` leave-probe never runs the checker, so its
  `costs <= 8 ops` over a forever-body never fires — a parse+emit-only probe
  proves less than it looks. Both probes here run `pruefe` and therefore omit
  `costs` on the forever-body (omission is explicitly legal, lane 191).
- **Gift numbers:** none taken. None were reserved for lane 234, and the task
  says to ask, not take — asking: no gift stock is needed, since no refusal
  was built and none could bite (a poison for an unparseable form falls via
  `P001`, never via the probed routing).

## Anything in the task believed wrong

- "Lane 222's merged AST (traverse subrange domain — in YOUR master now)" —
  wrong as measured (finding 1 above); lane 222 merged `parse.rs` refusal +
  handoff note, no AST. The lane report (refusal + handoff) is the accurate
  record, not the task's one-line summary.
- "lane 229's merged checker (window effects + exit rule — … the exit owes a
  stated obligation, your lowering must discharge exactly that)" — half
  wrong: 229 merged the object-reads rule (E010/E011) and STATED the exit
  obligation without building the exit rule (correctly — the label does not
  exist). There is no exit-rule obligation to discharge in C yet; the
  discharge point (`absenkung.rs` `Schleife` budget) is specified, not built,
  and my probes cover the routing half that exists.
- "The exit lowering must preserve the loop postcondition at the exit point
  (lane 229's obligation, in C)" — 229's obligation has a checker half
  (invariant P at the exit, `wirkungen.rs`) that precedes any C half; with no
  label and no invariant-at-exit rule, a C-side "postcondition preservation"
  claim would be uncheckable prose. Said plainly per rule 4: this deliverable
  is weaker than the task asks, and the gap is missing syntax, not missing
  effort.
