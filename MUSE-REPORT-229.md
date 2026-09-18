# MUSE-REPORT-229 — subrange traverse checker: effects + early exit (TODO §-1 wave B)

## What was done

The `E010` walk in `crates/gabbro-check/src/wirkungen.rs` now reads the
**object of a `traverse`**: `traverse v of g over …` evaluates `g` (the walk
starts there), so the object reads like a bound. Two arms, both in
`wirkungen.rs`, both under pre-existing codes:

- `sammle_taten`, `StmtArt::Schleife` arm: `if let Some(g) = &x.gegenstand {
  liest_expr(g, t); }` beside the existing `domaene_liest`. This is the
  function level — an undeclared object read falls with **`E010`**, and the
  derivation (`rumpfwirkungen_mit`) and the owner pass (`lese_orte`, lane
  151/D267) inherit the same read with no second walk.
- `pruefe_touches`: the same object deed is held against `touches` — an
  object the traverse's own list does not name falls with **`E011`**.

This closes the booked gap in `wirkungen.rahmen` ("misses … the object of a
`traverse`") for this pass; `saetze.rs` strikes that clause and books the two
new probes. No new diagnostic code was needed, so **N416–420 are returned
unused**. `MARKE_EMIT*` untouched; `parse.rs`, `emit.rs`, Lean untouched.

Lowering side (`absenkung.rs`, doc only): the future windowed-traverse arm
(lane 234) lands inside the existing `Schleife` row — scaffold, bounds and
clamps must fit `STATEMENTS_PER_PRIMITIVE` (18), counted by the same lexer;
an arm that does not fit reads `C001`. That obligation is already enforced,
so nothing was built there either.

## New definitions / theorems / probes (exact names)

- `crates/gabbro-check/src/wirkungen.rs`: no new function; two added walk
  lines as above, each with a `Lane 229` comment stating the doctrine (object
  held, carrier not — see below).
- `crates/gabbro-check/tests/traverse_object.rs` (new): 4 snippet rows —
  `objekt_in_beiden_listen_ist_still`, `lauf_ohne_gegenstand_ist_still`,
  `traegerlauf_bleibt_ausserhalb_von_touches`,
  `gegenstand_ohne_touches_faellt_mit_e011`.
- `beispiele/gift/1077-traverse-object-not-in-touches.gab` (`-- erwartet:
  E011`, fires exactly `E011` alone): poison, object in the function effects
  but missing from `touches`.
- `beispiele/gift/1078-traverse-object-not-in-effects.gab` (`-- erwartet:
  E010`, fires exactly `E010` alone): poison, object in `touches` but
  missing from the function effects.
- Gift numbers 1079–1081 returned unused (no expressible exit probes — see
  finding 2).

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full suite, incl. the 4 new
  snippet rows and `keine_zwei_korpusdateien_teilen_eine_nummer`).
- `python3 instrumente/pruefe-saetze.py`: exit 0, ratchet unchanged (55
  without sentence, 0 invented).
- Corpus verdict diff, measured, not asserted: all 839 files under
  `beispiele/` + `beispiele/gift/` were verdict-fingerprinted before and
  after the change — **diff is zero**. The only intended movements are the
  two NEW poison files (which fall by construction).
- `./emission-pruef` not run: no emitter change, no `MARKE_EMIT` change, and
  neither new probe takes an emitter path (plain `-- erwartet`, not `allein`).

## What remains open / findings

**Finding 1 (measured — a task premise is false).** The task states lane
222's merged AST (subrange domain: start + length) is in my master. It is
not: lane 222 (merge `99d0e489`) merged a **reader refusal**, not an AST —
`parse.rs` `traverse()` parses `from <start> count <len>` positionally and
refuses it with the pre-existing `P001` ("the window has no lowering yet …",
`parse.rs:4088-4174`), building no `Traverse`. There is no `Domaene`
variant and no `Traverse` field for a window anywhere in the tree
(verified by grep over `crates/gabbro-syntax/src/ast.rs`). Measured
behaviour: a windowed walk ends at parse; no checker pass ever sees a
window. Consequence: "traverse-over-window reads/writes exactly the window"
and "window bound expressions read" are **unbuildable in my exclusive file
set** (`wirkungen.rs`, `absenkung.rs`, `saetze.rs`, tests/probes — no
`parse.rs`, no `ast.rs`, no `emit.rs`). The rule I built is the exact
generalisation on the syntax that exists: the domain form's evaluated
expressions (today: the `of` object; tomorrow: the `from`/`count` bounds,
which join the same two walk sites — the comment in `pruefe_touches` names
the spot). The syntax lane must add: a `Domaene` window variant or
`Traverse` window fields carrying both bound `Expr`s (dropping them
silently would repeat the whole-table misread the `P001` note guards
against), plus `SYNTAX.md` §8 grammar.

**Finding 2 (measured — early exit needs a label that does not exist).**
`traverse` carries no label (`SYNTAX.md` §8; `schleifen.rs:114`), so a
`leave` inside one can only target an enclosing `retry`/`forever` — pinned:
`leave done` inside a traverse falls with `S001`, "no label is in scope
here". "Find the first, then continue" is unwritable (TODO §-1 open item),
and no invariant-dropping / clean-exit probe is expressible: a poison would
fall via `S001`/`P001`, never via an exit rule — a probe that cannot bite
is not a probe. Hence no exit refusal was built (building one would be the
vacuous-premise defect: a rule no ordinary program can reach).

**The exit obligation, stated plainly (deliverable 2).** What a future
labelled traverse exit owes, and where each half is checked:

1. Syntax (needs a parse/AST lane): `traverse` gains an optional label,
   `traverse [ident] …`, mirroring `retry`/`forever`. `leave L` / `next L`
   naming a traverse label is the bounded exit — bounded by construction,
   because a traverse walks a finite domain.
2. At the exit point the traverse's `invariant P` must hold, and the
   continuation may assume **only** P plus "the first k elements visited" —
   never "all elements visited". An exit that exports the whole-domain
   postcondition, or that leaves from mid-pass with P broken, stays
   refused. Label resolution stays `S001` in `schleifen.rs` (owns labels);
   the invariant-at-exit hold belongs beside `touches` in `wirkungen.rs`
   (this lane's file set, when labels land); the Pred decision itself
   belongs where Preds are already evaluated (`gegenbeispiel.rs` evaluates
   traverse invariants today).
3. Lowering (lane 234): the exit is a break out of the generated loop,
   inside the ≤18-statement `Schleife` budget `absenkung.rs` already
   enforces — specified, not built.

**Deliberately not built, with the measurement.** Holding the CARRIER walk
against `touches` (the whole-table form of "reads exactly the window")
fires on exactly two corpus files — `beispiele/09-ohne-zeiger.gab`
(`touches consumes Kappenraum.slots` over `descendants of
Kappenraum.slots[s]`: `consumes` covers no read in either leg) and
`beispiele/57-faedenhalt.gab` (`touches writes Faden.slots` over `slots of
Faden`: the bare-root domain deed is not prefix-covered). Both files are
deliberate, commented, and treat `touches` as the body's promise with the
walk carried by the function effects. Overriding that split would refuse
the corpus, which this lane may neither do (zero-diff mandate) nor repair
(corpus files outside the exclusive set). The doctrine is therefore:
bounds/object (evaluated expressions) stand against `touches` AND function
effects; the carrier walk stays the function effects' business. The
reverted carrier hold is documented in the code comment so the next lane
does not re-add it silently.

## Anything in the task believed wrong

- "Lane 222's merged AST … in YOUR master now; read `ast.rs`, not the lane
  report" — wrong as measured (Finding 1 above); the lane report's
  description (refusal + handoff) is the accurate one.
- "RESERVED … gift numbers 1077–1081 (poison: invariant-dropping exit;
  positive: clean early exit)" — half unusable as measured (Finding 2);
  1077/1078 carry the object rule instead, 1079–1081 unused.
- "extend the walk, do not widen it" (E010) — followed literally: the walk
  gained the object expression (a read the run performs) and nothing else;
  coverage filters (parameters, constants, unknown names, bare-vs-prefix
  `deckt`) are byte-identical.
