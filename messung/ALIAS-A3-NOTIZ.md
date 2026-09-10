# Alias A3 note: the event half of the gap

*Lane lane-15, base 291c27b. Lane scope forbids builds, so nothing below was
re-run here: line references are read at base, and every behavior sentence is
code reading, not a fresh measurement. Figures quoted from other notes name
their source.*

## 1. What A3 is

`messung/RACE.md` books two alias rows that nothing carries:

- A2: two pointers to one object under different names.
- A3: the event half — a write through one name invalidates nothing held
  through the other name.

`R007` closed A1 on 2026-08-24 (same syntactic place at two writable
parameters of one call); `R004` already carried the `own` half. A3 is what
stays silent the moment the two spellings differ. It has two halves and both
are open:

- (a) no refusal at the call with two writable pointer parameters bound to
  one object under two names;
- (b) no invalidation after it — facts, reads, and effects held through the
  sibling name survive a write through the other name across the call
  boundary.

## 2. What R007 and R004 compare: place strings

The mechanism, as read at base:

- Call arguments reach the checker as optional strings in `aufrufgraph.rs`:
  a place under any number of parens maps through `Ort::text()`, and anything
  that is not a place maps to nothing. A computed argument (`f(a + 1)`,
  `f(g(x))`) is a value, not a place, so it is never compared with anything.
- The double-marking pass in `crates/gabbro-check/src/m3.rs` compares those
  strings for equality: `R007` at two writable non-`own` positions, `R004` at
  two `own` positions. One report per call; the loop stops after the first.
- `saetze.rs`, sentence `m3.syntaktischer-alias`, states the limit openly: the
  syntactic half only, decidable without an alias analysis the checker does
  not have. Compared is the place, not the root, so `f(p->a, p->b)` passes by
  design. Only parameters count: a pointer arriving through a `let`, a global,
  or a return value carries no declared right and is not marked writable.

One rendering detail matters. `Ort::text()` in `ast.rs` prints an index
suffix as a fixed marker, so any two indexed arguments over one base share a
single spelling. Against that, the sentence note in `saetze.rs` reads as
though `f(t[i], t[j])` passes when the indices are equal at runtime; by the
code as read the two spellings are identical and the rule fires rather than
passes. Unmeasured under this lane, booked here as sentence-vs-code tension
that wants exactly one probe: same base with equal indices, same base with
provably different indices, and two different bases.

## 3. Slip-through classes

Each row is one way to put one object under two spellings, or to keep an
argument out of the string comparison entirely.

| class | example | why the string comparison misses it |
|---|---|---|
| re-view second name | w = kopfworte_von(k), then f(k, w) | distinct spellings, one object; the S4 shape counted in alias.rs |
| let-bound alias | let q = p, then f(p, q) | distinct spellings for one object |
| global plus view | f(g, h) where h views the same memory as g | distinct spellings; the global spelling alone would only match itself |
| value argument | f(g(x), p) | not a place, so no string exists to compare |
| indirect call | call through a place carrying a function-pointer contract | no key in the call graph; the R007 walk covers direct edges only |
| runtime-equal indices | f(t[i], t[j]) with i equal to j | index values are decided nowhere; see the spelling tension in section 2 |
| alias from two frames up | the two names are innocent at the immediate site | the call text shows two distinct spellings and nothing else |

The table is one-directional: it lists calls that pass and should not. The
index row cuts the other way too — one shared spelling for distinct objects
is a false-alarm risk, which is the precision price of comparing strings.

## 4. Cheapest sound rule: invert the default

Current default: distinctly spelled arguments are distinct objects unless
proven aliased — the checker refuses only on equal strings. Sound default:
two live writable pointer arguments at one call may alias unless proven
disjoint.

Minimal sound step, in order:

1. Refuse any call with two writable pointer parameters whose arguments are
   both live places, regardless of spelling. Signature-only, no liveness
   analysis: if both positions are writable in the callee declaration, the
   call must show disjointness or fail.
2. Keep exactly one pre-built disjointness proof: distinct field suffixes on
   one base. `f(p->a, p->b)` stays silent — the carve-out `R007` already
   documents. It is the only proof with precedent; everything else is refused
   until proven.
3. Bound the blast radius before building: `gabbro alias` already prints the
   writable multi-pointer call sites (strata S1 through S5 in `alias.rs`),
   which is the review surface of step 1. No new census is needed to size it.
4. Add further proofs one by one, each with its own probe — index
   disjointness, re-view tracking, cross-frame naming — never as silent
   exceptions. A cheaper variant of step 1 skips pairs where one argument is
   dead after the call, but liveness is itself new analysis; it is cheaper to
   live with, pricier to build.

What this rule does not close: half (b) of section 1. Refusing the call stops
the write from happening under two names; it does not kill a fact already
held through the sibling name. The invalidation half is separate work and
must be booked separately, or the refusal will read as a fix for stale facts
it never touches.

## 5. Risks and non-claims

- No run backs this note: builds are outside lane scope, so the
  sentence-vs-code tension on indexed spellings is flagged, not settled.
- Inverting the default over-refuses by construction until carve-outs land;
  landing them silently would rebuild the current gap under a stricter name.
- The field carve-out is sound only while fields of one record stay disjoint;
  overlapping layouts would need their own proof and do not get this one.
