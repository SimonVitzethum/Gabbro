# GabbroK — synthesis out of the manifest

Status: plan. No code. Everything below names its command where it counts
something; estimates are marked as estimates.

## 0. What gabbroK is, and what it is not

`gabbro new` writes the irreducible skeleton that checks, builds and runs
as written. gabbroK is the same idea run to its end: **a manifest in,
a program out — or a refusal that names the manifest line that cannot be
built.**

```
gabbrok build --manifest <spec> --out <dir>
```

Two exits per manifest line, never one: **emitted** (Gabbro source with an
anchor per line) or **refused** (`refused <code> <manifest line>`, with the
checker diagnostic quoted verbatim). A line that is neither is a tool
defect, and the run ends with a line-count comparison that aborts on
deviation — E1 wired in, not hung beside it, the way `AUFTRAG-GABBROV.md`
asks it of GabbroV.

What gabbroK is not: a second checker, a second emitter, a prover. The
oracle is always `gabbro check` and `gabbro emit`. gabbroK never joins the
trust base, and nothing it writes ships without passing both.

## 1. The two manifests, kept apart

The build manifest (`.bau`) stays what `BAUSYSTEM.md` measured it to be:
files per unit, unit kind, foreign compiler with flags, output directory.
It says which files form a unit and never what is in them; edges are
computed out of `module` and `use`, never written (W7).

The synthesis manifest (the spec) is a second file with a second subject:
**what the program must be**, not which files it is. Conflating the two
repeats the `rsync -a` class: one register over two things that drift.

## 2. What the spec carries — shared with GabbroV wherever possible

`AUFTRAG-GABBROV.md` section 4 already fixes the per-line shape both tools
read: name, obligation text, anchor (`file:line`), class, state — plus a
version field first and E1 inside the run. The `--lean` and `--isabelle`
channels already serialise the same register (`pflichten::sammle`), and the
assumption manifest already carries name, kind, probe or reason, and side
condition (`manifest.rs`). gabbroK reads all three and adds one part:

1. **Structure (new).** Tables with count, slots and types; records with
   fields and ranges; function signatures with parameters, result,
   `effects` and `costs`; devices by name and space only; locks and groups
   only where carried. No bodies. Every line carries its anchor.
2. **Contract (half standing).** `requires`, `ensures`, `maintains` and
   invariants as text plus anchor. The ordinal form (`ensures #1`) is not
   enough — the text field of manifest version 2 is the half that makes a
   line readable without the source, and it must become complete.
3. **Assumptions (standing).** The assumption set with class, probe or
   reason, machine where it matters, and side condition. Generated machine
   entries (float mode, lock imprint, boot retirement) stay generated.
4. **Write-back (new).** `refused <code> <manifest line>` plus the checker
   diagnostic quoted word for word. A fail points at the manifest line,
   never at generated C. A generated line no manifest line covers is the
   mirror defect, and it aborts the run.

## 3. How hard the spec language is to write

Measured against the corpus behind `GABBROV-V1.md` (63 obligations after
the rebooking, 55 sayable) and the means `SYNTAX.md` already carries:

- **Easy, one to one.** Tables, types, signatures, `effects` and `costs`
  frames, invariant names, lock footprints where carried. A writer copies
  declarations and pays no design cost.
- **Medium.** `requires` and `ensures` predicates (aggregation `count`,
  `reaches`, `old` and `result`), `traverse` domains, device promises,
  `retry` bounds with `on_exceeded`. Each has a grammar production and at
  least one probe; each can still surprise (bounded reachability is the
  largest of the three, and the language already has it while the Lean
  channel refused it by name).
- **Hard.** Loop bodies with measure and invariant, `by consuming`
  carriers, assumptions about the world (they stay prose plus probe and
  never become proof duties), frame conditions no `spec fn` can say.
  The hard class is the honest source of `undecided` and of refused
  manifest lines. It is priced, not hidden.

## 4. Stages and gates

- **K0 — freeze the spec.** Version field, E1 comparison, readers on both
  versions before the format moves. Gate: every reader refuses an unknown
  version instead of misreading it; line counts match in every run.
- **K1 — skeleton expander.** Structure plus signatures plus contracts as
  names, no bodies; every emitted line carries its anchor. Gate: the
  skeleton checks, and every line it cannot place is refused with its
  manifest line.
- **K2 — body search per obligation.** Templates first (`option`,
  `table`, `verbund`); loops only in the `traverse` and `retry` forms,
  anything else is `undecided`, never guessed. The search never stops at
  the first hit — it reports which hits fire. Gate: one search per
  obligation kind, each with a probe that shows the pair (without the
  fact it falls, with the fact it passes).
- **K3 — back-mapping.** Every `C001` and every checker refusal maps to
  the manifest line that caused it, with one test per exit (emitted,
  refused, and the counter-proof that a broken product fails). Gate: the
  E1 comparison plus the counter-proof, both green.
- **K4 — ratchet over the line.** Key `(name, class, text)`, anchor only
  as last resort — the `BERICHT-O3-RATSCHE.md` finding: ordinals do not
  move with conjunct swaps. Gate: a swap moves the verdict, an identical
  line keeps it.

## 5. Cost, in the open

K0 and K1 are weeks: format work plus the skeleton the tree already grows
(`new`, `abi`, the manifest printers). K2 is the expensive part — one
search space per obligation kind, and the no-early-abort rule applies to
every one of them. K3 is duty, not research. None of this is estimated
against the corpus it would then be measured on; the unseen-port rule
holds here too.

## 6. What this does not move

Beta needs no proof, only a checker that does not lie — gabbroK is behind
Beta, not on its path. K100 needs `H = 0` (done), `L` within its bound,
the assumption count down, and a second corpus; gabbroK consumes those
numbers and changes none of them. Lean stays the specification side and
Isabelle the proof side; gabbroK adds a reader, not a second register,
and says per line which side owns it.
