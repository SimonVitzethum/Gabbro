# S4 findings F1 and F2: evidence, fix, verification

Base: `291c27b` (S1 baseline). Lane: `lane-06`. Scope of this note: record the
evidence for F1 and F2 named in the S4 status, with a fix procedure and the
verification commands. Nothing here is executed; the commands below are quoted
for the lane that owns the fix, not run.

Corpus context (from the S4 status): `beispiele/`, `71` files, all accepted by
the Rust checker: `189` routines, `119` witnessed, of which `53` both-accept and
`66` rust-only. F1 and F2 explain part of the rust-only column.

## F1: `endetMitAusgang` does not know `-> never`

### Lean side

`programmlogik/Gabbro/Sicherheit/Anweisung.lean:270-280`:

- `istAusgang` answers true only for `.ret`, `.retCall`, `.leave`, `.exit`,
  and false for everything else.
- `endetMitAusgang` reads only the last statement of the list.

There is no call case. A block whose last statement is a call to a function
declared `-> never` counts as falling through.

The use site where the gap bites is the same file, line `342`: `bindCallElse`
demands `endetMitAusgang onErr`, so an error branch that ends in a diverging
call is refused by `pruefe` even though control never falls off it.

### Rust side

`crates/gabbro-check/src/m1.rs:1473-1496`: `endet_immer` resolves the callee
by name and answers true when its declared result is `Typ::Nie`. The comment
above the rule states the direction explicitly: answering false is safe, and a
body that does not obviously end must still end properly.

The canonical copy is `crates/gabbro-check/src/lib.rs:1171-1185`: same rule
over a divergent-name list, with the indirect-call case documented as never
ending a body.

### Effect

| side | reading of a trailing `-> never` call | instances |
|---|---|---|
| Lean `endetMitAusgang` | falls through | `11a` |
| Rust `endet_immer` | ends the block | `11a` |

Every instance is a potential rust-only cell: the Rust checker accepts, the
Lean `pruefe` refuses, and the seam witness for the routine goes red for the
model's sake, not the program's.

### Fix procedure

1. Thread the divergent set through `pruefe` and `pruefeBlock`
   (`Anweisung.lean:296` onward), either as the program's signatures
   (`P.sig`, mirroring `rufPasst` at line `285`) or as a separate divergent
   list in the style of `lib.rs:1171`.
2. Extend `istAusgang` with a divergent-call case that mirrors the Rust rule:
   a call whose callee declares the never-result ends the block.
3. Adjust the `exec_sicher` proof: the new case needs the assumption that a
   declared-divergent callee indeed does not return (the U1-class premise for
   the callee's body, one level down).
4. Re-emit the seam corpus and recount the both-accept / rust-only columns;
   F1 instances must move from rust-only to both-accept, and no both-accept
   cell may move the other way.

### Verification (quoted, not run)

```sh
SEAM_SRC=beispiele SEAM_OUT=/tmp/seam cargo test -p gabbro-check --test seam -- --ignored emit_corpus --nocapture
```

```sh
for f in /tmp/seam/Seam*.lean; do timeout 300 lake env lean "$f"; done
```

## F2: duty `#ret` reuse against `binde`-U3

### Emitter side

`crates/gabbro-check/src/lean.rs`:

- Lines `2462-2465`: before a loop whose body may return, the emitter unbinds
  the duty names `#returned` and `#ret` in-term
  (`(.bindName "#ret" (.lit .absent))`) and records them via `push_local`.
- Lines `2354`, `2368`, `2374`: a `return` inside a loop desugars to a rebind
  of `#ret` (to absent, to a call answer, or to a value) plus raising
  `#returned`.
- Lines `889-893`: `push_local` shadows freely -- it pushes and drops the
  range, never refuses.

So the walk accepts any reuse of `#ret`, at any nesting depth, under any
shape.

### Model side

`programmlogik/Gabbro/Sicherheit/Anweisung.lean:100-105`: `binde` rebinds a
name only with the same shape (`if g = g' then some`), takes a fresh name by
cons, and otherwise returns `none` -- the checker refuses (assumption U3, same
file, lines `49-51`: the Rust checker refuses `let x = 1; ... let x = true;`).

When the second binding of `#ret` carries a different shape than the first
(value shape versus absent, or two different value shapes across nested
loops), `pruefe` gives `none` where the walk accepted. The seam side papers
over only the entry case: adapter A2 (`lean.rs:6331-6336`) replays `#ret` as
`.opt`, and `seam_bind` / `replay_scope` (`lean.rs:6373-6397`) rebuild the
entry scope exactly -- but the in-loop rebinding conflict under U3 remains.

### Effect

| side | reading of a second `#ret` binding under a new shape | instances |
|---|---|---|
| Rust walk (`push_local`) | shadows, accepts | `18` / `39` |
| Lean `binde` (U3) | `none`, refuses | `18` / `39` |

Each instance is a rust-only cell by construction: same program, accepted
duty term on the Rust side, refused `pruefe` on the Lean side.

### Fix procedure

Preferred (emitter side, proof-neutral):

1. Freshen the duty names per loop-nesting depth (for example `#ret-N` /
   `#returned-N` indexed by the loop stack depth at `lean.rs:2462`), so two
   live bindings never share one name.
2. Carry the same indexing through the desugar sites (`2354`, `2368`,
   `2374`), the post-loop test and return re-emission (`2555-2601`), and the
   `#ret` shape carried into `ret_post` (`3696-3706`).
3. Extend the seam replay (`6382-6397`) with the indexed names; A2 keeps
   reading entry `#ret` as `.opt`.

Alternative (model side, heavier): add a duty-name exception to `binde` with
its own soundness argument. This changes the trusted predicate instead of the
generated term and needs a proof that the exception cannot leak into
user-visible scope -- strictly more expensive than freshening.

### Verification (quoted, not run)

```sh
SEAM_SRC=beispiele SEAM_OUT=/tmp/seam cargo test -p gabbro-check --test seam -- --ignored emit_corpus --nocapture
```

```sh
for f in /tmp/seam/Seam*.lean; do timeout 300 lake env lean "$f"; done
```

Plus a nested-loop probe pair (one loop returning inside another) emitted
through the same driver with `SEAM_SRC` pointed at the probe directory, to
show the F2 cells moving from rust-only to both-accept with no reverse move.

## Open points

- F1 needs the never-result to be visible where `istAusgang` decides; if the
  signature table is not in reach there, the divergent list has to travel as
  an extra parameter through every `pruefe` clause.
- F2 freshening renames generated lines in every loop witness; the diff will
  be large and mechanical, and must be reviewed as mechanical.
- Both fixes move rust-only cells toward both-accept; the remaining rust-only
  column (F3 and later findings) is out of scope for this note.
