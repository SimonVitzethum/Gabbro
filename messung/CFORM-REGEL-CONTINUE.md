# CForm ruling: `continue`

Status: ruled 2026-09-10. Verdict: admit with price. No emitter change.

Census slot: C2, `fortStmt`, 3 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.fortStmt`). This is the
small form of the break/continue class, picked as the second ruling of this
lane beside `logUndOder` (ruled in `messung/CFORM-REGEL-LOGUNDODER.md`). The
large sibling, `break` at 51 sites, stays open; this note records where its
sites live so the next ruling starts from data, not from search (section 4).

## 1. Emitter site

Exactly one line of the emitter writes `continue` into C output
(`crates/gabbro-check/src/emit.rs:8536`), inside the descendants post-order
walk skeleton:

```c
for (;;) {
    if (!{h} && {basis}[{k}].{kind} != {n}u) { {k} = {basis}[{k}].{kind}; {h} = false; continue; }
    if ({k} == {r}) break;
    ...
}
```

Every other `continue;` hit in `emit.rs` (18 of 19) is a Rust-level loop
statement of the emitter itself, not emitted text. So all 3 census sites come
out of this one line: the corpus units that walk a tree to its leaves each
carry one copy of the fixed skeleton.

Two facts narrow the form further, both read off the code:

- User code cannot emit it. Gabbro `leave` / `next` lower to `goto`, never to
  `break` / `continue`, precisely because a C `break` always takes the
  innermost loop while the named Gabbro exit may aim further out (comment at
  7505-7531). No user path reaches the `continue` line; it is machine
  skeleton, not user control flow.
- The sibling line 8537 (`if ({k} == {r}) break;`) is one of the `break`
  sources, not this ruling. The remaining `break` sources are the retry
  watchdog at 7367 and the two switch-case terminators at 8909 and 8971,
  which account for the bulk of the 51 open `break` sites.

Count: 3 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), one emission line.

## 2. Compiler fold

Two shapes of the same loop body, `cc (GCC) 16.2.1` on x86-64, instruction
counts from `objdump -d` per function:

```c
void walk_continue(int *a, int n) { for (int i = 0; i < n; i++) { if (a[i] < 0) continue; a[i] += 1; } }
void walk_nested(int *a, int n) { for (int i = 0; i < n; i++) { if (a[i] >= 0) { a[i] += 1; } } }
```

| flags | continue form | nested form |
|---|---|---|
| -O0 | 40 | 38 |
| -O2 | 17 | 17, same mnemonic sequence |
| -Os | 11 | 11, same mnemonic sequence |

Reading: at optimisation the two shapes fold to the same instruction
sequence; at -O0 the `continue` form costs 2 instructions. A refusal (nesting
the walk-skeleton remainder under an `else`) would buy 2 instructions at -O0
and nothing above it, against restructuring the most delicate emitted loop in
the tree (the skeleton whose edge reads must precede the body because `by
consuming` may destroy the handed node, per the comment at 8524-8530).

## 3. Semantic price

Admitting `continue` pins one fact into the target language: an unconditional
jump to the loop-continuation point of the innermost `for (;;)`. The price is
small and this note states it whole:

1. Loop control, single site, fixed skeleton. The jump target is unambiguous
   (the innermost loop is the skeleton's own), the guard is fixed machine
   text, and termination rests on the well-foundedness hypothesis the
   skeleton already cites. No new proof obligation arises beyond the one the
   walk already carries.
2. No user confusion class. Because user exits are `goto` (section 1), a
   reader of emitted C can trust that every `continue` is the skeleton's and
   every user exit names its loop. The wrong-loop error the emitter guards
   against at 7505-7531 cannot pass through this form.

UB inventory: `continue` contributes no UB class. It performs no access, no
arithmetic, and no sequencing decision beyond the jump, which stays inside
the loop the skeleton controls. There is nothing here that can devalue a
proof through C's rules, so no inventory row is owed.

## 4. Verdict: admit with price

`continue` goes on the list with the price of section 3: loop-skeleton
control out of one emission line, no user path, no UB. Refusal was considered
and rejected: it would rewrite the descendants-walk skeleton to save 2
instructions at -O0, touching the loop whose edge-read order is load-bearing,
which fails the trivially-safe bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-10 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two shapes above.

Remainder for the next ruling: `break` (51 sites, still open) lives at four
lines — retry watchdog 7367, walk exit 8537, switch terminators 8909 and
8971. The switch pair is the bulk and the natural next split: case
terminator (mechanical, one per arm) against loop exit (control flow). The
`while` form (11 sites) is a separate ruling and is not booked here.

Effect on the census on admission: C2 loses the `continue` row, the C count
falls one further step, and the break/continue class carries one open door
(`break`) instead of two.
