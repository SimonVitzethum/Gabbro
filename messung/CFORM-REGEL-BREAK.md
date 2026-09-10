# CForm ruling: `break`

Status: ruled 2026-09-10. Verdict: admit with price. No emitter change.

Census slot: C2, `abbruchStmt`, 51 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.abbruchStmt`). This is the
large sibling of `continue` (3 sites, ruled in
`messung/CFORM-REGEL-CONTINUE.md`): that note mapped where the `break` sites
live, and this note rules on them. The `while` form (11 sites) is a separate
ruling and is not booked here.

## 1. Emitter site

Emitted-text `break` comes out of exactly four lines of
`crates/gabbro-check/src/emit.rs`. Every other `break;` hit in the file is a
Rust-level statement of the emitter itself, not emitted text.

| emitter line | function | shape written |
|---|---|---|
| 7367 | `anweisung`, exchange-update lowering | `if (atomic_compare_exchange_weak_explicit(...)) break;`, loop exit on a won race inside the bounded CAS loop |
| 8537 | `nachfahren`, descendants post-order walk | `if ({k} == {r}) break;`, walk exit out of the `for (;;)` skeleton |
| 8909 | `match_markiert`, tagged match | `} break;`, switch-case terminator, one per arm |
| 8971 | `match_grund`, reason match | `} break;`, switch-case terminator, one per arm |

The natural split, already named in the `continue` ruling, is case terminator
(mechanical, one per arm, the bulk of the 51) against loop exit (control flow,
two lines). The fix differs per side: the terminator has no deletion that
preserves meaning, the loop exit has one that costs (section 2).

Two facts narrow the form, both read off the code:

- User code cannot emit it. Gabbro `leave` / `next` lower to `goto`, never to
  `break` / `continue`, precisely because a C `break` always takes the
  innermost loop while the named Gabbro exit may aim further out (comment at
  7505-7531). No user path reaches any of the four lines; all 51 sites are
  machine skeleton or machine case arms, not user control flow.
- The switch pair always terminates a braced arm (`case ...: { ... } break;`),
  never a bare fall-through chain. The `switch` carries no `default` on
  purpose so that `-Wswitch` stays a second reader of the closed distinction
  (comment at 8912-8924).

Count: 51 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), four emission lines.

## 2. Compiler fold

Two shapes of the same loop accumulation, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
int sum_break(int *a, int n) { int s = 0; for (int i = 0; i < n; i++) { if (a[i] < 0) break; s += a[i]; } return s; }
int sum_flag(int *a, int n) { int s = 0; int stop = 0; for (int i = 0; i < n && !stop; i++) { if (a[i] < 0) stop = 1; else s += a[i]; } return s; }
```

| flags | break form | flag desugar |
|---|---|---|
| -O0 | 33 | 36 |
| -O2 | 20 | 22 |

Reading: the flag desugar costs 3 instructions at -O0 and still costs
2 at -O2; it buys nothing at any level. A refusal of the two loop exits
would pay that on every walk and every exchange update in the corpus to
restructure the two most delicate emitted loops in the tree: the CAS retry
whose pass bound is the point of the construct, and the walk skeleton whose
edge reads must precede the body because `by consuming` may destroy the
handed node (comment at 8524-8530).

The switch pair has no row in this table, and the absence is itself a
finding: deleting a case terminator does not fold to the same program, it
falls through into the next arm. There is no semantics-preserving desugar
to measure, only a meaning change. Refusal is not a rewrite there; it is a
different program.

## 3. Semantic price

Admitting `break` pins two facts into the target language, one per side of
the section 1 split, and the note names both because the admission is the
ruling:

1. Loop exit out of two emission lines. The jump leaves the innermost
   `for (;;)`, whose identity is unambiguous in both skeletons (the CAS
   retry loop, the descendants walk). Termination of the walk rests on the
   well-foundedness hypothesis the skeleton already cites; termination of
   the retry rests on its pass bound. No new proof obligation arises beyond
   the ones the two loops already carry.
2. Case termination out of two emission lines. The jump leaves the
   `switch`, one per braced arm, and is what keeps the closed distinction
   closed at the C level. A reader of emitted C can trust that every `break`
   under a `case` is the arm's own terminator, because user exits are
   `goto` (section 1) and cannot pass through this form.

UB inventory: `break` contributes no UB class of its own. It performs no
access, no arithmetic, and no sequencing decision beyond the jump, which
stays inside the loop or switch the skeleton controls. There is nothing
here that can devalue a proof through C's rules, so no inventory row is
owed. This matches the `continue` ruling: the break/continue class is pure
control over machine skeletons.

## 4. Verdict: admit with price

`break` goes on the list with the two prices of section 3: loop-skeleton
exit out of two emission lines, case termination out of two more, no user
path, no UB. Refusal was considered per side and rejected on both:

- Terminator side: no semantics-preserving deletion exists. Removing the
  `break` merges the arms by fall-through, which is a different program,
  not a cheaper one.
- Loop-exit side: the flag desugar costs at -O0 and at -O2 (section 2) and
  touches the retry loop and the walk skeleton, which fails the
  trivially-safe bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-10 with `cc -O0/-O2 -c` plus per-function `objdump -d`
counts on the two shapes above.

Effect on the census on admission: C2 loses the `break` row, and the
break/continue class carries zero open doors (`continue` admitted in
`messung/CFORM-REGEL-CONTINUE.md`, `break` admitted here).
