# Tearing inventory — single accesses vs sequences in emitted C

*Lane 47, base d162dfc, 2026-09-10, arch x86_64, cc GCC 16.2.1.
Scope: inventory only. No emitter, checker, probe, or test change.*

## Method

Three corpus units were emitted with the already-built gabbro binary and the
emitted C was inspected as assembler at two optimisation levels:

- `beispiele/01-tabelle.gab` — shared table slots, plain and compound slot
  assign under lock discipline
- `beispiele/35-tausch.gab` — atomic compare-exchange with declared ordering
- `beispiele/05-nebenlaeufigkeit.gab` — release store / acquire load pair,
  plain shared global assign, per-core relaxed merge-add, lock take/release

All three check clean (`gabbro pruefe` exit zero) and emit clean.
Binary provenance: the binary is the main-tree debug build from the same day.
No commit after its build time touched `crates/` (checked with
`git log --since` over `crates/`, empty), so the emitter it carries is the one
this worktree holds. The `.gab` sources are read from this worktree; only the
machine code generation ran elsewhere.

Recomputation:

```bash
G=/home/simon/Dokumente/Gabbro/target/debug/gabbro
for f in 01-tabelle 35-tausch 05-nebenlaeufigkeit; do
  $G emit beispiele/$f.gab > /tmp/$f.c
  for o in 0 2; do cc -std=c11 -O$o -fkeep-static-functions -S -o /tmp/$f-O$o.s /tmp/$f.c; done
done
```

Apparatus note: without `-fkeep-static-functions`, `-O2` deletes every
function in these units (all are static, the unit has no main) and the `.s`
file shrinks to a stump of a few lines. The flag keeps the functions for
inspection; codegen of the kept bodies is otherwise unchanged.

## Verdicts

Reading guide: single-access means the C statement lowers to one machine
memory access on x86_64 (no torn read or write possible for a naturally
aligned narrow access). Sequence means two or more machine accesses, so a
concurrent observer can see the middle. Neither verdict says anything about
atomicity of read-modify-write: only rows with a `lock` prefix are atomic,
and that is stated per row.

| emitted C form | Gabbro source | asm at -O0 | asm at -O2 | verdict | conditions | Erhaltung tafel rows fed |
|---|---|---|---|---|---|---|
| slot plain assign, `c->slots[s].benutzt = false;` | plain `=` to a slot field, 01-tabelle | single `movb` store | single `movb` store (folded into surrounding code) | single-access | aligned narrow store, both levels, x86_64 | zuweisung, named row admitted with one effect per statement |
| shared global plain assign, `farbbericht = wert;` | plain `=` to a `static mut` global, 05 | single `movq` store | single `movq farbbericht(%rip)` store | single-access | eight byte alignment shown by `.comm farbbericht,8,8`, both levels, x86_64 | zuweisung, same row as above |
| slot compound assign, `c->slots[s].marke += 1;` | `+=` on a slot field, 01-tabelle | sequence: load, `leal`, store | single `addl $1, mem`, no lock prefix | sequence at -O0, single RMW instruction at -O2 | x86_64; atomic at neither level, the lost-update window is closed by lock discipline, not by the instruction | zusammZuweisung, census slot under generous reading of assignment, plus zuweisung |
| guarded compound assign, `o->slots[obj].zaehler -= 1;` under a lower-bound guard | `-=` inside `if`, 01-tabelle | sequence: load, `leal`, store | sequence: load, `subl`, store, value reused by the following zero test | sequence at both levels | x86_64; the guard does not merge the accesses | zusammZuweisung plus zuweisung, same rows as above |
| atomic compare-exchange, `atomic_compare_exchange_strong_explicit` with release on success and acquire on failure | `exchange ... when old(...) == ...`, 35-tausch | single `lock cmpxchgl` | single `lock cmpxchgl`, result via `sete` | single-access, atomic | both levels, x86_64; ordering is the declared one, a plain `=` would have been seq_cst | atomar, named row for named ordering under A10 |
| release store and acquire load, `atomic_store_explicit` release and `atomic_load_explicit` acquire | `publishes` store and `awaits` load, 05 | single `movb` store and single `movzbl` load | single `movb` store and single `movzbl` load | single-access | x86_64 TSO carries the ordering, no fence instruction emitted at either level | atomar, same row as above |
| relaxed merge-add, relaxed load then `z += v` then relaxed store | `accumulates ... merge add` report path, 05 | sequence: load, add, store | sequence: `addl mem, reg` then store | sequence at both levels | x86_64; safe only by the single-writer-per-cell discipline, each core writes its own cell and the merge loop reads | atomar, same row as above |
| lock take and release, `KAPPEN_nimm();` and `KAPPEN_gib();` | `locks` block entry and exit, 05 | single `call` each | single `call` each, release call as tail jump | call sequence, one call instruction per op | the emitter writes only prototypes (`void KAPPEN_nimm(void);`), the body is foreign, so atomicity lives outside the unit | ruf, named row for calls to a declared or foreign body |
| volatile register access, `*(volatile uintN_t *)(basis + off)` | device register read or write | not measured | not measured | open, no verdict in this lane | none of the three units emits a volatile site; measuring it needs the device unit, a fourth unit outside the two-to-three budget | fluechtig, named row carried as axiom by name |

Evidence lines, copied from the inspected assembler:

```asm
addl    $1, 4(%rdi,%rax,8)          # slot += 1 at -O2, single RMW, no lock
movl    (%rax), %eax                # guarded -= at -O0, the load half
leal    -1(%rax), %edx              # guarded -= at -O0, the op half
movl    %edx, (%rax)                # guarded -= at -O0, the store half
lock cmpxchgl %edi, BESITZER(%rip)  # atomic exchange at -O2, single and atomic
sete    %al                         # exchange result, flags to boolean
movq    %rdi, farbbericht(%rip)     # shared global store at -O2, single mov
movb    $1, FARBE_FERTIG(%rip)      # release store at -O2, single mov, no fence
movzbl  FARBE_FERTIG(%rip), %eax    # acquire load at -O2, single mov, no fence
addl    (%rdx,%rax,4), %ebx         # relaxed merge-add at -O2, load-op half
movl    %ebx, (%rdx,%rax,4)         # relaxed merge-add at -O2, store half
call    KAPPEN_nimm@PLT             # lock take, one call instruction
jmp     KAPPEN_gib@PLT              # lock release at -O2, tail call
```

## What this feeds, and what stays open

The Erhaltung ruling table (`grammatik/Grammatik/Erhaltung.lean`, `tafel`,
proposed SYNTAX section 19.4) gains witness material for four rows:
zuweisung, zusammZuweisung, atomar, and ruf. The fluechtig row stays open;
its emitted shape is documented in the emitter source but was not re-measured
here, and the table counts that openly rather than silently.

Two findings worth carrying upward. First, the optimisation level moves one
row across the boundary: slot `+=` is a three-instruction sequence at -O0
and a single instruction at -O2, so any ruling that cites the machine shape
must name the level. Second, release and acquire on this arch cost nothing
visible: both lower to plain moves, and the ordering rides on x86 total store
order plus the compiler barrier inside the builtin. A port of these verdicts
to a weakly ordered arch would re-measure every atomar row.

Guardian note, measured not assumed: the revocation watcher reads this
directory (`pruefe-widerruf.py` globs `messung/*.md`) and reported thirteen
entries over 257 files before this file joined; with it the set holds 258.
The booked count in TODO.md is untouched on purpose — lane scope allows this
one file only, so the number is the integrator's, and this paragraph is where
the next lane finds the reason.
