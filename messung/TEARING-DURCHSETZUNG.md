# Tearing enforcement — the ruling as a check module

*Lane 146, base 6f26e76, 2026-09-11. Scope: two new files only —
`crates/gabbro-check/src/tearing.rs` (new module) and this note. No `lib.rs`
edit, no `emit.rs` edit, no probe, no test-suite, no count change. No new
assembler was inspected: every machine line below is copied from the lane-47
evidence block, and the module's fixtures assert that mechanically.*

## What the module is

`tearing.rs` enforces the lane-70 ruling (`messung/TEARING-RULING.md`) over
the lane-47 inventory (`messung/TEARING-INVENTAR.md`) as a post-emission
check: it scans the emitted C of one unit for multi-instruction sequences on
shared carriers and refuses them with the named code `T001`. The `T` letter
is unused anywhere else in `crates/`, so the kennungen guardian sees one
code in one file even after this commit.

## Refusal logic

One code, two shapes, each naming the guarantee that redeems it:

| emitted C shape | verdict | guarantee named | evidence (lane 47, both levels named) |
|---|---|---|---|
| compound assign (`+=`, `-=`, `&=`, `\|=`) to a shared carrier, guarded or not | refuse `T001` | exclusive access; the atomic form is the upgrade path | slot `+=`: load/`leal`/store at -O0; `addl $1, 4(%rdi,%rax,8)`, single RMW with no lock prefix, at -O2 |
| guarded compound assign (`o->slots[obj].zaehler -= 1;` under a lower-bound guard) | refuse `T001` | exclusive access; the guard sits beside the sequence | `movl (%rax), %eax` / `leal -1(%rax), %edx` / `movl %edx, (%rax)` at -O0; load, `subl`, store at -O2 |
| relaxed load, local fold, relaxed store on a shared accumulates cell in one function body | refuse `T001` | single-writer-per-cell | load, add, store at -O0; `addl (%rdx,%rax,4), %ebx` then `movl %ebx, (%rdx,%rax,4)` at -O2 |
| plain `=` store, atomic compare-exchange, release store / acquire load, lock take/release calls | pass | — (the atomicity price stays in the ruling) | single `movb`/`movq`, `lock cmpxchgl %edi, BESITZER(%rip)` with `sete %al`, plain moves, one `call` each |
| `volatile` access, port `__asm__ __volatile__` | open, no verdict | unmeasured — no device unit in the inventory | not measured at either level |

Carrier sharing is passed in from the declarations (`SharedCarriers`:
tables and `static mut` roots as carriers, `accumulates` stems as cells),
never re-derived from the C text. A compound assign to an undeclared name is
a local fold and passes; the merge fold alone passes for the same reason.
`++`/`--` are not compound shapes (the emitter uses them for locals and
loop counters only). A `+=` inside a comment or a string literal is
documentation, not a sequence, and is blanked before the scan. The scan
collects every refusal and never stops at the first hit.

Single-access admitted rows pass silently; volatile lines are listed under
`open` — counted openly rather than admitted silently, the way the ruling
counts the fluechtig row.

## The one hook point (specified, not built)

The module is standalone: no `pub mod` in `lib.rs`, no call in `emit.rs`.
When it is wired, exactly ONE call site is needed — a post-emission scan per
unit, after the C text is complete:

* **Site:** `emit.rs`, function `anweisung`, the `StmtArt::Zuweisung` arm's
  terminal push (the `ort(&z.ziel, …)`, `zuw_op(&z.op)`, value format — the
  single funnel through which every plain and compound place assignment
  reaches the C text). `check(&c_text, &shared)` runs once per unit at or
  above this arm's caller, not once per statement.
* **No second hook** for merge-add: the `accumulates` lowering (`_melde` /
  `_lies` with `atomic_load_explicit`, fold, `atomic_store_explicit`) is seen
  by the same scan after the fact, which is why one hook point covers both
  sequence shapes.
* **`SharedCarriers`** is built from the unit's declarations at the same
  site: tables and `static mut` globals name the carriers, `accumulates`
  names the cells.

It is NOT wired today for a measured reason: the scan reads C text, not
discipline. `01-tabelle` compounds under `KAPPEN` (exclusive access held at
the Gabbro level, invisible in the C) and `05-nebenlaeufigkeit` merges under
single-writer-per-cell (a discipline over cores, not over lines) — a hard
gate now would red-flag the corpus's own correct units. The refusal names
the guarantee; proving it is held belongs to the lock passes. Until that
join exists, this lane ships the refusal logic with its fixtures, not a gate.

## Verification

* `rustc --edition 2021 --test crates/gabbro-check/src/tearing.rs`:
  **14 passed, 0 failed.** The suite walks one row per measured form
  (emitted C in, ruling verdict out), proves every one of the thirteen
  lane-47 evidence lines is cited by at least one row at a named level, and
  checks the negatives: undeclared cells, read-only merge loops, split
  bodies, locals, comments, loop counters, and word boundaries on
  single-letter carriers.
* `cargo check -p gabbro-check`: clean (the tree is untouched apart from the
  two new files; the unwired module is compiled by the standalone run
  above, not by the package build).

## Open remainder (inherited, not added)

Volatile stays open for the device unit, a fourth unit outside the
inventory's budget. Every verdict stays x86_64-bound and level-bound per the
ruling. The Erhaltung feed is unchanged: witness material for zuweisung,
zusammZuweisung, atomar, ruf; fluechtig still open. Booked counts in
`TODO.md` are the integrator's — lane scope allows these two files only.
