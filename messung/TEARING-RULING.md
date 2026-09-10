# Tearing ruling — admissions over the lane-47 inventory

*Lane 70, base c7dcd69, 2026-09-10, arch x86_64, cc GCC 16.2.1 (inherited).
Scope: ruling only. The inventory is `messung/TEARING-INVENTAR.md` (lane 47,
base d162dfc). No emitter, checker, probe, or test change. No new measurements:
every assembler line cited here is copied from the inventory's evidence block,
and no `cc -S` run was needed to confirm any of them.*

## The rule

A form is admitted as tear-free if and only if the inventory shows a single
machine memory access at both -O0 and -O2. Admission is never free: each
admitted row carries its atomicity price — the alignment, architecture, or
ordering assumption the single access rests on.

A sequence form is refused as self-sufficient: at least one level shows two or
more machine accesses, so a concurrent observer can see the middle. Each
refusal names the exact guarantee that redeems it — exclusive access,
single-writer-per-cell, or atomic form — and states what breaks without it.

Lock-prefixed instructions are the only atomic read-modify-write in this
ruling. A single non-locked RMW instruction (the -O2 shape of slot `+=`) is
still a sequence in consequence: one instruction, two observable halves, no
atomicity. The optimisation level can move a row across the single/sequence
boundary, so every verdict below names both levels.

## Admissions — single-access at both levels, with price

| emitted C form | verdict | atomicity price | evidence (lane 47) |
|---|---|---|---|
| slot plain assign, `c->slots[s].benutzt = false;` | admit | aligned narrow store; no ordering claim beyond one non-torn write | single `movb` store at both levels |
| shared global plain assign, `farbbericht = wert;` | admit | eight byte alignment per `.comm farbbericht,8,8`; one non-torn write, no RMW atomicity, no ordering | single `movq` store at -O0; `movq %rdi, farbbericht(%rip)` at -O2 |
| atomic compare-exchange, `atomic_compare_exchange_strong_explicit` with release on success and acquire on failure | admit | the declared ordering itself; a plain assign here would have been sequentially consistent by default, the named ordering is the price paid deliberately | `lock cmpxchgl %edi, BESITZER(%rip)` at both levels; result via `sete %al` |
| release store and acquire load, `atomic_store_explicit` release and `atomic_load_explicit` acquire | admit | x86_64 total store order plus the compiler barrier inside the builtin; no fence instruction emitted; re-measure on any weakly ordered arch | `movb $1, FARBE_FERTIG(%rip)` store and `movzbl FARBE_FERTIG(%rip), %eax` load at -O2; single moves at -O0 |
| lock take and release, `KAPPEN_nimm();` and `KAPPEN_gib();` | admit as call sequence | atomicity lives outside the unit: the emitter writes only prototypes, the body is foreign | `call KAPPEN_nimm@PLT`, one call instruction per op; release as tail jump `jmp KAPPEN_gib@PLT` at -O2 |

## Refusals — sequence at one or both levels, with consequence

| emitted C form | verdict | guarantee needed | what breaks without it | evidence (lane 47) |
|---|---|---|---|---|
| slot compound assign, `c->slots[s].marke += 1;` | refuse | exclusive access; atomic form is the upgrade path | lost update under concurrency; the -O2 single instruction narrows the window but does not close it | sequence load, `leal`, store at -O0; `addl $1, 4(%rdi,%rax,8)`, single RMW with no lock prefix, at -O2 |
| guarded compound assign, `o->slots[obj].zaehler -= 1;` under a lower-bound guard | refuse | exclusive access; the guard contributes nothing to atomicity | same lost update as the unguarded form; the guard does not merge the accesses | `movl (%rax), %eax`, `leal -1(%rax), %edx`, `movl %edx, (%rax)` triple at -O0; load, `subl`, store with the value reused by the following zero test at -O2 |
| relaxed merge-add, relaxed load then `z += v` then relaxed store | refuse | single-writer-per-cell: each core writes its own cell and the merge loop reads | concurrent writes to one cell tear; concurrent read of a cell mid-sequence sees the middle | load, add, store sequence at -O0; `addl (%rdx,%rax,4), %ebx` then `movl %ebx, (%rdx,%rax,4)` at -O2 |

Why each guarantee is exactly the one named:

* Compound assign needs exclusive access because the inventory says so in so
  many words: the lost-update window is closed by lock discipline, not by the
  instruction. The -O2 single-instruction shape changes nothing about that —
  without the `lock` prefix it is not an atomic form, so the lock around it
  carries the whole guarantee.
* Guarded compound assign needs exclusive access for the same reason plus one
  observation: the guard sits beside the sequence, not inside it. Both levels
  still show load, operate, store, so the guard refines when the sequence runs
  without ever merging it into one access.
* Relaxed merge-add needs single-writer-per-cell, the weakest sufficient
  guarantee in the menu: no lock, no atomic instruction, but the discipline
  exactly. Each core writes its own cell and only the merge loop reads, so no
  two writers ever share a torn middle. Break the discipline — two writers,
  one cell — and the sequence tears exactly as measured.

The atomic form is the standing graduation path for any refused row whose
discipline is unavailable: the compare-exchange row shows what it costs — a
`lock`-prefixed instruction with a declared ordering — and that cost is why
the disciplines above are worth keeping where they already hold.

## Open remainder

* Volatile register access (`*(volatile uintN_t *)(basis + off)`): no verdict
  in the inventory and therefore none here. Measuring it needs the device
  unit, a fourth unit outside the inventory's budget. Owned by a future lane.
* Architecture binding: every verdict above is x86_64-bound. A port to a
  weakly ordered architecture re-measures every atomar row, since release and
  acquire currently lower to plain moves.
* Level binding: slot `+=` crosses the single/sequence boundary between -O0
  and -O2. Any later ruling that cites the machine shape must name the level;
  this one names both, per row.
* Erhaltung feed: the ruling confirms witness material for the zuweisung,
  zusammZuweisung, atomar, and ruf rows of the Erhaltung table
  (`grammatik/Grammatik/Erhaltung.lean`, `tafel`); the fluechtig row stays
  open and is counted openly rather than silently.
* Count note: lane scope allows this one file only, so booked counts in
  TODO.md are the integrator's — the same arrangement as the inventory's
  guardian note, which this file joins rather than settles.
