# SYNTAX section draft: per-form atomicity — which emitted forms are single accesses (design only)

Status: DESIGN ONLY, no implementation. Worktree lane-93, base 536e118,
2026-09-10. Sources: `messung/TEARING-INVENTAR.md` (lane 47, base d162dfc)
for every assembler verdict, `messung/TEARING-RULING.md` (lane 70, base
c7dcd69) for every admission and refusal. No new measurements were taken in
this lane and none were needed: each machine shape below is copied from the
inventory's evidence block. Do NOT edit `dokumente/SYNTAX.md` from this
lane; a later lane moves the text.

## 1. Where the text goes

Recommended placement: a new subsection at the end of SYNTAX section 11
(Concurrency), after the race-discipline theorems table and its "There is
no third case" paragraph, before the `concurrent, effects, shared`
subsection. Reason: the table answers the question section 11 leaves open
— given that a conflicting pair is either happens-before ordered or on an
`atomic`, which emitted forms actually lower to one machine access, and
which lower to a sequence whose middle a concurrent observer can see.

Alternative placement, if the integrator prefers to keep section 11 to
Gabbro-side discipline: a new subsection 21.7 (Producer contract), with a
one-sentence pointer from section 21.4 (the ruling table). The ruling
already feeds the Erhaltung table rows zuweisung, zusammZuweisung, atomar,
ruf, and fluechtig, so either landing keeps the feed line short.

Section number and heading are the integrator's; the draft below uses a
placeholder number.

## 2. Draft prose for the new subsection

### 11.x Per-form atomicity — which emitted forms are single accesses

Section 11 proves properties of derivations: every access derives its
guard, every publication derives its pairing. What it does not say is what
the emitted C lowers to on the machine — whether one Gabbro statement
becomes one memory access, which no concurrent observer can tear, or a
sequence of accesses, whose middle it can. That mapping was measured on
three corpus units at two optimisation levels (inventory, lane 47) and
ruled (ruling, lane 70). The rule: a form is admitted as tear-free exactly
when the inventory shows a single machine memory access at both levels;
admission is never free, and each admitted row carries its price. A
sequence form is refused as self-sufficient and names the exact guarantee
that redeems it.

Bounds, stated once for the whole table: every verdict below holds on
x86_64 with GCC 16.2.1 at optimisation levels -O0 and -O2, and
nowhere else is claimed. A port to a weakly ordered architecture
re-measures every atomar row. The optimisation level can move a row across
the boundary — slot compound assign is the instance — so each row names
both levels. Only lock-prefixed instructions are atomic
read-modify-write in this table; a single non-locked read-modify-write
instruction is one instruction with two observable halves, a sequence in
consequence, not an atomic form.

Admitted — single access at both levels, with price:

| emitted C form | Gabbro source | machine shape, both levels | price of the admission |
|---|---|---|---|
| slot plain assign, `c->slots[s].benutzt = false;` | plain assign to a slot field | single movb store at -O0 and -O2 | aligned narrow store; one non-torn write, no ordering claim beyond it |
| shared global plain assign, `farbbericht = wert;` | plain assign to a static mut global | single movq store at -O0 and -O2 | eight byte alignment per the object record; one non-torn write, no read-modify-write atomicity, no ordering |
| atomic compare-exchange, `atomic_compare_exchange_strong_explicit` with release on success and acquire on failure | exchange with declared ordering | single lock cmpxchgl at both levels, result via sete | the declared ordering itself; a plain assign here would have been sequentially consistent by default, the named ordering is paid deliberately |
| release store and acquire load, `atomic_store_explicit` release and `atomic_load_explicit` acquire | publishes store and awaits load | single movb store and single movzbl load at both levels | x86 total store order plus the compiler barrier inside the builtin; no fence instruction emitted; re-measure on any weakly ordered arch |
| lock take and release, `KAPPEN_nimm();` and `KAPPEN_gib();` | locks block entry and exit | one call instruction per op at both levels; the release call is a tail jump at -O2 | atomicity lives outside the unit: the emitter writes only prototypes, the body is foreign |

Refused — sequence at one or both levels, with consequence:

| emitted C form | Gabbro source | machine shape | guarantee needed | what breaks without it |
|---|---|---|---|---|
| slot compound assign, `c->slots[s].marke += 1;` | compound assign on a slot field | load, operate, store sequence at -O0; single addl to memory with no lock prefix at -O2 | exclusive access; the atomic form is the upgrade path | lost update under concurrency; the -O2 single instruction narrows the window but does not close it |
| guarded compound assign, `o->slots[obj].zaehler -= 1;` under a lower-bound guard | compound assign inside a guard | load, operate, store triple at -O0; load, subl, store with the value reused by the following zero test at -O2 | exclusive access; the guard contributes nothing to atomicity | the same lost update as the unguarded form; the guard refines when the sequence runs without ever merging it into one access |
| relaxed merge-add, relaxed load then add then relaxed store | accumulates report path with merge add | load, add, store sequence at -O0; memory-operand add then store at -O2 | single-writer-per-cell: each core writes its own cell and only the merge loop reads | concurrent writes to one cell tear; a concurrent read of a cell mid-sequence sees the middle |

Why each guarantee is exactly the one named: compound assign needs
exclusive access because the inventory says so in so many words — the
lost-update window is closed by lock discipline, not by the instruction,
and the -O2 single-instruction shape changes nothing without the lock
prefix. Guarded compound assign needs it for the same reason plus one
observation: the guard sits beside the sequence, not inside it, at both
levels. Relaxed merge-add needs single-writer-per-cell, the weakest
sufficient guarantee in the menu: no lock, no atomic instruction, but the
discipline exactly — break it with two writers on one cell and the sequence
tears as measured. The atomic form is the standing graduation path for any
refused row whose discipline is unavailable: the compare-exchange row shows
what it costs, and that cost is why the disciplines above are worth keeping
where they already hold.

## 3. Open remainder (rides with the text, not against it)

Volatile register access, of the shape volatile-qualified dereference of
base plus offset, carries no verdict: none of the three measured units
emits a volatile site, and measuring it needs the device unit, a fourth
unit outside the inventory's budget. The Erhaltung table row fluechtig
therefore stays open, carried as an axiom by name, and this subsection must
count that openly rather than silently: the table above covers four of the
five fed rows (zuweisung, zusammZuweisung, atomar, ruf) and names the fifth
as unmeasured. Architecture and level bindings from section 2 repeat here
as obligations, not footnotes: any later lane that cites a machine shape
names the level, and any port names the arch and re-measures the atomar
rows.

## 4. Self-check (this lane)

`dokumente/SYNTAX.md` untouched (this file is the draft, placement
proposed in section 1). `crates/` untouched; no build was run in this lane,
full or otherwise; no emitter, checker, probe, or test change. English
prose throughout; table cells carry no bold numbers; no ebnf fences. Count
note: lane scope allows this one file only, so booked counts in TODO.md
are the integrator's — the same arrangement as the inventory's guardian
note and the ruling's count note, which this file joins rather than
settles.
