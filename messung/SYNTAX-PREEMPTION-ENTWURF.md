# SYNTAX.md row draft: preemption timing excluded by decision

Status: DESIGN ONLY, no implementation. Worktree lane-94, base 536e118,
2026-09-10. Companion to `messung/PREEMPTION-ENTSCHEID.md`, which owns the
decision; this note owns the prose that `dokumente/SYNTAX.md` will carry.
Do NOT edit `SYNTAX.md` itself from this lane; a later lane moves the text
and proves against it.

Sources read for this draft, and no others:

- `messung/PREEMPTION-ENTSCHEID.md` (the decision: exclusion by decision,
  named assumptions, reopening conditions)
- `dokumente/SYNTAX.md` §16.2 (the table this row joins; read-only)

## 1. Proposed placement

A new final row in the §16.2 table of `dokumente/SYNTAX.md` — after the
`9. the three parameters` row (`SYNTAX.md:1347`), before the closing
paragraph that begins "So the answer to the question". In sequence it is
item 10. No existing row is touched. When the row lands, the closing
paragraph's enumeration, which today ends at (9), gains preemption timing
in cycles as the fourth outside item beside handler scheduling plus cost
model, the parser, and the three parameters; that one-sentence touch-up
belongs to the landing lane, not this one.

## 2. Draft row (paste-ready)

```markdown
| preemption timing | excluded by decision — no timing defs are introduced and no timing proofs are owed; the temporal cost of preemption, bus, and cache interference stays outside the model | logical placement stays modelled: preemption only between events, never inside one (Korngrenze, Unterbrechung.lean, discharged from Gesittet); while a thread holds a masking lock no foreign handler thread steps (MaskenOrdnung, run side of H102); one event covers at most one cell and executes indivisibly (EreignisAtomar, Koernung.lean); when a handler runs stays a scheduling fact (scheduling cut C1/C2); the sonde books its scope openly — counter body only, locks outside the bracket, p99 tripwire over one machine, sample not verdict (sonde_tick.c contract) |
```

The row fits the table's three columns (item, status, what carries it).
The status cell carries the exclusion, the third cell carries what stays
modelled and where each half lives.

## 3. What is excluded

Temporal cost, all of it: how long a masked section holds off a handler,
how many cycles one preemption adds, bus and cache interference, lock
acquire and release cost, scheduling latency, and any conversion between
ops and cycles. No hold-time definitions are introduced here, and no
timing proofs are owed here: the proof phase is separate, and there is
nothing in this decision for it to prove.

## 4. Why exclusion (bench limits, sample-vs-bound honesty)

A preemption-timing model would need exactly four things the tree refuses
to pretend it has. It would need a lock-inclusive workload, but the probe
provides no lock implementation, and timing a local stub would be an
analogy the probe contract forbids. It would need an isolated machine and
a calibrated clock, but the bench runs unisolated with a raw fenced TSC
that virtualization voids. It would need a verdict statistic over the tail
where preemptions live, but the verdict reads p99 precisely to look away
from the noisy max, and the calibration books that choice openly. And it
would need an ops-to-cycles conversion, but ops are not cycles and the
tree refuses the conversion, while a sample is not a verdict over all
inputs. Writing down hold-time definitions on top of this bench would
upgrade a falsifier sample into a fake worst-case bound. The honest move
is to book the boundary and stop.

This exclusion smuggles in no logical atomicity of transfers either.
Koernung proves the negatives openly: a multi-byte write is as many events
as bytes, never one; a multi-byte read records one event while folding
over many cells; and the two-byte tear is witnessed, not hypothesised. A
preemption CAN cut inside a logical multi-byte transfer. That cut is
placed by the grain model; its cost in cycles is what stays unmodelled.

## 5. What stays modelled

Logical placement, covered by five named assumptions from the decision
record:

| name | content | source |
|---|---|---|
| Korngrenze | every run step, handler or not, is one whole good event fitting its thread trace; preemption only between events | Unterbrechung.lean, discharged from Gesittet |
| MaskenOrdnung | while a thread holds a lock declared with masks irqs, no foreign handler thread steps | Unterbrechung.lean, run side of H102 |
| EreignisAtomar | one event covers at most one cell and executes indivisibly | Koernung.lean, holds of every event |
| Sonde scope | counter body only, locks excluded; cycles not ops; p99 tripwire over this machine; sample not verdict | sonde_tick.c header and contract |
| Scheduling cut | when a handler runs is a scheduling fact, quantified over runs where it did run; no priority levels | Unterbrechung.lean cuts C1 and C2 |

Happens-before coverage extends to handlers through lock release and
acquire edges, or the handler step is excluded upfront by masking. WHEN a
handler runs stays a scheduling fact outside the model. The booked
threshold is a tripwire over one machine's measured distribution, not a
derived bound: a green run says nothing about lock cost, by design.

## 6. What would reopen the decision

Any one of the following reopens it, and only one is needed:

1. A deadline that must be discharged as a proof rather than watched by
   a falsifier tripwire. A sample cannot carry a guarantee.
2. A handler with a hard latency requirement that must survive masked
   sections. That needs worst-case hold times, which need measuring.
3. Evidence that masked hold times or preemption tails dominate the
   measured distribution, for example a p99 or max shift attributable to
   preemption under a lock-inclusive workload.
4. A bench that can carry the model: isolated core, calibrated clock,
   lock-inclusive harness, and stated hold-time measurements with the
   same positive controls the current probe documents.

Until one of these holds, preemption, bus, and cache timing stay outside
the model by decision, and every green sonde line keeps meaning only what
its contract says: not refuted here, this time.

## 7. Self-check (this lane)

- `dokumente/SYNTAX.md` untouched; no Lean file added or changed; no
  build, no cargo, no Isabelle.
- This note is the only new file: `messung/SYNTAX-PREEMPTION-ENTWURF.md`.
- No ebnf fence anywhere in this file; no bold number in any table cell;
  prose is English throughout (Lean and probe names are code, not prose).
