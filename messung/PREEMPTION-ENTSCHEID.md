# Preemption timing: decision record

Decision: EXCLUDE the preemption / bus / cache timing model by decision.
No timing defs are introduced here, and no timing proofs are owed here:
the proof phase is separate, and there is nothing in this record for it
to prove.

Sources read for this decision, and no others:

- `grammatik/Grammatik/Unterbrechung.lean` (masking, handler-as-thread sentence)
- `grammatik/Grammatik/Koernung.lean` (grain premise, atomicity boundary, negatives)
- `sonden/sonde_tick.c` (locks-excluded cycle measurement, noise honesty)

## What is modelled, and what is not

Modelled is logical placement: preemption happens only between events,
never inside one (Korngrenze), and while a thread holds a masking lock no
foreign handler thread takes a step (MaskenOrdnung). Happens-before
coverage extends to handlers through lock release/acquire edges, or the
handler step is excluded upfront by masking. WHEN a handler runs stays a
scheduling fact outside the model.

Not modelled is temporal cost: how long a masked section holds off a
handler, how many cycles one preemption adds, bus and cache interference,
lock acquire/release cost, scheduling latency, and any conversion between
ops and cycles. The sonde measures the counter body only; locks are
outside its bracket by design, and a green run says nothing about lock
cost. The booked threshold is a tripwire over one machine's measured
distribution, not a derived bound.

## Why exclusion, in cycles-grade terms

A preemption-timing model would need exactly the four things the tree
refuses to pretend it has. It would need a lock-inclusive workload, but
the probe provides no lock implementation and timing a local stub would be
an analogy the probe contract forbids. It would need an isolated machine
and a calibrated clock, but the bench runs unisolated with a raw fenced
TSC that virtualization voids. It would need a verdict statistic over the
tail where preemptions live, but the verdict reads p99 precisely to look
away from the noisy max, and the calibration books that choice openly.
And it would need an ops-to-cycles conversion, but ops are not cycles and
the tree refuses the conversion, while a sample is not a verdict over all
inputs. Writing down hold-time defs on top of this bench would upgrade a
falsifier sample into a fake worst-case bound. The honest move is to book
the boundary and stop.

This decision does not smuggle in logical atomicity of transfers either.
Koernung proves the negatives openly: a multi-byte write is as many events
as bytes, never one; a multi-byte read records one event while folding
over many cells; and the two-byte tear is witnessed, not hypothesised.
A preemption CAN cut inside a logical multi-byte transfer. That cut is
placed by the grain model; its cost in cycles is what stays unmodelled.

## Named assumptions covering the edge

| Name | Content | Source |
|---|---|---|
| Korngrenze | every run step, handler or not, is one whole good event fitting its thread trace; preemption only between events | Unterbrechung.lean, discharged from Gesittet |
| MaskenOrdnung | while a thread holds a lock declared with masks irqs, no foreign handler thread steps | Unterbrechung.lean, run side of H102 |
| EreignisAtomar | one event covers at most one cell and executes indivisibly | Koernung.lean, holds of every event |
| Sonde scope | counter body only, locks excluded; cycles not ops; p99 tripwire over this machine; sample not verdict | sonde_tick.c header and contract |
| Scheduling cut | when a handler runs is a scheduling fact, quantified over runs where it did run; no priority levels | Unterbrechung.lean cuts C1 and C2 |

## What would reopen this decision

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
the model by this decision, and every green sonde line keeps meaning only
what its contract says: not refuted here, this time.
