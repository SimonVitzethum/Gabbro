# Device-DMA memory-model note: assumptions and litmus probe plan

Status: NOTE ONLY, no implementation. Lane 16, base 291c27b, 2026-09-10.
It records which assumptions the CPU-device seam rests on and which probes
would falsify them. Nothing here changes the checker, the axiom layer, or any
number booked elsewhere.

## 1. Assumption list

The seam has no mechanised model to follow: for the MMU there is prior work,
for DMA devices there is none (see `dokumente/BEWEIS.md`, L2). What stands in
its place is a short list of named assumptions; each row states the claim and
the falsifier state.

| id | claim | falsifier state |
|---|---|---|
| A10 visibility (`release_stellt_sichtbarkeit_her`) | A release store makes every previously written payload word visible to a reader that loads the same cell with acquire. | booked unfalsifiable: a passing run shows only that the reorder stayed away this time (`messung/RACE.md` section 5, `messung/AXIOMSCHICHT.md`). |
| atomic disjunct (`geraeteregister_veroeffentlicht_wie_ein_atomic`) | A volatile store to a device register publishes the previously written payload to the device once the register write lands; on the atomic branch the machine orders. | falsifier `sonde_virtio_avail`, named in `beispiele/06-annahmen.gab`. Side note: a disjunction probe that establishes one side discharges the assumption rightly but does not report which side (`messung/ANNAHMEKONJUNKTIONEN.md`). |
| HB edges only (program order plus lock sync) | Happens-before has two edges: program order and release-L to acquire-L on a lock. A `publishes`/`awaits` pairing without a lock is no synchronisation edge. | structural premise, not probed by execution; matches race forms 17 and 22 in `messung/RACE.md` and section 2 of `messung/ZIEL-BEWERTUNG-2026-09-10.md`. |
| `c11_release_acquire_x86` | C11 release/acquire visibility as observed on x86_64. | litmus falsifier MP/SB/LB, planned in section 2. |
| `c11_release_acquire_aarch64` | C11 release/acquire visibility as observed on aarch64. | litmus falsifier MP/SB/LB, planned in section 2; aarch64 stays sealed, so the aarch64 arm is named expectation only, never a program. |
| `dma_visibility_in_order` | CPU-device races fall entirely under this name: two volatile accesses become visible to the device in program order. | order probe, planned in section 2. |
| `dma_kohaerent` | Device and core see the same cells without cache maintenance. | coherence probe, planned in section 2. Split off on 2026-08-31 from the old conjunction that carried both claims under one name (`messung/ANNAHMEKONJUNKTIONEN.md`). |

Scope notes:

- The model choice behind the `c11_*` pair is RC11 without SC, and the choice
  is less load-bearing than it looks: what the tree claims is RMW atomicity
  plus per-address coherence, identical in all candidate models
  (`dokumente/BEWEIS.md`, L2).
- The order half does not hold on aarch64 for C11 volatile without a DSB: a
  descriptor write to coherent RAM followed by a doorbell write to the device
  can become visible out of order. The aarch64 tree stays sealed in this
  folder; what `arch` makes sayable is only that the assumption does not hold
  there (`messung/ANNAHMEKONJUNKTIONEN.md`).
- A device is no thread: CPU-DMA pairs never enter the declared-concurrency
  check (`messung/NEBENLAEUFIGKEIT-ENTWURF.md`); they rest on this list alone.

## 2. Litmus probe plan

Each litmus ships as check plus counterprobe: one arm whose outcome the
assumption forbids, and one positive-control arm that fires repeatedly to prove
the harness can observe the reorder at all. The form is taken from
`sonden/sonde_release_sichtbarkeit.c`, which pairs its falsifier arm with a
recorded positive control.

| litmus | arch | check arm (forbidden under the assumption) | counterprobe (must fire) | state |
|---|---|---|---|---|
| MP (message passing) | x86_64 | flag seen set while payload reads stale | control with payload pre-published, flag read observed set | missing |
| MP (message passing) | aarch64 | same forbidden outcome, barriered form | expectation only, sealed, no program | missing |
| SB (store buffering) | x86_64 | both loads read the old value after both stores | single-thread interleaving that exhibits the stale read | missing |
| SB (store buffering) | aarch64 | same forbidden outcome, barriered form | expectation only, sealed, no program | missing |
| LB (load buffering) | x86_64 | both loads read the new value (addressing intact) | control exhibiting the fresh read | missing |
| LB (load buffering) | aarch64 | same forbidden outcome, barriered form | expectation only, sealed, no program | missing |
| DMA order (`sonde_dma_reihenfolge`) | x86_64 | descriptor write then doorbell write observed in order at the device | unbarriered variant observed out of order | named, no program |
| DMA coherence (`sonde_dma_kohaerenz`) | x86_64 | device reads back the core-written cell with no cache maintenance | known-pattern DMA read proving the harness observes device reads at all | named, no program |

Plan items beyond the table:

- Keep the two DMA probes observably distinct: today nobody asserts that the
  order probe and the coherence probe measure different things (N024 holds one
  name per duty, not distinctness of duties). Run both against one harness and
  record where they disagree.
- Land the x86_64 litmus probes as C programs under `sonden/` with the
  check-plus-counterprobe shape; keep the aarch64 column as named expectation
  so the sealed tree is described, not entered.

## 3. What stays unmeasured

- No aarch64 programs: the aarch64 column is expectation, never a probe.
- Direction caveat shared with A10: a green DMA probe shows the reorder stayed
  away on this run; it does not refute the model. Same directionality as
  `release_stellt_sichtbarkeit_her`.
- Counts booked elsewhere stand: assumption totals, probe coverage numbers,
  and the axiom-layer reach are untouched. This note adds names for planned
  probes, not probes.
