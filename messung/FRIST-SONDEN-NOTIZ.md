# Date-probe note: the missing dates, ordered

Status: open work, not a verdict. `beispiele/71-frist-und-zaehlung.gab`
dates one function (`zaehle_werte`, probe `sonde_tick`, sample currency);
every other costs-carrying function on a declared machine is dateless.
This note orders that remainder so the next date arrives with its probe,
the way `sonde_tick` did, instead of diluting the share.

## The count, and where it comes from

A `deadline` needs a machine (`K012`: a date on no machine floats), so the
census runs over the files that declare one:

```
beispiele/02-geraet.gab
beispiele/06-annahmen.gab
beispiele/07-eintritt-und-boot.gab
beispiele/11-grammatikbefunde.gab
beispiele/25-entrust.gab
beispiele/36-asm.gab
beispiele/57-faedenhalt.gab
beispiele/59-eintritt-nimmt-maskierte-sperre.gab
beispiele/60-annahme-mit-maschine.gab
beispiele/65-port-space.gab
beispiele/67-befehlsebene.gab
beispiele/71-frist-und-zaehlung.gab
```

```bash
grep -l ' arch ' beispiele/*.gab    # the 12 files above
# 29 distinct fn names with `costs <=` therein (text scan, 800-char window
# past each `fn name`, `extern` read from the prefix)
```

Of the `29`, one is dated (`zaehle_werte`, `deadline` beside `costs`);
`28` carry `costs` with no `deadline`. One of the `28`
(`uart_haengt`: `-> never`, `diverges` — a sample run never completes, so
no percentile ever materializes) is proposed `unfalsifiable` instead of
probed; the grammar keeps that tail legal and marked, and the manifest
entry carries the class so it never looks measured. That leaves `27`
missing date probes, which is the register below.

This settles the two counts the goal assessment books side by side
(`twenty-eight to go` beside `twenty-seven to go`): `28` dateless
functions, `27` probes after the one honest `unfalsifiable`.

## The classes

Borrowed from the probe quota file, restated for dates — a date probe
measures cycles on a machine, not truth of a sentence, so each class names
the bench the probe needs:

| class | meaning |
|---|---|
| `P0` | userland: the `sonde_tick` template applies as written — replicate the emitted shape, calibrate, book the tripwire |
| `P1` | ring zero: the timed path executes a privileged instruction or runs in supervisor context — a userland run faults (`77`) until a ring-zero bench exists |
| `P2` | device: the timed path touches device memory — without the device on the bench the probe stands at `77` |
| `P3` | no-emit: the timed body, or a mechanism it needs, is not emitted — a foreign body, a lock implementation the emitter only prototypes (`emit.rs` writes `void {n}_nimm(void);` and never defines it), a thread apparatus; timing a local stub would be an analogy, which the probe contract forbids |

`P0` is added deliberately: for assumptions the userland class is empty
and the floor says so, but for dates the userland work is not exhausted —
six rows below take the template as is. The classification is an estimate
per name and a reader may dispute any row; what is not an estimate is the
consequence column of the register.

## The register

Ordered by class, cheapest first: `P0`, then `P1`, then `P2`, then `P3`.
Numbers live in code spans only, so no counting guardian reads this file
as a register of measured values.

| # | function | file | costs | class | probe sketch |
|---|---|---|---|---|---|
| `1` | `abnahme` | `beispiele/06-annahmen.gab` | `4 ops` | `P0` | replicate the single global read; template as is |
| `2` | `freigabe` | `beispiele/06-annahmen.gab` | `4 ops` | `P0` | replicate the single global read; template as is |
| `3` | `byte_legen` | `beispiele/25-entrust.gab` | `2 ops` | `P0` | replicate the slot struct; fixed-seed refill; template as is |
| `4` | `barriere` | `beispiele/60-annahme-mit-maschine.gab` | `1 ops` | `P0` | fence executes in ring three; bracket and calibrate |
| `5` | `schreib_schranke` | `beispiele/67-befehlsebene.gab` | `1 ops` | `P0` | fence executes in ring three; bracket and calibrate |
| `6` | `speicher_schranke` | `beispiele/67-befehlsebene.gab` | `1 ops` | `P0` | fence executes in ring three; bracket and calibrate |
| `7` | `seite_vergessen` | `beispiele/67-befehlsebene.gab` | `1 ops` | `P1` | privileged invalidate; probe stands at `77` until ring zero |
| `8` | `ferne_kern_wecken` | `beispiele/67-befehlsebene.gab` | `1 ops` | `P1` | port write faults without privilege; ring-zero bench |
| `9` | `ausgeben` | `beispiele/36-asm.gab` | `1 ops` | `P1` | port write faults without privilege; ring-zero bench |
| `10` | `melden` | `beispiele/36-asm.gab` | `4 ops` | `P1` | calls out through the port write above; same bench |
| `11` | `schreiben` | `beispiele/36-asm.gab` | `1 ops` | `P1` | supervisor transition with no supervisor on the bench |
| `12` | `scharfschalten` | `beispiele/02-geraet.gab` | `1032 ops` | `P2` | needs the remapping registers on the bench |
| `13` | `warteschlange_scharf` | `beispiele/02-geraet.gab` | `16 ops` | `P2` | needs the queue in device memory, plus the foreign arm call |
| `14` | `used_lesen` | `beispiele/02-geraet.gab` | `4 ops` | `P2` | needs the queue in device memory |
| `15` | `bereit` | `beispiele/65-port-space.gab` | `2 ops` | `P2` | needs the serial line register on the bench |
| `16` | `leitungsstand` | `beispiele/65-port-space.gab` | `2 ops` | `P2` | needs the serial line register on the bench |
| `17` | `maske_setzen` | `beispiele/65-port-space.gab` | `2 ops` | `P2` | needs the interrupt register on the bench |
| `18` | `empfang_freigeben` | `beispiele/65-port-space.gab` | `4 ops` | `P2` | read-modify-write on the interrupt register; same bench |
| `19` | `sende` | `beispiele/65-port-space.gab` | `1026 ops` | `P2` | poll loop over the line register; bounded retry stays in the harness, the poll window is timed |
| `20` | `queue_arm` | `beispiele/02-geraet.gab` | `8 ops` | `P3` | foreign phase body; nothing emitted to replicate |
| `21` | `verteiler` | `beispiele/60-annahme-mit-maschine.gab` | `8 ops` | `P3` | foreign entry-context body; nothing emitted to replicate |
| `22` | `zaehle` | `beispiele/59-eintritt-nimmt-maskierte-sperre.gab` | `8 ops` | `P3` | lock acquire and release are prototypes only; exclude locks and say so, or build the lock bench first |
| `23` | `takt_verteiler` | `beispiele/59-eintritt-nimmt-maskierte-sperre.gab` | `40 ops` | `P3` | same lock as above; same choice |
| `24` | `bearbeite` | `beispiele/59-eintritt-nimmt-maskierte-sperre.gab` | `8 ops` | `P3` | ring lock is prototypes only; same choice |
| `25` | `ruf_verteiler` | `beispiele/59-eintritt-nimmt-maskierte-sperre.gab` | `40 ops` | `P3` | same lock as above; same choice |
| `26` | `halt_verteiler` | `beispiele/57-faedenhalt.gab` | `900 ops` | `P3` | needs the thread lock plus live threads; no thread bench |
| `27` | `alle_anhalten` | `beispiele/57-faedenhalt.gab` | `600 ops` | `P3` | halting threads needs threads; same bench as above |

`27` rows: `6` in `P0`, `5` in `P1`, `8` in `P2`, `8` in `P3`.
No row may stand twice, and a new `deadline` in any of the twelve files
adds a row here or it dilutes the share unseen.

## The template, for reuse

`sonden/sonde_tick.c` is the sample all `P0` rows copy and all other rows
adapt. Four properties make it a template rather than an example:

Fixed seed. The stimulus generator is a seeded shift register
(`SEED 0x71f8157dU`), reset before warmup and before the measured window,
so fresh contents every iteration and the same run twice. A checksum over
the observable output stands beside the verdict, so a re-run can check
that it measured the same distribution.

Fenced clock. Raw cycle counter bracketed by serializing fences on both
sides — not a calibrated wall clock, and said so. A warmup window of
untimed iterations precedes the measured window so the cold cache never
pays into the verdict. Core pinning is best-effort: failure prints a
warning and the run continues, noisier. Virtualization voids the numbers.

Verdict on the high percentile. Samples are sorted; ranks are nearest-rank
on the window length minus one. The maximum is scheduling tail and never
the verdict — the verdict reads the high percentile against the booked
tripwire. The booked tripwire sits about half again above the measured
percentile: clear of the bulk and of routine jitter, an order of magnitude
below anything a broken traversal could hide in. The tripwire is a
booking from calibration on one machine, not a conversion of the ops
date — ops and cycles share no conversion, and no rule holds the two
numbers against each other.

Control that falls. The probe takes a tripwire override; driven to one
cycle it must fall, and the default run must pass. The third state is
carried, not assumed: where the counter instruction faults, or the
architecture has none, the probe reports not-runnable instead of green.
A green run means not refuted here, this time, under this seed — and that
is all it means. Flaky red is a failed probe, not a failed date: re-run
before reading anything into it.

Calibration record of the sample, so every copy has a shape to match:

```
N=20000, warmup 1000 untimed, fixed seed, checksum stable across runs
min ~115 / p50 ~252 / p99 ~338, max noisy (scheduling tail)
five runs, p99 in {337,337,338,339,339}
booked C=512, default run exits 0, --max-cycles 1 exits 1, UBSan clean
built with cc -std=c11 -O2 -Wall -Wextra -Werror, same -O2 as the emit
```

Per class: `P0` copies the four properties unchanged. `P1` and `P2` keep
them and add the bench, with the not-runnable arm exercised the way the
counter-fault arm already is. `P3` either excludes the unemitted mechanism
from the timed window and says so in the header, the way the sample
excludes locks, or builds the missing bench first — timing a stub is an
analogy and stays forbidden. Every probe belongs to exactly one
obligation, carries a manifest entry with its class, and names a number
the pass can read on a machine the unit declares.

## Booked outside the register

Already dated: `zaehle_werte` (`beispiele/71`, `500 ops`, probe
`sonde_tick`) — the sample above, not a row below.

Proposed `unfalsifiable`: `uart_haengt` (`beispiele/65-port-space.gab`,
`1 ops`, `extern`, `-> never`, `diverges`). A date on a function that
never returns cannot be refuted by sampling: no run completes, so no
percentile materializes. Book the `unfalsifiable` tail with this reason
rather than a probe that can only ever hang or lie. If a reader disputes
the reason, the row moves into `P2` beside `sende`, whose exceeded-arm it
already serves — and the register grows back to `28`.
