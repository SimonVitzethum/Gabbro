# SONDEN rows of lane-72: four date probes after lane-59's three

Lane-59 staged the probes for FRIST-SONDEN-NOTIZ.md rows 1-3 (`abnahme`,
`freigabe`, `byte_legen`) ahead of their obligations. This lane dates the
next four: the three fence rows 4-6 (`barriere`, `schreib_schranke`,
`speicher_schranke`, all class `P0`) plus one ring-zero row of measured
choice, row 11 (`schreiben`, class `P1`). Every probe below copies the
`sonde_tick` template unchanged (fixed seed, 1000 untimed warmup iterations,
LFENCE-bracketed RDTSC, p99 verdict, `--max-cycles 1` control that falls);
only the workload block differs per probe.

Bench for all numbers below: `Tux`, x86_64, 20 cores, `cc (GCC) 16.2.1`,
built with `cc -std=c11 -O2 -Wall -Wextra -Werror` (the runner's flags),
UBSan runs add `-fsanitize=undefined`. Binaries lived in `/tmp`, never in
the tree.

## The four probes: p99, booked tripwire, controls

N is 20000 over five runs each; checksums stable across all five runs of
each probe.

| probe | obligation | p99 across five runs | booked C | default | `--max-cycles 1` | UBSan |
|---|---|---|---|---|---|---|
| `sonde_barriere` | `frist_barriere_eingehalten` | `53, 59, 77, 77, 77` | `120` | exit `0` | exit `1` | exit `0`, no finding |
| `sonde_schreib_schranke` | `frist_schreib_schranke_eingehalten` | `33, 63, 63, 65, 65` | `96` | exit `0` | exit `1` | exit `0`, no finding |
| `sonde_speicher_schranke` | `frist_speicher_schranke_eingehalten` | `77, 77, 77, 77, 77` | `120` | exit `0` | exit `1` | exit `0`, no finding |
| `sonde_schreiben` | `frist_schreiben_eingehalten` | `893, 1093, 1168, 1186, 1251` | `1920` | exit `0` | exit `1` | exit `0`, no finding |

Margins, all read against the slow frequency mode (the bulks step between
two core-frequency modes run to run, as in lane-59): `77 -> 120` (ratio
`1.56`), `65 -> 96` (ratio `1.48`), `77 -> 120` (ratio `1.56`),
`1251 -> 1920` (ratio `1.53`). About half again above the worst measured
p99 in each case: clear of the bulk and of routine jitter, an order of
magnitude below anything a broken path could hide in. Checksums:
`42913250536966`, `42954178085256`, `42767317773259`, `2726416`.

Why `schreiben` is the measured choice: it is the only row of classes
`P1`/`P2` whose timed path executes on this bench. `seite_vergessen`
(`invlpg`), `ferne_kern_wecken` / `ausgeben` (`outb`) and `melden` (calls
out) fault in ring three; every `P2` row needs device memory on the bench.
A probe that cannot run stands at `77`, and a `77` probe has no falling
control. `schreiben` is a `write` supervisor call: the transition is real,
the bench's own kernel serves it, `laenge` stays zero so no byte is ever
written, and bulk-transfer cost is explicitly excluded in the header. The
register class below is `P4` (it runs in userland on the bench this folder
already has); the FRIST note's `P1` names the transition, whose estimate a
reader may dispute -- the reason it runs here is written into the probe.

## Deadline clauses added (N from costs, ten times)

`N = 10 * promised costs`, after the single precedent `zaehle_werte`
(`gabbro kosten`: computed `114`, promised `500`, booked deadline `5000`;
ratio `10.0` against promised, `43.9` against computed -- so the rule reads
against the promised number K001 holds the body against). The three fence
bodies and `schreiben` are `asm`, for which the checker computes nothing
(`0 bodies computed`), so promised is the only number and the same rule
applies uniformly: `1 ops -> 10 ops`. No checker rule holds the two numbers
against each other (`kosten.rs`, «SG-22»: different units, no conversion),
so the ten is a writer's booking, stated in each probe header and here.

| function | file and line | clause |
|---|---|---|
| `barriere` | `beispiele/60-annahme-mit-maschine.gab:56` | `deadline <= 10 ops arch x86_64 falsifier sonde_barriere` |
| `schreib_schranke` | `beispiele/67-befehlsebene.gab:43` | `deadline <= 10 ops arch x86_64 falsifier sonde_schreib_schranke` |
| `speicher_schranke` | `beispiele/67-befehlsebene.gab:55` | `deadline <= 10 ops arch x86_64 falsifier sonde_speicher_schranke` |
| `schreiben` | `beispiele/36-asm.gab:36` | `deadline <= 10 ops arch x86_64 falsifier sonde_schreiben` |

All three files check clean with the prebuilt binary at the base commit
(`0 errors`, measured 2026-09-10): the `beispiele/71` control stays clean
and the `gift/695` control still refuses with `K011`, so the binary says
yes and no in the right places. The emit of each file gains only the
assumption-header lines (`frist_*_eingehalten (assume): falsifier ...`,
the mechanism file 60's own header comment describes); no generated
instruction changes.

## Manifest derivation and the duplicate-name check

`gabbro annahmen` over the three files derives all four assumptions
(`frist_barriere_eingehalten`, `frist_schreib_schranke_eingehalten`,
`frist_speicher_schranke_eingehalten`, `frist_schreiben_eingehalten`).
They read `ungedeckt` (struck) until the assembly lists the four probe
names in `manifest::SONDEN_MIT_PROGRAMM` -- see the assembly moves below.

Duplicate names, against the `beispiele/43-gegenprobe.gab` pattern (one fn
name in two files, the map keeps the first): `barriere`,
`schreib_schranke` and `speicher_schranke` stand exactly once in the whole
non-poison tree. `schreiben` stands twice -- `beispiele/36-asm.gab:33`
(supervisor call, now dated) and `messung/proben/probe-zwei-gibibyte.gab:61`
(table slot write, no deadline, no arch) -- plus once under poison
(`gift/463`, excluded from every scan). Only the `beispiele/36` one carries
a deadline, so exactly one `frist_schreiben_eingehalten` exists and the
first-wins map never sees a second.

## EXACT rows to append (register numbers 40-43)

```
| 40 | **frist_barriere_eingehalten** | `sonde_barriere` | `P4` | **PROGRAM** |
| 41 | **frist_schreib_schranke_eingehalten** | `sonde_schreib_schranke` | `P4` | **PROGRAM** |
| 42 | **frist_speicher_schranke_eingehalten** | `sonde_speicher_schranke` | `P4` | **PROGRAM** |
| 43 | **frist_schreiben_eingehalten** | `sonde_schreiben` | `P4` | **PROGRAM** |
```

Parsed with the guardian's own `zeilen_der_tafel` before drafting: all four
match `ROW`. The register today parses to `39` rows at classes `P1 14`,
`P2 15`, `P3 4`, `P4 6` with `6` programs -- note the class table prints
`P2 16`, one above the parsed register; the assembly reconciles that stale
cell. After the append: `43` rows at `P1 14`, `P2 15`, `P3 4`, `P4 10`
with `10` programs.

## Quota recompute from the measured base

Base measured in this worktree before any change:
`pruefe-sondendeckung.py` prints `6 of 39`, `A_p = 0.1538` against booked
`6/39` and floor `1/8`, `ALL PASS`, exit `0`.

New state: covered `6 + 4 = 10`, denominator `39 + 4 = 43`.
`A_p = 10/43 = 0.2326` against floor `0.1250` (slack `0.1076`). Ratchet:
`10 * 39 = 390` against `43 * 6 = 258`, holds. Floor:
`10 * 8 = 80` against `43`, holds. Reachable: `10 + 0 = 10` (`P4` has no
open row left); `80` against `43`, holds. Missing probes: `43 - 10 = 33`,
unchanged in count (four obligations arrived with their probes).

New mark: `(10, 43)`.

## Assembly moves (this lane performs none of them)

1. Append the four rows above to `dokumente/SONDENDECKUNG.md`.
2. Move `MARK_QUOTE` in `instrumente/pruefe-sondendeckung.py` from
   `(6, 39)` to `(10, 43)`.
3. Enter the four probe names in `manifest::SONDEN_MIT_PROGRAMM`
   (alphabetical: after `sonde_boot_unerreichbar`, `sonde_schreib_schranke`
   and `sonde_schreiben` and `sonde_speicher_schranke` around
   `sonde_release_sichtbarkeit`/`sonde_tick`) and rebuild -- a cargo build
   this lane must not run.
4. Reword speech tooth seven: it drops the hardcoded four probes of
   2026-09-04 and expects the floor missed without them, but `6 of 43`
   without those four still meets it. Drop every `P4` program the register
   books instead (without all ten nothing is covered). Verified
   transiently in this worktree (edit, run, revert, no trace).
5. Recalibrate speech tooth eight: `range(30)` no longer outgrows the
   floor at `10 of 43` (reachable `10` against `43 + 30 = 73` still holds).
   `range(40)` does (`43 + 40 = 83 > 80`). Verified transiently the same
   way. A derived bound (`8 * reachable - n_ann + 1`) would not rot again.
6. Carry the prose numbers: `P4` rows `6 -> 10`, register `39 -> 43` rows,
   programs `6 -> 10`, missing `33 of 39 -> 33 of 43`, the floor paragraph
   (`6 / 39 = 0.1538` and its slack sentence), the class table's `P4` cell
   (plus the stale `P2 16` above), and the orphan-count snippet if it moves.

Measured intermediate states, so the assembly knows what to expect:
rows plus mark only (no list, no teeth): the speech test aborts at teeth
seven, eight and the control with exit `2`, printing no quota -- the known
abort shape, not a silent green. All six moves together (simulated
transiently, including the manifest list as source text): every one of the
nineteen speech teeth green, `10 of 43`, `A_p = 0.2326`, `ALL PASS`,
exit `0`. The one move the simulation cannot stand in for is the rebuild
in move 3: only a fresh binary carries the list outward.
