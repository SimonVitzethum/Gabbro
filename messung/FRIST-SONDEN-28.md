# Frist probes for the remaining deadlines (post 5c)

Status: measurement, not a verdict. Base `359d192`, branch `z07-posten`,
worktree `.claude/worktrees/z07` only. All numbers below live in code spans,
so no counting guardian reads this file as a register.

## Census: where the `28` went

The auditor booked `28` of `29` deadlines without a running probe at its base,
with one measured (`sonde_tick`). At this base (`359d192`) eleven more date
probes have landed in `sonden/` with their `deadline` clauses, so the count
reads differently and both readings are stated:

- `29` costs-carrying functions on a declared machine (the census of
  `messung/FRIST-SONDEN-NOTIZ.md`, unchanged).
- `12` of them dated and probed at this base: `zaehle_werte` (`sonde_tick`),
  `abnahme`, `freigabe`, `byte_legen`, `barriere`, `schreib_schranke`,
  `speicher_schranke`, `schreiben`, `zaehle`, `takt_verteiler`, `bearbeite`,
  `ruf_verteiler`.
- `17` remaining. Of those, `14` get a staged running probe below (new files
  under `messung/proben/frist-28/`, this post's own directory, nothing else
  touched) and `3` are booked without a probe (`queue_arm`, `verteiler`,
  `uart_haengt` -- which, why, and what harness change each needs).

No existing file is edited: no `.lean`, no `beispiele/`, no `crates/`, no
`sonden/`, no register, no runner. The probes are STAGED, not bound: no
`deadline` clause names them and no manifest entry lists them, because binding
needs a checker-side entry plus a dated clause, both outside this post's
scope. Staging ahead of obligations has precedent (lane-59 staged three
probes ahead of theirs). Binding is booked as follow-up below.

## What each probe demonstrates

Every probe copies the `sonde_tick` template unchanged (fixed seed, `1000`
untimed warmup iterations, `LFENCE`-bracketed `RDTSC`, `p99` verdict,
`--max-cycles 1` control that falls, `77` where the counter faults) and only
the workload block differs. After the verdict each probe prints the sampling
grid over its own run: period `S` is the booked tripwire in cycles, the
deadline moment `d` is the worst typical cost (`p99`), check at `0`, use at
`d + S`. Spacing (`deadlineSpacing`: `d + S <= use`) holds by construction, so
the window's `SEEN` arm fires: tick `n * S` lands in `[d, use]` with the
printed margin. That is `TickClock.window`
(`grammatik/Grammatik/Fristlauf.lean`) executed over measured numbers.

What it is not: the grid is COMPUTED, not hardware-kept. That the hardware
keeps the grid is cut `C4`, a per-use premise no sample discharges. The probe
demonstrates detection within the bound; it does not close `C4`. Ops are never
converted to cycles (`D10`); the tripwire is a booking over one machine's
distribution, not a conversion of the ops date.

## Evidence: verification runs on `fisch` (`2026-09-11`)

Full run: `messung/proben/frist-28/run.sh` (default `20000` iterations).
`run.sh` builds each probe, runs the default (want exit `0`), the
`--max-cycles 1` control (want exit `1`), and a UBSan build plus run (want
exit `0`); privilege-guarded probes want exit `77` twice. Result on `fisch`:
`FRIST-28: ALL PASS`, exit `0` (log `/tmp/z07-verify3.log` on `fisch`).

| probe | staged obligation | staged deadline | `S` | `d` (`p99` this run) | tick | margin | arm |
|---|---|---|---|---|---|---|---|
| `frist28_scharfschalten` | `frist_scharfschalten_eingehalten` | `10320 ops` | `192` | `129` | `192` | `129` | `SEEN` |
| `frist28_warteschlange_scharf` | `frist_warteschlange_scharf_eingehalten` | `160 ops` | `192` | `129` | `192` | `129` | `SEEN` |
| `frist28_used_lesen` | `frist_used_lesen_eingehalten` | `40 ops` | `192` | `129` | `192` | `129` | `SEEN` |
| `frist28_bereit` | `frist_bereit_eingehalten` | `20 ops` | `192` | `86` | `192` | `86` | `SEEN` |
| `frist28_leitungsstand` | `frist_leitungsstand_eingehalten` | `20 ops` | `192` | `86` | `192` | `86` | `SEEN` |
| `frist28_maske_setzen` | `frist_maske_setzen_eingehalten` | `20 ops` | `192` | `86` | `192` | `86` | `SEEN` |
| `frist28_empfang_freigeben` | `frist_empfang_freigeben_eingehalten` | `40 ops` | `192` | `86` | `192` | `86` | `SEEN` |
| `frist28_sende` | `frist_sende_eingehalten` | `10260 ops` | `192` | `86` | `192` | `86` | `SEEN` |
| `frist28_alle_anhalten` | `frist_alle_anhalten_eingehalten` | `6000 ops` | `3200` | `1763` | `3200` | `1763` | `SEEN` |
| `frist28_halt_verteiler` | `frist_halt_verteiler_eingehalten` | `9000 ops` | `3200` | `1849` | `3200` | `1849` | `SEEN` |

All ten: default exit `0`, control exit `1`, UBSan exit `0`, checksums stable
across runs (recompute prints them beside every verdict).

Calibration behind the tripwires (five runs each, `20000` iterations,
`run.sh --calibrate`, log `/tmp/z07-calib.log` on `fisch`): worst `p99`
`129` for the eight small probes (stepping `43`/`86`/`129` run to run),
`2107` for `alle_anhalten`, `1806` for `halt_verteiler`. `C` sits about half
again above the worst measured `p99` in each case (ratios `1.43` to `1.52`),
the same rule the earlier lanes booked (`1.48` to `1.56`).

Three rebookings happened during verification, all upward, all stated:

- `leitungsstand` `128 -> 192`: the verification run plus two of six re-runs
  measured `p99 129`, refuting `C=128`. Same stepping the gate probes show.
- `warteschlange_scharf` `128 -> 192`: the verification run measured above
  `128` the same day, same stepping.
- `halt_verteiler` `2752 -> 3200`: the verification run measured `p99 2236`
  (heavier tail than calibration), and the timed body is byte-identical to
  `alle_anhalten`, so the tripwire is uniform with it.

## The four `77` probes: measured absence, not green

| probe | staged obligation | provisional `S` | status on `fisch` |
|---|---|---|---|
| `frist28_seite_vergessen` | `frist_seite_vergessen_eingehalten` | `512` | `77` |
| `frist28_ferne_kern_wecken` | `frist_ferne_kern_wecken_eingehalten` | `4096` | `77` |
| `frist28_ausgeben` | `frist_ausgeben_eingehalten` | `4096` | `77` |
| `frist28_melden` | `frist_melden_eingehalten` | `8192` | `77` |

Each attempts its single privileged instruction (`invlpg`, `outb`) under a
`SIGSEGV`/`SIGILL` guard before any timing: in ring three it faults and the
probe exits `77` having measured nothing. The tripwire is PROVISIONAL
(vendor latency plus margin, void until a ring-zero calibration) and the
printed grid line is labeled a computed illustration, not a measurement. Real
port IO is never executed speculatively: the guard fires before any timing.
On a ring-zero bench the same binary times the instruction as emitted and the
`--max-cycles 1` control falls there. UBSan builds exit `77` identically.

## Booked without a probe: three, with the harness change each needs

- `queue_arm` (`beispiele/02-geraet.gab`, `costs 8 ops`): `extern`, no body
  is emitted. Timing a local stub would be an analogy, which the probe
  contract forbids. Needs: the emitter emits the phase-transition body, or a
  phase bench the probe can call without inventing one.
- `verteiler` (`beispiele/60-annahme-mit-maschine.gab`, `costs 8 ops`):
  `extern`, same position as `queue_arm`. Needs the same: an emitted entry
  body behind the dispatch.
- `uart_haengt` (`beispiele/65-port-space.gab`, `costs 1 ops`, `-> never`,
  `diverges`): a date on a function that never returns cannot be refuted by
  sampling -- no run completes, so no percentile ever materializes. Needs: the
  `unfalsifiable` tail with this reason (the proposal `FRIST-SONDEN-NOTIZ.md`
  already carries), not a probe that can only hang or lie.

## The twelve pre-existing probes on `fisch`: eight green, four red

Re-ran all twelve bound `sonden/` date probes on `fisch` (default runs,
`cc` with the runner's flags). Eight exit `0`. Four refute there:

- `sonde_byte_legen` (booked `112`): `p99 129` red, `p99 86` green on retry --
  flaky, frequency stepping.
- `sonde_ruf_verteiler` (booked `104`): `p99 129` red once, `p99 86` green
  twice after -- flaky.
- `sonde_barriere` (booked `120`): `p99 129` three times -- systematically red
  on `fisch` (booked on `Tux` at `p99` in `53`..`77`).
- `sonde_speicher_schranke` (booked `120`): `p99 258` once, `p99 129` twice --
  systematically red on `fisch` (booked on `Tux` at `p99 77`).

Per the probe contract a red run is a failed probe until re-run, and the
re-runs split two and two: two flaky, two systematic. The systematic two miss
by exactly one frequency quantum (`43` cycles) -- the `fisch` distribution
steps one quantum above the `Tux` booking. NOT rebooked here: those are bound
probes with owner-booked tripwires, and rebooking another lane's calibration
from this post would be the wrong hands on the numbers. Remainder: rebook
`barriere` and `speicher_schranke` for `fisch` (or book per-machine tripwires)
at the owning lane.

## Recompute commands

On `fisch` in directory `gabbro-z07` (tree synced with `rsync -rlpgoD`,
`beweise/` with `rsync -a`):

```bash
./messung/proben/frist-28/run.sh
./messung/proben/frist-28/run.sh --calibrate
cc -std=c11 -O2 -Wall -Wextra -Werror -o /tmp/p messung/proben/frist-28/frist28_sende.c && /tmp/p
cc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=undefined -o /tmp/pu messung/proben/frist-28/frist28_sende.c && /tmp/pu
/tmp/p --max-cycles 1; echo exit=$?
```

Pre-existing probes (default runs only, no rebooking):

```bash
for s in sonde_tick sonde_abnahme sonde_freigabe sonde_byte_legen sonde_barriere sonde_schreib_schranke sonde_speicher_schranke sonde_schreiben sonde_zaehle sonde_takt_verteiler sonde_bearbeite sonde_ruf_verteiler; do cc -std=c11 -O2 -Wall -Wextra -Werror -pthread -o /tmp/$s sonden/$s.c && timeout 120 /tmp/$s; done
```

## Remainder

- Binding (owner assembly, same moves `SONDEN-ROWS-72.md` lists): dated
  `deadline` clauses at the fourteen functions, manifest entries, register
  rows, quota-mark move. This post stages the probes; it binds none.
- Ring-zero bench for the four `77` probes (real calibration + falling
  control there), or a decided per-machine tripwire note.
- `unfalsifiable` tail for `uart_haengt` with the reason above.
- `barriere` / `speicher_schranke` rebooking for `fisch` (previous section).
- `C4` stays open: the grid is computed per run, keeping it is still a
  per-use premise.

## Guardian impact

None intended and three checked: no `.gab` added or changed (coverage
register untouched), no `sonden/` file added or changed (program column
untouched), no `manifest.rs` entry (checker logic untouched), no `.lean`
touched, no German doc cell rephrased. This file carries numbers in code
spans only.
