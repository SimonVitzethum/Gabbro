# MUSE-REPORT-1215: From W runs to the GX refinement (the missing target leg)

## What was done

New file `grammatik/Grammatik/X86/TsoGxRefine.lean` (+ one `import
Grammatik.X86.TsoGxRefine` line appended to `grammatik/Grammatik.lean`).
Follow-up of lane 1187 (`TsoRunInduction.lean`): bridged lowered-fragment
traces yield W runs; this lane states and proves the GX refinement
consuming those runs for shared atomic carriers.

### New definitions / theorems (all in `Gabbro.Grammatik.X86`)

- `gxSchrittAusG`: every G step is a GX step, any `Tg` (accepted
  `gx_aus_g` named for the fragment consumer).
- `gxLaufAusG`: every G run is a GX run, any `Tg` (accepted
  `gx_aus_g_lauf`).
- `brueckenSchrittGx`: a `BrueckenSchritt` from a W machine reached from
  the weak start over a G start refines to a `RufSchrittGX` step, and the
  presented memory IS G's memory outside `Tg` (accepted `schwach_ist_gX`
  applied to the step's `RufSchrittW`). The DRF/checker premises stay
  explicit.
- `brueckenLaufGx`: a start-anchored `BrueckenLauf` yields a reached
  `RufErreichbarGX` run (induction; prefix reachability via
  `brueckenLauf_erreichbar`).
- `geteiltVAtomar`: `GeteiltV` carries `AtomarAusgenommen` (`h.1.1`).
- `brueckenLaufGxGeteilt`: the run refinement over exactly the admitted
  shared atomics `GeteiltV P ws` (needs `[DecidableEq D.Fn]`).
- `havocLaesstPlain`: no `HavocA` environment touches a non-admitted
  carrier (accepted class unpacked).
- `lockBeiWeiterleitungVerweigert`: a core forwarding a byte (pending own
  entry) refuses every LOCK XADD step (`neuestens_jüngste` split +
  accepted `tsoRmw_puffer_bleibt_verweigert`).
- `gxLockLaenge`: `laengeOk 9 = true` (witness length, `decide`).
- `gxSchrittAusG_zeuge`: joint witness -- concrete G step (`0 → 42`,
  `witM` bytes change), its GX embedding over `GeteiltV ctProg []`,
  reached one-step GX run, `ErbtW`, reached trace with two timestamps,
  foreign byte outside footprint, stale divergence (owner-only
  forwarding), two-core changed memory (`spurW`).
- `lockBeiWeiterleitungVerweigert_zeuge`: joint witness -- `setTso
  hwWitStart ctS4` (well-formed) forwards seven at `ctF` on core 1 while
  core 0 reads zero, LOCK XADD refused.
- Local instance `DecidableEq witD.Fn` (via `Unit`, the Korpus07 pattern).

### Verification

- `./lean-probe`: `== 0 error(s)`, exit 0.
- `./lean-bau`: `Build completed successfully (640 jobs).` (last line).
- `#print axioms`: every main theorem depends only on a subset of
  `[propext, Classical.choice, Quot.sound]` (standard); `gxLockLaenge`
  on none.

## What remains open (exact remaining obligation, also in CUTS)

1. Discharging the DRF/checker premises (`GutO`, `AbgK`, `FussSX` over
   `GeteiltV`, `StartExklusiv`) for a lowered program -- the checker side.
2. A start-anchored bridged run: the fragment head must first be REACHED
   from `RufStartG` by entry/call prefix execution, which the three
   bridged kinds do not cover. Hence no joint `_zeuge` for
   `brueckenLaufGx`/`brueckenLaufGxGeteilt` yet -- reported as a finding
   per rule 13, not weakened around (the witness program `ctProg`
   returns immediately, so its start can never reach the hand-placed
   fragment head; a program whose body contains the fragment plus entry
   execution is new work).
3. Assembling a `SchrittW` with the `rmw` field from an admitted LOCK
   step (all parts present: `tsoRmw_xadd_einzel_rmw`,
   `tsoRmw_kein_split`, `tsoRmw_kette_ohne_verlust`, lowering
   certificate still to be linked).
4. `valX86_sound`; scheduling, fairness, progress, timing; interrupts,
   devices, MMIO, DMA.

## Where the task text is wrong or inapplicable

- The MECHANISM paragraph asks for "your family's event type and a
  `HwAdapter` (or an extended step relation)". There is no new hardware
  family here: the consumer is machine GX, not `HwMaschine` (same reason
  lane 1187 claims no `HwAdapter` for W). Defining a fresh adapter would
  duplicate the accepted `tsoRmwAdapter`, against rule 16. I reused it
  for the LOCK leg and defined no adapter; the deviation is documented
  in the file's CUTS.
- The witness clause "(4)" is written for hardware-family lanes (two
  cores "where the family touches memory"). Applied to this lane: the GX
  leg is one step (only one concrete G step exists); the consumed TSO
  evidence is multi-step (8-flush drain + foreign issue, two-core
  `spurW`). A multi-step GX-run witness needs item 2 above.
- `Speicher` unqualified resolves to the X86 byte memory in this
  directory; source memory must be `Gabbro.Grammatik.Speicher D`
  (two stain-removal edits). `GeteiltV` needs `Grammatik.Zielsatz.Spec`
  imported plus `[DecidableEq D.Fn]`.
