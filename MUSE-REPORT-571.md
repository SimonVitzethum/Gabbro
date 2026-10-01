# MUSE-REPORT-571: Entry state, image permissions and user binding duties

## What was done

New file `grammatik/Grammatik/X86/EntryExecution.lean` (owned) plus the
additive umbrella import in `grammatik/Grammatik.lean`. It connects the
accepted entry admission (`EntryState.eintrittOk` over the checked `Bild`
mapping) and caller-gate admission (`GateStub`/`ValidatorSkeleton.valTore`)
to executed-memory consequences, with the actual generic source duties
reused and a jointly witnessed reached source run.

Definitions:

- `eintrittZulassung`: joint x86 admission `Bool` (checked image mapping
  AND entry state AND every listed caller gate).
- `zulassungSpeicher`, `zeugenEintrittAusf`: witness memory/entry state on
  the minimal accepted image `valZeuge` (one `ret` byte) with a stack
  window `[0x7000, 0x8008)` covering the checked word below the top and
  the word the `ret` pops; `ausfuehrbar` comes from the checked image
  only, so the stack is never executable.
- `torRuferPflicht`: the generic `AufruferPflicht` reused (not restated)
  as the caller-side binding-duty consumer interface.

Theorems (all premises used; no conclusion restates a premise):

- `zulassung_wohlgeformt`, `zulassung_eintritt`: admission projections.
- `zulassung_rip_ausfuehrbar`: RIP executable through the CHECKED loaded
  mapping (`geladen`), not the state's own permission function.
- `zulassung_stapel_rw`: entry stack word below `rsp` readable/writable.
- `zulassung_erster_schritt`: from admission plus a fetched/decoded
  instruction that steps, the RIP is mapping-executable AND the real
  `byteschritt` runs (reuses `byteschritt_weiter`; no second executor).
- `find?_tupel_mem` (auxiliary, proved by induction): a pair the table
  search returns is a member with a true predicate.
- `tor_grund_im_kanal`: a raw answer decoding to a reason through an
  admitted gate's table names a reason inside the declared channel
  (`g < t.gruende`); kernel meaning of the table stays user logic.
- `valTore_verweigert_bei`, `zulassung_verweigert_unlisted`,
  `zulassung_verweigert_tor`: generic refusals (refused gate member,
  unlisted RIP).
- Witnesses: `zulassung_zeuge_ok` (admission, `decide`),
  `zulassung_fetch_ret` (fetch sees exactly `ret`, `decide`),
  `zulassung_schritt_ret` (step runs to RIP 0 via `ausgangRip`,
  `decide`), `zulassung_fremd_verweigert` (unlisted RIP, `decide`),
  `zulassung_abi_verweigert` (clobbered-out gate, `decide`),
  `tor_grund_im_kanal_zeuge` (all channel-link premises jointly
  instantiated), `eintrittAusf_zeuge` (main joint witness: admitted
  entry, fetched `ret`, executed step, reached non-degenerate source
  run with `ReqAmEintritt` at its actual place from
  `vertragStandort_lauf_zeuge`, real x86 memory change from
  `write_read_zeuge`).

## Last check results

- `./lean-probe grammatik/Grammatik/X86/EntryExecution.lean`:
  `== 0 error(s)`, all axioms within `[propext, Classical.choice,
  Quot.sound]`; the joint witness uses exactly the standard goal set.
- `./lean-bau`: `Build completed successfully (428 jobs)`.
- Goal files untouched, so no goal-axiom drift from this lane
  (new file's maximum is exactly the standard triple).

## What remains open

See the `CUTS:` block in the file. In short: source-to-entry lowering
(IR lane 287 / QUELLBRUECKE) and the async interrupt model stay open;
`torRuferPflicht` is stated, not jointly instantiated (fixture `eD`
has `Ax := Empty`, so no gate inhabitant exists -- recorded honestly);
single-step scope only (witness `ret` pops to unlisted RIP 0);
callee-side obligation (c), hardware, and cost/time claims untouched.

## Producer/consumer interface and next integration

- Produces for the lowering/integration owner: `eintrittZulassung`
  (decided x86 admission), `zulassung_erster_schritt` (admission to
  running first byte step), `tor_grund_im_kanal` (decoded reason inside
  the declared channel), `torRuferPflicht` (caller precondition the
  gate lowering must discharge at actual values).
- Consumes, unchanged: `Bild`, `EntryState`, `GateStub`,
  `ValidatorSkeleton.valZeuge`/`valTore`, `Byteschritt`,
  `VertragOrtB.ReqAmEintritt`, `FremdRuf.AufruferPflicht`,
  `ContractSites.vertragStandort_lauf_zeuge`.
- Measurable next step: whoever proves source-to-entry lowering can
  conjoin an actual emitted-bytes claim to `eintrittZulassung` and
  extend `eintrittAusf_zeuge`; multi-step entry legs can build on
  `zulassung_erster_schritt`.

## Task feedback

Nothing in the task appears wrong. One clarification worth keeping:
the "user binding duties" half splits into an instantiable part
(`ReqAmEintritt`, jointly witnessed from the reached run) and a
stated-only part (`AufruferPflicht`, no fixture inhabitant since
`eD.Ax` is empty) -- the file records both instead of forcing a
degenerate witness.
