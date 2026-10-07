# Agent 06 report — executions from instruction traces

## Done
- Read frozen vocabulary `arm/Arm/Mem/Event.lean` (`Ev`, `Rel`, `Exec`) and
  `arm/Arm/Isa/Monad.lean` (`Eff` tree); Sail citations fixed: memory effects
  `__ReadMem`/`__WriteMem` are `sail-arm/arm-v9.4-a/src/mem.sail` lines 44-57,
  the event interface is `sail/lib/concurrency_interface/read_write.sail`,
  barriers are the `Barrier` union of
  `sail-arm/arm-v9.4-a/src/interface.sail` lines 166-189.
- Skeleton `arm/Arm/Mem/Trace.lean`: `Trace` (core, events, addr/data/ctrl),
  `Trace.po` (earlier-before-later pairs); wired into `arm/Arm.lean`.
- Build: `./arm-bau` exit 0, 0 errors (7 jobs).

## Open
- `runEff`/`Trace.ofEff` (Eff tree against read supply), dependency
  constructors, `arm/Arm/Mem/Exec.lean` (`Exec.wf`, `Exec.ofTraces`), good/bad
  examples, two-core message-passing witness, `.agent/DONE`.

## CUTS
- `Trace.po` covers only intra-trace order; cross-core `po` is assembled in
  `Exec.ofTraces` (not yet written).
- No theorems yet, so no `#print axioms` output to record.
