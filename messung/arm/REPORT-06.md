# Agent 06 report — executions from instruction traces

## Done
- Read frozen vocabulary `arm/Arm/Mem/Event.lean` (`Ev`, `Rel`, `Exec`) and
  `arm/Arm/Isa/Monad.lean` (`Eff` tree); Sail citations: memory effects
  `__ReadMem`/`__WriteMem` are `sail-arm/arm-v9.4-a/src/mem.sail` lines 44-57,
  the event interface is `sail/lib/concurrency_interface/read_write.sail`,
  barriers are the `Barrier` union of
  `sail-arm/arm-v9.4-a/src/interface.sail` lines 166-189.
- `arm/Arm/Mem/Trace.lean` (new, imported from `arm/Arm.lean`):
  `Trace` (core, events, addr/data/ctrl), `Trace.po` (earlier-before-later),
  `runEff` (fuel-bounded replay of an `Eff Unit` tree: `rdMem` reads the
  supplied value, `wrMem`/`bar` emit events, register reads answer zero
  without an event, `raise` ends the run), `Trace.ofEff`, `Trace.withDeps`.
- `arm/Arm/Mem/Exec.lean` (new, imported from `arm/Arm.lean`):
  `Exec.ofTraces` (union of traces plus chosen `rf`, `co`, optional `rmw`),
  `Ev.isRead/isWrite/addr?/size?`, `Exec.rfOk` (exactly one same
  address/size/value write per read), `Exec.coOk` (strict total order per
  location), `Exec.poOk` (per core, transitive, irreflexive), `Exec.depOk`
  (read to po-later), `Exec.rmwOk` (read to po-later same-core same-address
  write), `Exec.wf` (unique ids plus all clauses).
- Examples: `exGood_wf` (true); planted refusals `exBadRf_wf` (value
  mismatch), `exBadCo_wf` (missing totality), `exBadPo_wf` (cross-core po),
  `exBadDep_wf` (edge from a write), `exBadRmw_wf` (cross-core rmw), all
  false. All closed `decide` proofs, each on `[propext]` only.
- Witness `mp_wf`: message passing assembled from `Eff` trees (`mpW`,
  `mpR`, `mpInitW` via `Trace.ofEff`, combined by `Exec.ofTraces`), `wf`
  holds; non-degenerate (6 events, init plus two cores, cross-core `rf` on
  both cells). Axioms `[propext]` only.
- No consistency predicate defined (agent 07's). No field added to frozen
  files; nothing frozen edited.
- Build: `./arm-bau` exit 0, 0 errors (8 jobs).

## Open
- Nothing. All deliverables done, committed, reported.

## CUTS
- `ofEff` leaves dependency edges empty; `withDeps` attaches
  caller-reported ones checked by `wf`. Intra-instruction dependency
  synthesis (which read feeds which later access) is future work with the
  instruction agents.
- Register/system reads answer zero in `runEff`: core-local values invisible
  to the memory model; an instruction whose memory effects depend on them
  still emits the right events, only the values come from the supply.
- Theorems use only closed `decide` proofs: `propext` throughout.
