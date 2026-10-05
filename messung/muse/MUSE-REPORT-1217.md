# MUSE-REPORT-1217: Pipeline atomics — execBlock correspondence

Lane 1217, clone `/home/simon/Dokumente/gabbro-muse/a1217`, branch `muse/1217`
(verified at start). Owned files only:
`grammatik/Grammatik/X86/PipelineAtomicsBlock.lean` (new, ~610 lines),
`grammatik/Grammatik.lean` (one appended import line), this report.

## What was built

Follow-up of lanes 1163 (`PipelineAtomics.lean`) and 1203
(`PipelineAtomicsBind.lean`), which had per-access facts only. This lane
adds the block level, reusing accepted definitions unchanged (no new
machine, no new decoder row, no second IR, no second source
interpreter, no optimiser change, no existing-file edits):

- §1 Block chaining: `SperrSchritt` (one MFENCE-bracketed section step:
  entry drain, reached middle with foreign frame, exit drain,
  lowerable body) and inductive `SperrLauf` (sections chained state to
  state), with `sperrlauf_erreichbar` (one reached run via `sperre_korrekt`
  + `erreichbar_kette`), `sperrlauf_leer` (nonempty runs end drained),
  `sperrlauf_fremd` (foreign buffers intact).
- §2 CAS failure at register level: `bind_cas_fehlschlag`, the twin of
  lane-1203 `bind_cas_erfolg`, via the accepted
  `lockVoll_cmpxchg_fehlschlag_adapter` (stutter at the address the
  register pair names, decided `false` ledger).
- §3/§5 Block (non-)lowering: `block_nested_verweigert`,
  `block_leer_ok`, `block_singleton_ok`, `gift_block_val_nested`,
  `gift_block_val_ueberlang`, `abOps` (release write then acquire read
  of the shared global at `abGlobA`) with `abOps_senk` (two plain
  MOVs), `abblock_refuses_nested` (nested section refused anywhere in
  a block, induction following the lane-1163 shape).
- §4 Real source block: witness declaration `abD` (two-row `0..1000`
  table, shared-atomic `0..255` global, one lock), contract `abV`,
  oracle `abO`, program `abSrc`
  (`T[0] = 35; A = 42; locks L { T[1] = 17 }; T[0] = A;`) with
  `ab_quelle` proved by `rfl` (row 0 = 42 via the atomic read,
  row 1 = 17, atomic 42).
- §6 Concrete CAS machine `abM` (word 10 at the global, rax = 11,
  empty buffers; all side facts by `decide`) with
  `ab_cas_fehlschlag_inst` (register-bound stutter).
- §7 Concrete section run `ab_sperrlauf_inst` over the accepted
  `fdS2` drains (exit via proved `ab_drain_leer_ident`, drain of an
  empty buffer is the identity from `drainKernN_null`).
- §8 `abblock_correct` (any source run yields the computed values and
  the emitted lowering, via `ab_quelle` substitution) and the joint
  non-degenerate witness `abblock_zeuge` (source + target memory
  change, written table `abV`/`witD`, bound CAS failure, bracketed
  section, refusal). Full CUTS block and `#print axioms` for every
  theorem.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineAtomicsBlock.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (640 jobs)`.
- `#print axioms`: every theorem depends only on `propext`,
  `Classical.choice`, `Quot.sound` (several on subsets, some on none).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grepped).
- No new diagnostic codes, gift/example numbers, or German text: all
  refusals reuse `senkListe = none` / `valAtom = false`; witnesses
  reuse `senkAtom_zeuge`/`bind_zeuge` states.
- Rust out of scope (no Rust touched); no push (lane rule).

## Findings and apparatus notes (for the coordinator)

1. Corrupted identifier bytes (real, worked around): one early write
   left non-ASCII lookalike bytes spelling "vertrag" on the `abV`
   type line. Lean reported `unknown identifier`; ASCII patterns
   (`rg`, `sed s///`, Edit `oldString`) silently failed to match it.
   Proven by byte counts (`wc -c`) and match/no-match experiments.
   Fix: extracted the trusted bytes of `Vertrag` from
   `Syntax.lean:451` (`head -c 21 | tail -c 7`, 7 bytes verified) and
   spliced them in with addressed `sed` (`s`, `r`, `N`-join); ground
   truth was `lean-probe`, not display. The affected token sequence
   was never typed again afterwards.
2. Tool staleness: after the first `sed -i` on the file, the Edit
   tool no longer matched sed-touched lines (it sees its own last
   state, not bash writes). From that point the file was edited only
   via addressed `sed` (patterns avoiding the corrupted token) plus
   Edit on untouched regions. Recommend: do not mix Edit and
   `sed -i` on one file within a lane.
3. Lean facts: a nested `{ }` record inside `LockMaschine where`
   fails to parse (`expected '}'`); the same `Zustand` literal as a
   standalone `def` (`abZu0`) works. `Orakel.sichtbar` takes two
   arguments (`Glob → World → Bool`); `nomatch` needs `Empty`, so a
   `Unit` glob uses `fun _ _ => true`. `()` does not elaborate
   against `abD.Glob` under a metavariable world — `Unit.unit` does.
   `sperrlauf_leer` needs a `≠ []` premise (the empty section list
   drains nothing). `(some x).isSome = true` is not closed by `rw`
   alone — `decide` works on closed instances.
4. Task reading: in the real `Semantik`, a shared-atomic read is
   `σ.globs g` (world content), not an oracle answer; the "read
   oracle" leg is therefore the world-supplied value flowing into
   row 0 (`abRead`/`ab_quelle`), with the atomic-havoc stability
   staying with lane 1163 (`rely_stabil`, cited). Nothing in the
   task is otherwise wrong; no premise was added, no conclusion
   weakened.

## Open (see CUTS)

No TSO word-install for the block's own MOVs (lane 1163 per-access
+ lane 1203 `wort_installation` cover it); no integer-slot machine
run (accepted `Pipeline`, cited); no SFENCE/LFENCE brackets;
per-step framing of arbitrary middles stays an explicit premise;
no seq_cst total order, fairness, retry bound, timing, interrupts,
devices, MMIO, or DMA.

Commits on `muse/1217` (this report included): skeleton, SperrLauf
chaining, CAS-failure binding + refusals, source block, access
sequence + refusal, CAS machine, drain run, correspondence + witness.
