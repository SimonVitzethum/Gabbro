# MUSE-REPORT-880: Copy coalescing rule lemma

## What was done

New file `grammatik/Grammatik/X86/OptCoalesceMove.lean` (registered as
`import Grammatik.X86.OptCoalesceMove` at the end of
`grammatik/Grammatik.lean`), proving the DESIGN section 7 example-1 /
"Layout / allocation" row copy-coalescing rule over the reused canonical
vocabulary only (`Typen`, `Syntax`, `Semantik`, `ReferenzB`,
`X86.Typen`, `X86.Wort`). No second IR, no second evaluator, no
per-program rule, no source/checker/Spec/goal/emitter change, no new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT change, no
friend-reserved file touched.

Certificate shape (exact): layer-A local rewrite record `CoalRewrite`
(`quelle`, `kopie`, `gleicheWeite`) plus layer-B recomputed analysis
citations `CoalAnalyse` (`avail`, `dominiert`, `adressGenommen`,
`callArg`), admitted by the decided Bool `coalZulassen` (conjunction;
refusal falls back, never warns).

New definitions/theorems (exact names):
- `CoalRewrite`, `CoalAnalyse`, `coalZulassen`
- Refusals: `coalVerweigert_avail`, `coalVerweigert_dominiert`,
  `coalVerweigert_weite`, `coalVerweigert_adressGenommen`,
  `coalVerweigert_callArg` (the last two are the precise DESIGN failure
  case: address-taken spill via call arg must NOT fire)
- Probes: `probe_coalZulassen_ok`, `probe_coalZulassen_avail`,
  `probe_coalZulassen_spillCall`
- Value preservation: `coalWort` (+ `probe_coalWort`), `coalGleit_behält`
  (admitted float copy keeps value and `gleitPasst` outcome; + `probe_coalGleit`)
- `OptCoalesceMove_verbindung`: generic rule lemma over arbitrary
  integers at an `Endblock.bind` window with arbitrary continuation
  `rest`; concludes value preservation + `execEnd` outcome equality
  (hence same faults incl. IEEE `logik bereich`, same contracts at their
  place with actual values, no new call-log event, no added/removed
  shared access for concurrency, unchanged step-budget accounting) +
  width-exact word image. Every premise is used by its proof.
- `OptCoalesceMove_verbindung_zeuge`: joint inhabitation on `refD`
  (`3 + 4` vs copy `7` under `bind`/`leave`), with
  `refEin_schreibt`, `refB_erreicht`, `refB_schreibt` (non-degenerate:
  table-writing contract, reached run with memory-changing step).
- `CUTS` block + `#print axioms` for every main theorem.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`, including
`Built Grammatik.X86.OptCoalesceMove`. Axioms: at most
`[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel` set;
`Spec.lean` untouched).

## What remains open (see CUTS)

No block-window float-copy rewrite; no multi-copy chains / 2-cycles
(each link needs its own avail/dominance citation; copy-slot deadness is
the allocator's obligation); no formal level-(c) machine-work bound
(OPEN per IR-VALIDIERUNG lane 278); no silicon/TSO-GX/ABI claim;
spill-slot copies stay with `SpillPrivate`.

## Task feedback

Nothing in the task is believed wrong. One scoping note: the task asks
for "budget" preservation and the proof covers step-budget accounting
equality (same block shape, removed copy pure/unbudgeted); the
machine-work transfer itself is OPEN by design and recorded in CUTS,
not claimed.
