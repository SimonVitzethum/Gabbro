# MUSE-REPORT-880: Copy coalescing rule lemma (repair resubmission)

## Review response (MUSE-REPORT-1030, VERDICT: REPAIR)

All three findings addressed, R1+R2+R3 jointly:

- F1 (conclusion restated premises): the connection is restated over a
  CONCRETE copy shape. The copy is the variable read `var x` of the
  available dominating definition; the value conclusion is derived
  through the COMPUTED var-read fact (`eval` of `var` is the
  environment lookup) plus the avail equation -- not a direct instance
  of an assumed expression equation. The orte equality is DERIVED from
  admitted purity via the proved soundness lemma, not assumed.
- F2 (certificate unlinked): two proved admission-to-semantics bridge
  instances now exist (`kopieRein_klingt`, `kopieBind_liest`), and CUTS
  records the explicit residual open obligation (per-site discharge of
  `hRein`/`hVerfuegbar` from recomputed avail/dominance, owned by the
  validator/lowering lane; the witness's `rfl` discharges do NOT count
  as that discharge).
- F3 (overstated wording): the section-4 doc comment and this report
  state exactly which equalities are assumed (validator discharge:
  `hRein`, `hVerfuegbar`) and which are proved (var-read computation,
  derived orte equality, `execEnd` congruence, word image). The earlier
  "proves value preservation" sentence is withdrawn in that
  unqualified form.

## What was done

`grammatik/Grammatik/X86/OptCoalesceMove.lean` (registered as
`import Grammatik.X86.OptCoalesceMove` in `grammatik/Grammatik.lean`),
proving the DESIGN section 7 example-1 / "Layout / allocation" row
copy-coalescing rule over the reused canonical vocabulary only
(`Typen`, `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`).
No second IR, no second evaluator, no per-program rule, no
source/checker/Spec/goal/emitter change, no new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT change, no
friend-reserved file touched.

Certificate shape (exact): layer-A local rewrite record `CoalRewrite`
(`quelle`, `kopie`, `gleicheWeite`) plus layer-B recomputed analysis
citations `CoalAnalyse` (`avail`, `dominiert`, `adressGenommen`,
`callArg`), admitted by the decided Bool `coalZulassen`.

New definitions/theorems (exact names):
- `CoalRewrite`, `CoalAnalyse`, `coalZulassen`
- Refusals: `coalVerweigert_avail`, `coalVerweigert_dominiert`,
  `coalVerweigert_weite`, `coalVerweigert_adressGenommen`,
  `coalVerweigert_callArg` (the last two are the precise DESIGN failure
  case: address-taken spill via call arg must NOT fire)
- Probes: `probe_coalZulassen_ok`, `probe_coalZulassen_avail`,
  `probe_coalZulassen_spillCall`
- Purity bridge: `kopieRein` (validator-recomputed orte-emptiness;
  probes `probe_kopieRein_add`, `probe_kopieRein_slot`) with proved
  soundness `kopieRein_klingt` (+ `kopieRein_klingt_zeuge`)
- Computed copy core: `kopieBind_liest` (a variable read of the
  just-bound slot IS the bound value, by `rfl` from the bind/env
  semantics) (+ `kopieBind_liest_zeuge`)
- Value preservation: `coalWort` (+ `probe_coalWort`), `coalGleit_behält`
  (+ `probe_coalGleit`; conditional-`hEq` shape per accepted lane-860
  practice, not a repair driver)
- `OptCoalesceMove_verbindung`: generic rule lemma over the concrete
  `var x` copy at an `Endblock.bind` window with arbitrary continuation
  `rest`; concludes value preservation (via computed var-read +
  avail), `execEnd` outcome equality (via derived orte equality --
  hence same faults incl. IEEE `logik bereich`, same contracts at
  their place with actual values, no new call-log event, no
  added/removed shared access for concurrency, unchanged step-budget
  accounting) + width-exact word image. Every premise is used by its
  proof.
- `OptCoalesceMove_verbindung_zeuge`: joint inhabitation on `refD`
  (in-scope slot holding `7` reused instead of recomputing pure `7`),
  with `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`
  (non-degenerate: table-writing contract, reached run with
  memory-changing step).
- `CUTS` block (incl. the R2 residual-obligation entries) + `#print
  axioms` for every main theorem.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`, including the rebuilt
`Grammatik.X86.OptCoalesceMove`. Axioms: at most
`[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel` set;
`Spec.lean` untouched).

## What remains open (see CUTS)

Per-site discharge of `hRein`/`hVerfuegbar` from recomputed
avail/dominance (validator/lowering lane); no block-window float-copy
rewrite; no multi-copy chains / 2-cycles; conservative purity (`fall`,
memory/globe/device/binder refused); no formal level-(c)
machine-work bound (OPEN per IR-VALIDIERUNG lane 278); no
silicon/TSO-GX/ABI claim; spill-slot copies stay with `SpillPrivate`.

## Task feedback

Nothing in the lane or review task is believed wrong. One process
note: mid-repair, `./lean-probe` once reported `unknown identifier
vertrag` at the witness while the theorem above it still carried its
`sorryAx` from the unfinished C2 proof step; after the proof was
completed the identical line probed green with no edit. Suspected
stale incremental session state in the probe wrapper (the committed
green file had the same spelling), not a source error; recorded here
so a re-occurrence is recognised.
