# MUSE-REPORT-651 — Exact review of author 650 (Growing TSO history to typed carrier W transition)

## Scope and method

Reviewed the exact pinned snapshot (`.tmp/review/SNAPSHOT.json`, author 650) against the owner
task (`.tmp/review/author-650/OWNER-TASK.md`), the PATCH diff and the actual candidate module
(`grammatik/Grammatik/X86/CarrierTraceBridge.lean`, 946 lines). Verified clone
`/home/simon/Dokumente/gabbro-muse/a651` on branch `muse/651`. Reproduced independently with
the queued wrapper on the current tree (base `24e625c0` present locally; candidate content
identical to the snapshot copy):

- `./lean-probe .tmp/review/author-650/grammatik/Grammatik/X86/CarrierTraceBridge.lean`
  prints `== 0 error(s) in the COMPLETE output; exit 0`.
- `#print axioms` output is within the standard goal set for every theorem:
  `ErbtW`/`erbtW_start`/`ctFfresh`/`ctFremdFF` on `[propext]`, `erbtW_schritt`/`erbtW_waechst`
  on `[propext, Quot.sound]`, `assignSlot_spur`/`schrittW_aus_gruppen_drain` and the joint
  witness on `[propext, Classical.choice, Quot.sound]`.
- `grep` for `sorry|admit|axiom|native_decide|unsafe` finds only the English word
  "admitted" in a header comment (meaning previously accepted work, not a Lean `admit`);
  no tactic-level violation. `histVon` occurs only in the header comment stating it is
  never used; the relation consumes only `traceHist`/`traceSicht`/`traceFrisch`.
- All consumed lemmas resolve to real accepted definitions in this tree:
  `spurStart`/`SpurSchritt`/`spurStart_inv`/`spurSchritt_inv`/`traceSicht`/`traceFrisch`
  (`X86/TSOTrace.lean`), `WortGruppe`/`DrainSpur`/`FremdFrei`/`wort_gruppe_liest_zurueck`/
  `eigen_fremd_gleich`/`fremd_leer_eigen_erhalten`/`fremdFrei_aus_leer`
  (`X86/WordAccessGrouping.lean`), `rep_schritt_bleibt`/`RepSlot`/`zahlWort`/
  `zahlWort_wortZahl`/`witD`/`witI`/`witE`/`witHL`/`witHT`/`witSigma`/`witSL`/`witO`/`witA`/
  `witM`/`witM'`/`witVal` (`X86/SourceMemory.lean`), `blattFragment_voll`
  (`X86/SourceAccessCompleteness.lean`), `RufStartW`/`mitSpeicher`/`vorSicht`/`ordVon`/
  `SchrittW` (`Speichermodell/MaschineW.lean`). No miniature source interpreter, no new
  IR, no invented witness infrastructure (reuses the accepted `wit*` family).
- PATCH touches only owned paths: new `MUSE-REPORT-650.md`, one import line appended to
  `grammatik/Grammatik.lean`, new `grammatik/Grammatik/X86/CarrierTraceBridge.lean`.
  No checker, Spec, goal, emitter, Rust or friend-reserved file edits.

## Semantic findings

- `ErbtW` is a genuine clock-bound plus view-coverage relation, not a hidden simulation:
  no assumed read, no whole `SchrittW`/GX premise. `erbtW_start` computes (`0 < 1`,
  `0 <= _`); `erbtW_schritt` case-splits the real `SpurSchritt` (issue keeps the clock,
  flush advances by one) and uses both `hErbt` conjuncts, `hinv` (`hblick`) and `hs`;
  `erbtW_waechst` transports both invariant and relation by induction. All premises used.
- `schrittW_aus_gruppen_drain` derives an actual typed-carrier `SchrittW` (built via the
  real `RufSchrittG.blatt` over `mitSpeicher`/`weltVon` with `execStmt` evidence), plus
  independently derived cross-side value agreement (`wort_gruppe_liest_zurueck` rewritten
  by `hnode`, closed by `zahlWort_wortZahl`) and `RepSlot` (via `rep_schritt_bleibt`).
  Checked premise use: `hLo`/`hHi` feed `zahlWort_wortZahl`; `hRd` feeds
  `rep_schritt_bleibt`; `hnode` feeds the `read64` rewrite; `hInvN` feeds the freshness
  side-condition; every grouping premise feeds `hread`; `hs`/`hhead`/`rest` feed the
  leaf facts and machine construction. The `rmw` field is discharged by refuting the
  exchange head against `hhead`, which is legitimate for this no-read fragment.
- Tearing discipline is honest: the drain requires the full eight-entry `WortGruppe` plus
  `FremdFrei` at every visited state; the claim is observational grouping under checked
  exclusion, never hardware atomicity. CUTS restricts unobservability to the
  single-significant-byte witness value (42) and leaves multi-byte tearing at the byte
  layer. The stale-view refusal is concrete (`ct_stale0`/`ct_stale1` by `decide`: core 0
  reads canonical zero where core 1 forwards seven).
- The joint witness `schrittW_aus_gruppen_drain_zeuge` is non-degenerate and joint:
  written table (`ctHw`), memory-changing source step `0 -> 42` (`hBefore`/`hAfter` by
  `rfl` over the real `execStmt`), memory-changing target drain (`hBytes`, decided
  inequality), eight-flush drain with a real foreign issue inside (`ct_step1..9`,
  `ct_spur`, `ct_hstoer`), two distinct trace timestamps on a reached step
  (`ct_erreichbar`, `ct_uhren`), pending foreign byte outside the footprint
  (`ctBuf1_4`, `ctFfresh`), and the concluded `SchrittW`/value/`RepSlot` from the main
  theorem applied to these same concrete values.
- Two non-blocking observations: (a) the `SchrittW` carrier-agreement field is proved
  stronger than needed (`traegerGleich_refl` for all carriers, leaving that subgoal's
  non-read hypothesis unused), which the report discloses as a vacuity — this strengthens
  rather than weakens the claim; (b) the helper `assignSlot_spur` (quantified over
  `Expr`) has no own same-named witness, but its exact premises are jointly inhabited
  inside the main witness (same `witI`/`witE`, `hOrte` by `rfl`, real `hExec`), so this
  is a naming gap for a follow-up, not a vacuity or contradiction.
- No source-specific trust rules, no desired-correctness premises, no assumed complete
  histories, no forged fetched input (all drain steps are `rfl`/`decide` computations over
  real `TSOZustand` bytes and buffers), no guarantee weakening, no inflated closure:
  reads, LOCK/RMW, run induction, GX refinement, scheduling and devices stay OPEN in
  truthful CUTS. Full `./lean-bau` was not re-run here (author evidence: 458 jobs green;
  integration gate re-checks); the file-level reproduction above is exact.

CANDIDATE: 650 bcf4f44dfa13281dc8a782f98bbd8b5be6bf0a58

The accepted bounded claim is: `ErbtW` with proved start/step/finite-trace preservation
plus one actual typed-carrier `SchrittW` for a no-read `assignSlot` fragment write whose
exclusion-checked grouped TSO drain installs the source-written word, with derived
cross-side value agreement and `RepSlot`, witnessed jointly on `witD` with a `0 -> 42`
source step, an eight-flush drain containing foreign activity, two distinct trace
timestamps and a stale-view refusal; read carriers, LOCK/RMW, run induction and GX
closure remain OPEN per CUTS.

VERDICT: ACCEPT
