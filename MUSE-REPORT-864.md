# MUSE-REPORT-864: Redundant-load CSE rule (lane 864)

## What was done

New file `grammatik/Grammatik/X86/OptCseLoad.lean` (~490 lines) plus one
import line in `grammatik/Grammatik.lean`. No other file touched; no new
diagnostic/gift/example/CLI numbers, no MARKE changes, no source, checker,
Spec, goal or emitter edits, no friend-reserved optimiser files.

The rule covers OPTIMIZER section 3.7 A1 (load reuse over proved sameness),
section 3.3 V1/V2 (no CSE across invalidation), section 5.2 (no motion
across atomics/locks/fences/calls/MMIO) and the section 7.2 alias row
(certificate carries the sameness proof, validator recomputes). Read once
each: the real `Syntax`/`Semantik` `eval`/`execEnd` fragment covered
(`Expr.slot`, `Endblock.bind`, `World.lese`), `TableLayout` (computed
extents/alignments, overlap/alignment refusals as the shape of admission
predicates), `CostSummary` (removed computation is pure and unbudgeted;
formal machine-work bound OPEN, same cut as the fold lane), and the
invariant/effect exports (`InvariantenOpt.slot_read_stabil` is the value
core this rule builds on; `RahmenTreu` covers call frames, not eval
congruence, so it is cited, not reused).

## Exact names of new definitions/theorems

- `CseLoadCert` (structure, 7 validator-decided `Bool` fields:
  `gleichObj`, `breiteOk`, `ausrOk`, `tokenOk`, `stabilOk`, `idxRein`,
  `keinPublishHoist`), `cseLoadZulassen` (admission conjunction).
- Refusals: `cseLoadVerweigert_publish` (hoist above publish-acquire),
  `cseLoadVerweigert_token` (intervening store/atomic/fence/call/lock),
  `cseLoadVerweigert_stabil` (no ownership/held-lock/immutability),
  `cseLoadVerweigert_objekt`, `cseLoadVerweigert_weite`,
  `cseLoadVerweigert_idx`, plus probes `probe_cseLoadZulassen_ok`,
  `probe_cseLoadZulassen_publish`, `probe_cseLoadZulassen_token`.
- `cseLoadWort`, `probe_cseLoadWort`, `cseLoadGleit_behält`,
  `probe_cseLoadGleit` (value/word/IEEE preservation, no syntax
  premises, hence no witnesses needed).
- `CseLoadRewrite` (exact certificate shape: `ladestelle`,
  `nutzungsstelle`, `zitatVerfuegbar`, `zitatReinheit`, `zert`),
  `cseLoadRewritePrueft`, `cseLoadRewrite_prueft`,
  `probe_cseLoadRewrite_ok`, `probe_cseLoadRewrite_publish`.
- `cseSlotN` (int projection through the checked type proof, after
  `Adressraum.weltByte`).
- TARGET `OptCseLoad_verbindung`: two adjacent integer-slot loads under
  a double `bind` with arbitrary continuation `rest`; concludes value
  equality, slot/glob agreement, held-lock agreement, the EXACT spur
  difference (optimized spur drops precisely the one eliminated read
  event), the orte equations, the word image, and both windows unfolded
  to the same `rest` at the related handoff states. Validator admission
  is consumed through conditional deliveries (`hIdx`/`hHalt`), the
  DESIGN 7.3 soundness shape; every premise is used.
- Companion `OptCseLoad_verbindung_zeuge`: all premises jointly
  instantiated on `refD` (closed index `0` via `zwIdx`, `zwLoad0/1`,
  `zwVar`, `zwS1/zwR1/zwS2/zwS2'/zwR2/zwR2'`), with
  `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`
  (non-degenerate: table-writing function, reached run, slot `0 -> 100`).
- `probe_zwIdx_orte`.

## Last `./lean-bau` result line

`== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed
successfully (511 jobs)`. `./lean-probe` on the new file: 0 errors,
0 warnings. `#print axioms` for every main theorem: subset of
`propext`, `Classical.choice`, `Quot.sound` (standard; nothing added to
`gabbro_ziel`, which was not touched).

## What remains open (see CUTS in the file)

Generic `optSound` (Bool-to-Prop bridge), downstream rest-induction for
arbitrary continuations, non-adjacent (dominator/avail) windows,
float-typed load windows at `Endblock` level, formal machine-work bound,
silicon correspondence and the TSO/GX bridge.

## Task feedback

Nothing in the task is wrong. One scoping note: strict `execEnd`
equality between original and rewritten window is FALSE in general (the
eliminated read event lives in `spur`), so the connection states the
exact handoff relation instead of a false equality; the file says this
plainly. The `.var`-reuse orte difference (`[t]` vs `[]`) is the
mechanism, not a gap.
