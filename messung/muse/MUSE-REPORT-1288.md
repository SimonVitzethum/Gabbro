# MUSE-REPORT-1288: Exact review of lane 1287 (Memory types WC, WT, WP + cache-control)

## Task
Independent exact review of candidate lane 1287 (second pinned snapshot
after author repairs). Scope per `lanes/1288.md`: no banned tactics or
axioms; standard printed axioms; existing files untouched except one
import line; every premise used; the family's accepted evaluator lifted,
never copied; planted refusals really refuse; a non-degenerate witness
(memory-changing step, two cores where relevant); silicon facts checked;
honest CUTS with no claim larger than the proof (in particular no
hardware-correspondence or W/GX claim). Full `./lean-bau` result reported
below. Exactly one machine-readable verdict line, no weakened guarantees,
no fake closure.

## Clone verification
- `pwd` = `/home/simon/Dokumente/gabbro-muse/a1288`,
  `git branch --show-current` = `muse/1288` (single short commands).
  Match: PASS.
- Owned file only: `MUSE-REPORT-1288.md`. No other file created or edited.

## Candidate identity

CANDIDATE: 1287 d60993034581952addc8a6e3aae88e6bc69909c2

- Pinned snapshot (`.tmp/review/SNAPSHOT.json`): author 1287, head
  `d60993034581952addc8a6e3aae88e6bc69909c2`, base
  `738366545afbddf7ac664db92804703db24f8868`, files
  `MUSE-REPORT-1287.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HwMemTypesWC.lean`, clean true.
- This supersedes the first pinned head `162a6d02` (reviewed
  procedurally only: no candidate content was available then, so no
  stale snapshot is approved here).
- Evidence materialised in-clone under `.tmp/review/author-1287/` and
  reviewed in full: `PATCH.diff` (1429 lines: author report,
  one-line `Grammatik.lean` import, new 1288-line
  `HwMemTypesWC.lean`), `MUSE-REPORT-1287.md`, `OWNER-TASK.md`,
  `BUILD-EVIDENCE.json` (per-step probe/build log).

## Findings (each checklist item inspected)

- Banned tactics/axioms: PASS. Grep over the patch for Lean-code use of
  `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `sorryAx`
  finds only English prose ("admit theorems", "admits", "axioms" in
  comments/report). No `intro _` / `have _ :=` discards. Proofs use
  `decide`, `simp`, `rw`, `cases`, `refine`, `exact` only.
- Printed axioms: PASS (author-supplied probe output). Every main
  theorem prints within `[propext]`, `[propext, Quot.sound]`, or no
  axioms -- a subset of the standard set, e.g. the connection
  `hwWc_verbindung1287` on `[propext, Quot.sound]`, its joint witness
  on `[propext]`. 40 `#print axioms` lines close the file.
- Existing files: PASS. The patch touches only `grammatik/Grammatik.lean`
  (exactly one appended import line) plus the two new/author-owned files.
- Premise use: PASS. The 20-premise connection theorem discharges every
  premise: steps via bypass/frame/go-through/NOP/fence lemmas, wf chained
  across all six stages, both named assumptions applied
  (`wcPinsLaenge`, `wtWpBus_liest`), observation premises turned into
  the two owner/foreign splits and both memory-change inequalities,
  profile/permission premises turned into the two planted refusal facts.
  No premise is weakened away; contracts hold at their place.
- Lift, not copy: PASS. The WC buffer, step functions and adapter are
  new (no accepted WC model exists to lift -- necessarily new and so
  disclosed); everything reusable is reused unchanged: `drainVoll`
  with `drain_voll_leer` / `drain_voll_bereit`, `mfenceDrain_fremd`
  (no fence-everywhere), `pufferSetze` with `_gleich` / `_anders`,
  `neuestens` forwarding, `HwWf`, `hwWitStart` / `hwWitStart_wf`,
  the `HwAdapter` shape. Exact plug agreement
  (`adapterWt/Wc_stimmt_ueberein`) proves the plug equals the extended
  functions projected to the bare machine.
- Refusals: PASS, and they compute. Wrong-type UC/wrong-type
  (`wcAdapter_wc_falscherTyp/_nichtUc`), three-way permission refusal
  (`wcAdapter_ohneSchreibrecht`), decoder pins (PREFETCHh register form,
  LOCK prefix on both decoders, SFENCE mod=3 row not CLFLUSH), plus the
  kind and permission refusals as computed facts inside the connection.
- Witness: PASS, non-degenerate. Explicit six-state run: WC store with
  owner-only forwarding (core 0 sees 42, core 1 the old 0, memory still
  0), store-ordered CLFLUSH line drain (memory 0 -> 42), second WC store
  with owner-only forwarding, WT go-through (memory carries 9 at once),
  hint NOP at unreadable address 0, fence drain (memory 0 -> 43).
  Canonical memory changes twice; two cores observe (owner/foreign
  split twice); the joint `_zeuge` instantiates all twenty premises
  with both named assumptions discharged by `rfl`/decided facts.
- Silicon: PASS with stated bounds. PREFETCH 0F 18 with reg-field hints
  (0 NTA, 1 T0, 2 T1, 3 T2), mod=3 and LOCK refused; CLFLUSH NP 0F AE /7
  with the mod=3 SFENCE row refused -- all matching the cited SDM
  entries. WC weak ordering with combining youngest-last buffer and
  fence drain; WT/WP go-through with the shared memory equation (no
  data cache modelled -- stated in CUTS); fault rule readable-or-
  executable, disclosed as wider than a plain byte read. Line size 64
  and the CLFLUSH CPUID bit are named, never probed. Every ordering
  claim is a named assumption (`WcBusAnnahme`, `WtWpBusAnnahme`), never
  a silicon proof, exactly as the task demands. The cited SDM text
  itself is not present in this clone (no hardware-reference extract
  found here), so entry text was sanity-checked from the header
  citations, not re-verified word by word.
- CUTS/honesty: PASS. The CUTS block lists what is proved and an
  explicit NOT-proved list (no CLFLUSHOPT/CLWB/non-temporal forms, no
  WP invalidation traffic, aliasing reserved, cross-core WC eviction
  and WC read ordering OPEN, no W/GX, no source/checker/goal/emitter
  correspondence). No hardware-correspondence claim beyond cited
  entries; no W/GX claim. The report's failed `speicherTyp_mem`
  conjecture (found FALSE, replaced by the skip lemma) is reported,
  not worked around.
- Inhabitation rule: no program-syntax premises exist in this hardware
  file, so the syntax-witness clause is vacuous; the connection's joint
  `_zeuge` on a memory-changing run is present regardless.

## Non-blocking observations
- WP has generic agreement plus adapter admit/refusal theorems but no
  reached WP step inside the six-stage run (WT stands in; both share
  the memory equation by construction, stated). Acceptable; a WP run
  stage would strengthen a follow-up, not this verdict.
- The decoders pin canonical byte shapes (no SIB/displacement forms),
  consistent with the family's pin convention and the base machine's
  stated addressing scope; no coverage beyond pins is claimed.
- `typPfad` is a defined summary unused downstream; harmless (a
  definition, not an unused premise).

## Build results
- This clone (`muse/1288`, report-only, no candidate files present):
  `./lean-bau` green -- `Build completed successfully (671 jobs)`,
  `== exit 0; 0 error line(s) in the COMPLETE output`.
- Candidate tree (author-supplied `BUILD-EVIDENCE.json`, not
  independently rebuilt -- applying the patch here would violate the
  owned-files rule): `./lean-bau` `Build completed successfully
  (659 jobs)`; final `./lean-probe` on the new file `0 error(s),
  exit 0`; tree reported CLEAN. The evidence log also shows the
  intermediate red probes converging to green across the partial
  commits, consistent with genuine development rather than a single
  untested drop.

## Verdict

VERDICT: ACCEPT

- Candidate `d6099303` meets every review gate: closed proofs, standard
  axioms, one-line import discipline, full premise use, lifted (not
  copied) accepted vocabulary, computing refusals, a non-degenerate
  two-core memory-changing witness with joint `_zeuge`, checked silicon
  facts inside named assumptions, and an honest CUTS block claiming
  nothing beyond self-consistency. The previous procedural REPAIR is
  superseded by this substantive review of the new pinned snapshot;
  nothing from it carries over as an open finding.
