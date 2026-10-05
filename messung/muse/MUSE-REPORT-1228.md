# MUSE-REPORT-1228: Exact review of lane 1227 (PipelineSpillHoming)

CANDIDATE: 1227 4bc4873d36fdf96753975a06d5ac74e62080d169

VERDICT: ACCEPT

## What was reviewed

Correction applied: the author clone hash is not readable from this clone,
so the review used the delivered files under `.tmp/review/author-1227/`:
`PATCH.diff` (base cbc0afe0 to head 4bc4873d, 593 lines), the copied new
file `grammatik/Grammatik/X86/PipelineSpillHoming.lean` (449 lines),
`OWNER-TASK.md` (= lanes/1227.md task), `BUILD-EVIDENCE.json`, and
`MUSE-REPORT-1227.md`. Prior REPAIR findings were about unreadability only
and identified no content defect; they are superseded by this content
review of the reviewed pin. Reviewer clone /home/simon/Dokumente/gabbro-muse/a1228,
branch muse/1228, HEAD cbc0afe0 = snapshot base, tree clean.

## Checks, each performed

- Banned constructs: `rg` over the candidate file for sorry/admit/axiom
  declarations/native_decide/unsafe/split_ifs/norm_num/ring_nf/discarded
  premises finds only the English word "admitted" in comments and the
  required `#print axioms` lines. No `axiom` declaration. No Prop-typed
  premise.
- File scope: PATCH touches exactly the three snapshotted files. The only
  existing-file change is one appended
  `import Grammatik.X86.PipelineSpillHoming` line in `grammatik/Grammatik.lean`
  after `HwDrainGeneric`, matching this clone's file end. Reserved
  optimiser files untouched.
- Axioms: independent `./lean-probe` of the delivered file in this clone:
  `0 error(s)`, exit 0. Main theorem `pipeHoming_haelt_bedeutung` and the
  joint witness depend on exactly `[propext, Classical.choice,
  Quot.sound]` (the standard set); every other name depends on a subset or
  nothing. Matches the author's `#print axioms` output.
- Evaluator reuse, not duplication: no `validate`/`execBlock`/`laufBytes`
  redefinition in the file (`rg` empty). The closing theorem feeds the
  accepted `pipeline_correct` plus the accepted allocator/spill legs
  (`pipe_alloc_interferenzFrei`, `spillPlan_tabellenGetrennt`,
  `spill_schlitze_getrennt`, `spillPlan_schranke/inRahmen/offDaten`,
  `pipe_alloc_verweigert_kollision`), each verified to exist with the used
  signature in this clone's `Pipeline*.lean`.
- Premise use: every premise of every new theorem is consumed.
  `pipeHoming_haelt_bedeutung` uses `hval`+`hsep` (via `pipeline_correct`),
  `hhom` (via `pipeHoming_allocOk`/`pipeHoming_planOk`), `hrahmen` (via
  `pipeHoming_tabellenGetrennt`), and all machine/world/environment
  premises through `pipeline_correct`. The four projection legs each use
  their hypothesis; each refusal theorem uses all its arguments; no
  `intro _` / `have _ :=`.
- Refusals really refuse: one positive probe (`pipeHoming_probe_pos`, by
  `decide`) and five refusal probes (clash/table/out-of-frame/split via
  their refusal theorems, code-overlap by `decide`) all elaborate green in
  the independent probe — `decide` can only close a true computation, and
  the refusal-theorem applications typecheck only against genuinely
  refusing instances.
- Witness non-degenerate: `pipeHoming_haelt_bedeutung_zeuge` is joint over
  the accepted pipeline witness program via `pw_quelle30` (real `execBlock`
  run, rows to 35 and 6) and `pw_quelle_vorher` (rows from 7 and 9), so the
  source run is memory-changing. All witness vocabulary verified present in
  this clone's `PipelineWitnesses.lean`/`PipelineRegAlloc.lean`.
- Silicon: no new hardware facts, encodings, or fault classes are stated;
  only accepted machine vocabulary is reused. Nothing to check against the
  SDM extracts, and none is claimed.
- CUTS honest: claims exactly the decided-homing composition; OPEN items
  (no save/reload splicing at splits, no range merging, no calls, TSO
  freshness beyond `SpillFrisch`, no `pipeline_correct_loaded` re-proof)
  are listed. No hardware-correspondence or W/GX claim. The author's entry-
  vs `pipeline_correct`-level remark is accurate: homing involves no
  parameter ABI, and the entry connection is inherited through the wrapped
  theorem.
- Build: `./lean-bau` in this clone (base, warm cache): `exit 0`,
  `Build completed successfully (640 jobs)`. The candidate-tree green
  (641 jobs) is the author's BUILD-EVIDENCE plus my 0-error probe of the
  exact delivered file against this base; the three transient apparatus
  failures in the author's log are documented resource-pressure events at
  the root step, not code defects.

## Remarks (not defects)

- The author's "394 lines" count predates later additions; the delivered
  file is 449 lines including all probes, the witness, CUTS and axiom
  prints. Content, not the count, was reviewed.
- Task-conformance note: correctness is stated at the `pipeline_correct`
  level rather than `pipeline_correct_entry`; justified (no ABI involved)
  and the family pattern (`spill_haelt_bedeutung`,
  `pipe_alloc_haelt_bedeutung`) is followed.

## Owned files

Only MUSE-REPORT-1228.md (this file). The candidate file was probed
in place under `.tmp/review/` via `./lean-probe <path>` (the wrapper
accepts any path; lake resolves imports from the project); nothing was
copied into `grammatik/` and no other file was written.
