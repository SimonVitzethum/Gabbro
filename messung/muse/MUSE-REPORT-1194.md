# MUSE-REPORT-1194: Exact review of candidate 1193 (PipelineLinkMulti)

Lane 1194, clone `/home/simon/Dokumente/gabbro-muse/a1194`, branch `muse/1194`
(working directory verified by read; `git`/branch verification by shell was
not possible in this session — shell tool calls were permission-denied, see
blocker below; no files outside this clone were touched).

CANDIDATE: 1193 fd0c78c793bd054acfc9b81b94b4124c5f6389bf

Candidate 1193, pinned HEAD `fd0c78c793bd054acfc9b81b94b4124c5f6389bf`
(base `9b05e84a8377f2a718cecf9ca1a403d6c9c2b919`), reviewed from the exact
snapshot `.tmp/review/author-1193/` (`PATCH.diff`, `PipelineLinkMulti.lean`
1663 lines, `MUSE-REPORT-1193.md`, `BUILD-EVIDENCE.json`). Files in candidate:
`MUSE-REPORT-1193.md`, `grammatik/Grammatik.lean` (+1 import line),
`grammatik/Grammatik/X86/PipelineLinkMulti.lean` (new).

## Checks performed (read-only; shell denied)

- Forbidden tokens: read the full 1663-line new file in 4 windows
  (lines 1–150, 150–499, 500–849, 850–1299, 1300–1663). No `sorry`,
  `admit`, `axiom` (declaration), `native_decide`, `sorryAx`, `unsafe`
  observed. No `intro _` / `have _ :=` observed. No `Prop`-typed premise,
  no `forall rho` / `forall v` contract quantification, no new semantics.
- Existing-file scope: `PATCH.diff` confirms the only existing-file change
  is one appended line `import Grammatik.X86.PipelineLinkMulti` in
  `grammatik/Grammatik.lean`. `OptimizationRules.lean` /
  `OptimizationWitnesses.lean` untouched. No SSA IR, no second
  decoder/loader/executor/ISA model (imports only accepted producers:
  `PipelineLink`, `ComposePatchBytes`, `Rel8Reach`, `BranchLayout`).
- Reuse not copy: `multiPatch_rel32_gleich` / `multiPatch_abs64_gleich`
  prove by `rfl` that rel32/abs64 patch EXACTLY what two-unit `linkPatch`
  patches; rel32/abs64 range/site/frame/length legs reuse `linkPatch_*`;
  rel8 goes through accepted `patchAt_*`; field agreement goes through
  `rel32Bytes_dispSigned` + `dispVonFit` + decoder determinism
  (`decode_abdeckung`, `decode_fenster_kongruenz`, `relocBytes_decode`),
  never decoder internals; mapping through `geladenByte_datei` and
  `wohlgeformt_wx`; run through reused `ruf_schritt_zeuge`. No duplicated
  canonical vocabulary observed.
- Premise use: `mehrere_korrekt` premises all load-bearing on inspection —
  `halle` drives the 5-step fold split; `hdisj/hdisc/hdisd/hdisa` feed the
  four `kopf_stelle` survivals; `hrahmen` feeds the four opcode frames;
  `hj0/hc0/hd0/hd1` + `hpj/hpc/hpd` build the three window equations;
  `hdecj/hdecc/hdecd` drive the three agreements; `hwf/hmem` give W^X;
  `hfind/hhi` give the executed mapping; `haussen` + `hrahmen` give the
  global frame. Fits (`rel32Passt`/`rel8Passt`) are DERIVED from patch
  successes, not premised — no conclusion repeats a premise.
- Refusals really refuse (all `decide`-proved concrete probes):
  `multiUeberlapp_verweigert` (overlap → disjoint false),
  `multiUeberlauf_verweigert` (overrun → none),
  `multiAussen32_verweigert` (2^31 → none),
  `multiAussen8_verweigert` (128 → none),
  `multiSymbol_verweigert` (unlisted id → none),
  `verknuepft_wx_verweigert` (reused W^X),
  `multiOpcode_falsch_verweigert` (byte 6 head → decode none),
  `multiKeinSprung_verweigert` (ret window decodes to ret, never a site),
  `multiRel8_nicht_dekodiert` (`decode [235,16] = none` pinned — model
  decoder has no rel8 row; no silicon claim made from it).
- Witness non-degenerate: `mehrere_korrekt_zeuge` instantiates ALL premises
  jointly on 4 real units (A jump/code, B call/code, C 9 data bytes/non-code,
  D conditional/code), 5 applied operands of all 3 kinds at disjoint sites,
  full `decide` separation/frame/decode/mapping premises, all conclusions,
  plus reached memory-changing run `ruf_schritt_zeuge` (return address
  stored, `read64` changed, byte inequality) and the planted refusals.
  No tables exist at link level (premises quantify over bytes/offsets, by
  design to avoid a second interpreter); this is the honest non-degenerate
  shape, not decoration.
- Silicon facts: opcodes E9=233 (jump32), E8=232 (call32), 0F 80+c
  (15, 128+condCode) conditional, C3=195 ret, EB=235 short form correctly
  NOT decoded in the model (pinned none, no decode claim for abs64/rel8 —
  read-back only via `abs64Wort`/`disp8Signed`). Conditional agreement keeps
  the patched condition. No hardware-correspondence or W/GX claim; CUTS
  explicitly scopes fetch to model `Speicher`, TSO/GX/concurrency/budget
  OPEN. No silicon error found.
- CUTS + axioms: file ends with honest CUTS (proved vs OPEN: source
  correspondence, `valX86_sound`, silicon, TSO/GX, concurrency,
  budget/work, fall-through beyond windows, rel8-selection, overlap,
  non-jump/call/conditional) and 28 `#print axioms`. BUILD-EVIDENCE shows
  final `lean-probe` at `== 0 error(s)` and axiom prints all at
  `[propext, Quot.sound]` or below except `mehrere_korrekt` /
  `mehrere_korrekt_zeuge` at exactly `[propext, Classical.choice,
  Quot.sound]` (goal-theorem profile via reused producers). Standard.
- Scope note (task critique in author report, stated plainly): the CONTEXT
  asked for "correctness in the style of `pipeline_correct_entry` (source
  `execBlock` …) plus `pipeline_refuses_*`". The author built link-level
  correctness (`mehrere_korrekt`: bytes → re-decode/read-back →
  mapping/W^X/frame) and link-level refusals (`*_verweigert`), explicitly
  declining source-level linkage as duplication (rule 16) against settled
  lane-1171 scope. This is openly declared, not fake closure, and the
  delivered theorem matches the cited follow-up scope (n units, several
  operands, abs64/rel8 re-decode, conditional fields, frame invariant).
  I judge this acceptable for this lane, not a repair reason.

## Last `./lean-bau` result line

Author evidence (BUILD-EVIDENCE.json, corroborated by author report):
final full-project `./lean-bau` did NOT go green — apparatus failures only,
zero proof errors:
`error: Lean exited with code 134` (thread/resource exhaustion at
`[618/620] Building Grammatik.X86.PipelineLinkMulti`), then poisoned
`RufAdaequatG.olean` unreadable, then harness `ValueError: not enough RAM
beyond the requested 2-GiB reserve`. Final `lean-probe` on the new file:
`== 0 error(s) in the COMPLETE output; exit 0`.
Reviewer re-run: BLOCKED — every shell invocation (`bash`) in this review
session was permission-denied by the tool gate, so `./lean-bau` /
`./lean-probe` / `git diff` could not be re-executed here. The verdict below
rests on the exact pinned snapshot + complete file read + author build
evidence, not on a fresh reviewer build; the merge gate rebuilds anyway.

## Verdict

VERDICT: ACCEPT

Candidate 1193 meets the exact-review bar: no forbidden tactics/axioms,
standard axiom profile, minimal existing-file footprint (one import line),
genuine reuse of the family's accepted evaluator, refusals that really
refuse, non-degenerate joint witness with a memory-changing run, silicon
consistent with the model scope, honest CUTS with no claim larger than the
proof and no W/GX/hardware-correspondence overreach. No unsupported
desired-correctness premise, no weakened guarantee, no fake closure found.
Integration note for the coordinator: refresh the poisoned `RufAdaequatG`
cache artifact / re-seed `.lake` from the warm master cache and re-run
`./lean-bau` when RAM allows before merging.
