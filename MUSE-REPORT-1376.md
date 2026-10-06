# MUSE-REPORT-1376: Exact review of candidate 1375 (SystemEvaluators)

## Scope

Independent exact review of CANDIDATE: 1375 `9030c336f0a2d7f44d77af1717b24649527add0e`
(base `b1082d447e14f0dfdb98aaf507a91f4ee5590eb4`, files: `MUSE-REPORT-1375.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/SystemEvaluators.lean`).
Review clone `/home/simon/Dokumente/gabbro-muse/a1376`, branch `muse/1376` verified.
The pinned hash was never touched (`git show/log/diff` on it never used);
the candidate was reviewed as delivered FILES under `.tmp/review/author-1375/`.
Own file: only this report. No Lean or existing-file edits in this lane.

## Checks performed

- Forbidden patterns: scanned the candidate Lean file for real `sorry` / `admit`
  tactic / `axiom` declaration / `native_decide` / `unsafe`. No hits (only
  English words `admitted`/`admit` inside prose comments). CUTS block and
  `#print axioms` per main theorem present (11 prints).
- Axioms (independent `./lean-probe` on the delivered candidate file, in place):
  `== 0 error(s) in the COMPLETE output; exit 0`. Reported dependencies:
  `[propext]`, `[propext, Quot.sound]`, or none — a subset of the standard trio,
  matching the author's BUILD-EVIDENCE.json final probe entry.
- Existing files: PATCH.diff touches `grammatik/Grammatik.lean` with exactly one
  appended line (`import Grammatik.X86.SystemEvaluators`) and adds the one new
  file. Nothing else modified; no theorem weakened or deleted.
- Reuse, not copy: no redefinition of `SysSnapAusgang`, `kernMitRegRip`,
  `ArchFehler`, `HwAdapter`, `sysWitStart` or the PREFETCHh evaluator in the
  candidate (only a comment citing `decodePrefetch1287`/`wcAdapter_prefetch_nop`
  as reused, never redefined). Evaluator legs and the `adapterSysEval` plug are
  built over the accepted outcome vocabulary and the `adapterSystem` shape.
- Refusals: register-form PREFETCHW/MSW, wrong reg fields, neighbour
  RDTSCP/XGETBV rows, truncated/empty inputs all pinned to `none` by `decide`;
  old-chain refusal pinned per new row (`kapDecode_nimmt_*_nicht`, 10 decides);
  extended chain `kapDecodeSysEval` proves exact agreement on old-chain rows
  (`kapDecodeSysEval_alt`, schematic) and joint refusal (`kapDecodeSysEval_nichts`).
- Premise use: spot-checked all theorem shapes — every premise (`m`, `c`, `st`,
  `ev`, feature/vm/CPL hypotheses, chain equalities) is threaded into the goal;
  no `intro _`, no Prop-typed premise, no conclusion restating a premise, no
  memory-less "semantics". No theorem quantifies over program syntax, so rule 13
  does not trigger; the joint closed witness `sysEval_zeuge` is provided anyway.
- Witness non-degeneracy: `sysEval_zeuge` joins 9 chain pins, run pins on two
  cores (PREFETCHW core 0 RIP 0x1000→0x1003 with memory provably unchanged,
  WBINVD core 1 →0x1002), CPL-3 CLTS #GP, bit-less PREFETCHW #UD, SYSENTER
  refusal at snap and plug level, and a TSO issue/forward/drain that changes
  ACTUAL shared memory 0-to-42 with owner-only forwarding, plus `SysWf`
  (`sysWitStart_wf`). Verified green by the probe above.
- Silicon: encodings match the architecture (CLTS 0F 06, INVD 0F 08,
  WBINVD 0F 09, SYSENTER 0F 34, SYSEXIT 0F 35, PREFETCHW 0F 0D /1, PREFETCHWT1
  0F 0D /2 memory-only ModRM, LMSW/SMSW 0F 01 /6//4 memory-only, WBNOINVD
  F3 0F 09). Privilege/fault classes are right: hint/cache NOPs advance RIP
  with no memory/buffer effect; CPL!=0 or vm renders CLTS/INVD/WBINVD/WBNOINVD
  #GP; MSR/CR0 rows (SYSENTER/SYSEXIT/LMSW/SMSW) decode but always refuse —
  never silently admitted. LOCK shapes refuse at decode. No flag is
  constrained (undefined flags stay FREE). The `.tmp/HARDWARE-REFERENCES`
  Intel snapshot is not present in this reviewer clone, so SDM-volume citations
  were checked for plausibility only; no silicon fact in the file contradicts
  known encodings. No AMD provenance is claimed. Collapsing LMSW/SMSW into one
  `.msw` refusal row is acceptable (both refuse; no admitted behaviour is
  merged). The feature-bit-gated #UD legs for absent prefetch enumeration are
  explicit caller inputs, not pinned silicon values — vendor-neutral.
- No over-claim: CUTS names SIB/displacement tails, effective-address
  computation, CR0/MSR semantics, cache effects, timing/serialisation/fences,
  and the W/GX bridge as OPEN; states no hardware correspondence beyond
  self-consistency and no width-merge obligations with the explicit reason
  (no register or memory writes exist in this family; every admitted leg
  carries `m.mem` syntactically). Width N/A is stated, not dodged.
- `./lean-bau` on this clean reviewer tree (candidate not applied here):
  `== exit 0; 0 error line(s) in the COMPLETE output` /
  `Build completed successfully (713 jobs).`
  (Candidate's own evidence reports 712 jobs green on its base; the +1 here is
  master having moved on. The candidate file itself probes green above.)

## VERDICT: ACCEPT

CANDIDATE 1375 `9030c336f0a2d7f44d77af1717b24649527add0e` — exactly one verdict:
ACCEPT. No unsupported desired-correctness premises, no weakened guarantees,
no fake closure found.

## What remains open (not a defect of this candidate)

- Maintainer wiring: add the `syseval` arm for `sysEvalDecode` in last position
  of `kapDecode` (after the `avx2` arm); `kapSysEval_*` state the required
  behaviour. Deliberately left to the maintainer per lane rules.
- Merge gate `lean-layout --apply` is expected to move the module to
  `Befehle/System/` per rule `^System\w+$` and rewrite the import (disclosed
  by the author).
- The `SysExtra` nine, SMSW register forms, SIB/displacement tails, CR0/MSR
  semantics, and the W/GX bridge stay with their own lanes (all named in CUTS).

## Task issues

- None blocking. The author's note that its `.tmp/LANE.md` copy truncates the
  FAMILY paragraph mid-sentence is plausible but did not harm the result: the
  nine reconstructed rows match report 1365's OPEN list and the refusal
  structure, and the module is shaped so rows can be swapped without touching
  the chain/adapter/witness pattern.
