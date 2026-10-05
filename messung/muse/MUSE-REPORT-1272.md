# MUSE-REPORT-1272 — exact review of candidate 1271 (new snapshot, full review)

CANDIDATE: 1271 e22bc7aefa53a553aaa16d286f0ef14129337d8c
VERDICT: ACCEPT

## Identity and snapshot
- Clone: `/home/simon/Dokumente/gabbro-muse/a1272` — verified.
- Branch: `muse/1272` — verified (`git branch --show-current`, `git status` clean).
- Pinned snapshot `.tmp/review/SNAPSHOT.json`: author 1271,
  head `e22bc7aefa53a553aaa16d286f0ef14129337d8c`,
  base `c8bb42086282d1e2a7c5874a40303e7f060d3fad`, clean, files
  `MUSE-REPORT-1271.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/TsoGxEntryBytes.lean`.
- The commit object is absent from this clone (isolation: no fetch), but the
  coordinator delivered the full review material inside this clone under
  `.tmp/review/author-1271/` (`PATCH.diff`, the two Lean files,
  `MUSE-REPORT-1271.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`). This review
  inspects that delivered material only — no author-clone access, no fetch.
- The previous blocked verdict (no material delivered) is superseded by this
  full review; nothing is approved from the stale snapshot. Per build evidence,
  commits after `c73645e2` touch only the author report wording, so the Lean
  deliverable is unchanged; it is reviewed here as delivered, not by history.

## Candidate scope (PATCH.diff vs base)
- Exactly three files: new `MUSE-REPORT-1271.md`, one appended import line
  `import Grammatik.X86.TsoGxEntryBytes` at the end of `grammatik/Grammatik.lean`,
  new module `grammatik/Grammatik/X86/TsoGxEntryBytes.lean` (528 lines).
- No other existing file touched. `OptimizationRules.lean` /
  `OptimizationWitnesses.lean` untouched. No Rust, no new IR, no second
  interpreter, no new machine, no new decoder.
- Delivered `.lean` file matches the PATCH hunk: hunk header `+1,528`, file
  528 lines, full read of both identical; delivered `Grammatik.lean` ends with
  exactly the one appended import.

## Gate checks
- Forbidden tokens (`sorry`, standalone `admit`, `axiom` declarations,
  `native_decide`, `sorryAx`, `unsafe`, `split_ifs`, `norm_num`, `ring_nf`):
  zero matches by grep. Only hits are English prose "admitted" (twice,
  disclosed by the author) and the required `#print axioms` block (13 lines).
- Premise discards (`intro _`, `have _ :=`): zero matches.
- `#print axioms`: author-side build output (BUILD-EVIDENCE.json, final
  `./lean-bau`, 658 jobs green) shows every main theorem at most standard
  `propext, Classical.choice, Quot.sound`, `giftPrologCfg` axiom-free,
  `StapelLayoutFremd`/`worldRep_schreiben_fremd`/`gift_prolog_clobber_grund`
  at most `propext`. I could not re-execute the candidate build inside this
  clone (that would dirty owned-outside files with no revert available), so
  the axiom printout rests on author-side evidence plus the fact that every
  proof step uses only standard tactics over accepted lemmas — recorded
  honestly as the one non-independently-reproduced item.
- Every premise used (audited by reading, all proofs):
  `worldRep_schreiben_fremd` consumes `hW`/`hwr`/`hf`;
  `eintrittCallPrefix_lauf` feeds 19 premises to the accepted
  nested-restoration theorem and consumes `hpro` (run composition),
  `hrsp0` (stack-top join), `hsrc` (call preserves pushed value);
  `byteKopf_antwortErhalten` consumes the entry premises via `prolog_lauf`,
  `hW0`/`hfremd`/`hvar` via the two foreign-store transports and
  `envRepr_fremd`, and all 19 byte premises via the prefix theorem;
  all three refusals pass every premise to their accepted theorem.
  Three `-` patterns discard unneeded obtained conjuncts (the `prolog_lauf`
  rip equation, the `ReqAmEintritt` side fact, permission conjuncts the
  witness statement does not claim) — none is a premise of the theorem
  being proved; judged acceptable and recorded here.
- Accepted evaluator lifted, not copied: all force comes from accepted
  theorems verified present in-tree with matching signatures —
  `geholt_verschachtelt_wiederhergestellt` (argument order and 10-tuple
  conclusion match), `prolog_lauf` (5-tuple matches the obtain pattern),
  `schritt_call32/push64/pop64_reg/ret_erfolg` (all four signatures match
  the applications), `read64_rahmen`, `read64_nach_write64`,
  `write64_rahmen`, `writeBytesN_hit`, `lesbar8/schreibbar8_nach_schreiben`,
  `laufBytes_add`, `prologOk_teile`, `envRepr_fremd`, `byteschritt_geholt_*`,
  `startFragment_zeuge` (8-tuple shape matches), and the `nest*`/`wacheNest*`/
  `retNest*` fixtures plus `eD/eP/eO/eSp/eSetze/ePruefe` from accepted
  `ZielOrtEinfadenZeuge`. `WorldRep`/`RepSlot` shapes match the frame proof.
  No canonical definition duplicated; new items are only the admission
  predicate `StapelLayoutFremd`, the gift config, and the linkage theorems.
- Refusals really refuse: the three refusal theorems are thin wrappers over
  accepted loud-refusal theorems; the poison probes are closed proofs over
  accepted concrete witnesses (`wacheNestS` guard states verified present,
  `retNestS` with its non-executable target, `giftPrologCfg` with a
  `decide`-proved interference fact). Nothing is refused vacuously.
- Witness non-degenerate (`eintrittCallPrefix_zeuge`, closed, no premises to
  jointly instantiate): source side reaches from `RufStartG` with a
  `schreibt = true` table and observable `0 → 5` change (via accepted
  `startFragment_zeuge`); byte side runs 4 fetched steps with the frame
  written through memory, return word read back, the same byte provably
  different, `rsp` restored. Memory-changing on both sides.
- Silicon: no new hardware facts. Only existing `Befehl` forms and `encode`
  are referenced (CALL rel32 with its 5-byte length used consistently;
  sign extension lives in accepted `dispWort`). No correspondence claim
  beyond the proved transport.
- CUTS honest, claim not larger than proof: lowering identity booked OPEN
  with the pipeline owners (correct — identity across machines is unstatable
  here without their certificate, and assuming it would violate rule 4a);
  no TSO/GX bridge claimed (sequential `Speicher` throughout, stated);
  one-nest limit, `dst/src ≠ rsp`, disjoint slots, pilot ISA, one core,
  model memory, no time — all stated. The task-fit note in the author
  report is agreed with, not a finding.
- `./lean-bau` in this clean clone (baseline, not the candidate):
  `Build completed successfully (659 jobs).`

## Findings
No semantic findings. Two remarks, neither verdict-relevant: the doc comment
"every premise is consumed by the accepted nested-restoration theorem" is
slightly imprecise (`hpro`/`hrsp0`/`hsrc` are consumed outside it, still
inside the proof); and the author report's review-response section describes
the superseded blocked round, which is history, not a claim about this
snapshot. No weakened guarantee, no desired-correctness premise, no fake
closure found.
