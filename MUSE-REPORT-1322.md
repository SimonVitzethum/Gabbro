# MUSE-REPORT-1322

Independent exact review of lane 1321 (candidate head
32278d455bac0a4cf835fa2839abdf9d9ba7f68a, base f92c2649).

## What was done

Reviewed the delivered candidate files only
(`.tmp/review/SNAPSHOT.json`, `.tmp/review/author-1321/PATCH.diff`,
`OWNER-TASK.md`, `BUILD-EVIDENCE.json`, the copied tree
`grammatik/Grammatik/X86/HwTranslateFull.lean` (1078 lines),
`MUSE-REPORT-1321.md`). Never read the author clone or the pinned
hash (no `git show/log/diff` on it). Verified clone
`/home/simon/Dokumente/gabbro-muse/a1322`, branch `muse/1322`
before starting. Ran `./lean-probe` on the exact delivered Lean
file in place and `./lean-bau` on my own clean clone (which holds
no candidate file, so the build result below is the clean-base
result; the candidate-file result comes from the probe plus the
author build log, whose final entry is green).

## Findings per review criterion

- Scope: exactly the three registered files. `Grammatik.lean`
  diff is one appended line
  (`import Grammatik.X86.HwTranslateFull`). No other existing
  file touched.
- `./lean-probe` on the candidate file:
  `== 0 error(s) in the COMPLETE output; exit 0`.
  `#print axioms` for the checked entries: `[propext, Quot.sound]`
  or a subset (several `decide` witnesses depend on fewer).
  Within the standard goal set; no `Classical.choice` needed.
- Forbidden tokens: content search over the candidate file finds
  no `sorry` / `sorryAx` / `axiom` declaration / `native_decide` /
  `unsafe`. The only `admit` substring hits are English words
  ("admits", "admitted") in comments, not the tactic.
- Premise use: every theorem's premises are consumed by its proof
  (agreement lemmas rewrite with `hkan`/`hMiss`/`h`; inversions
  case-split the step hypothesis; `hwVollSchritt_wf` cases the
  step and discharges each arm). No `intro _` / `have _ :=`
  discard, no conclusion restating a premise, no contract
  quantification issue (no program-syntax premises at all;
  rule 13 has no `ZEUGE:` trigger here).
- Lifting, not copying: the family evaluator `seitenGangGross`,
  `tlbSuche`, `tlbEntfernen`, `tlbCr3Spuelung`, `walkLesen`,
  `hwSchritt_wf`, the gross witnesses (`witGrossTab`,
  `witGrossSteuer*`, `wit_gross_*`) and the two-core TSO facts
  (`hwWit_weiterleitung`, `hwWit_fremd_alt`,
  `hwWit_spülung_aendert_speicher`) are all reused by name.
  The earlier `HwVollSchritt` collision with the capstone union
  step (visible in the author's intermediate build log) is fixed
  in the delivered file: the relation is `HwUebersetzVollSchritt`
  and the nine inversions carry the `voll` prefix.
- Refusals are genuine: `vollGp_verweigert` (non-canonical admits
  only #GP), `vollGross_verweigert`, `vollSteuer_verweigert`,
  `vollSchritt_frisch_braucht_miss`,
  `vollSchritt_veraltet_braucht_treffer` are all proved from the
  step inversions, and the concrete `decide` witnesses
  (`witVoll_stal_revoke/smap/smep`, `witVoll_nach_invlpg_fehl`,
  `witVoll_nichtkanonisch_hit`) compute real admissions/faults.
- Witness non-degeneracy: `voll_zeuge` joins 29 conjuncts over
  two cores (stale admit on core 0 vs fault on core 1 for the
  revoked page), a memory-changing fresh write with
  accessed/dirty write-back bits set, flat permissions for the
  2 MiB and 1 GiB pages, and the accepted two-core TSO run
  (owner-only forwarding, drain 0 -> 42). Non-degenerate.
- Silicon: canonical-first #GP ordering is the correct x86 order
  (GP precedes the walk and the cache); INVLPG per-core removal,
  CR3 flush with PCID off, bit positions, error-code meanings and
  the 48-bit canonical width are all stated as named assumptions
  in CUTS, not discharged. No AMD provenance claimed. Vendor
  neutral.
- CUTS honest: lists proved content, named silicon assumptions,
  and the explicit NOT-proved list (no write-probe walk, no real
  OS `FlachStimmtGross` instance, no fault delivery, no W/GX
  simulation, no timing, no stop-class transfer). Claim matches
  proof; no hardware-correspondence or W/GX claim anywhere.

## Last build results

- `./lean-probe` (candidate file, in place):
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (own clean clone, no candidate file):
  `Build completed successfully (691 jobs)`, exit 0.
- Author build log final entry: `== exit 0; 0 error line(s) in
  the COMPLETE output`, `Build completed successfully (688 jobs)`.

## What remains open

Nothing for this review. Merge-time notes (not findings): the
author base (f92c2649) predates this clone's base, so the merger
re-checks the one import line and the `Grammatik.lean` union on
landing; the `voll_zeuge` joint witness is the MECHANISM witness
(the owner task carries no `ZEUGE:` lines and no theorem
quantifies over program syntax).

## Task feedback

Nothing in the task is wrong. One process note: the lane
instruction to copy the candidate file into my own clone for
`./lean-probe` could not be followed literally (file copy into
`grammatik/` is blocked here), so I probed the delivered file at
its delivered path instead; imports resolve against my clone's
`grammatik/` and the output elaborates the candidate's own
definitions and axioms, so the check is exact.

## VERDICT: ACCEPT

CANDIDATE: 1321 32278d455bac0a4cf835fa2839abdf9d9ba7f68a — ACCEPT.
No unsupported desired-correctness premises, no weakened
guarantees, no fake closure.
