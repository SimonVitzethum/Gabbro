# MUSE-REPORT-935: Exact review of author 785 (CAS divergence record)

## Identity

- Clone `/home/simon/Dokumente/gabbro-muse/a935`, branch `muse/935`: verified, match.
- Review materials used (all inside this clone, no other clones touched):
  `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-785/OWNER-TASK.md`,
  `.tmp/review/author-785/MUSE-REPORT-785.md`,
  `.tmp/review/author-785/BUILD-EVIDENCE.json`,
  `.tmp/review/author-785/PATCH.diff`,
  `.tmp/review/author-785/grammatik/.../CasDivergenceRec.lean`,
  `.tmp/HARDWARE-REFERENCES/` (REFERENCES.json + local Intel text snapshot).

## CANDIDATE and VERDICT

- CANDIDATE: 785 `502e5403cc521806c0e8cc3d0927a0411f67f6d5`
  (base `56537272a31df3de5d9b7898bbade91c3de817b8`, identical to this clone's HEAD;
  files: `MUSE-REPORT-785.md`, `grammatik/Grammatik.lean` (one appended import),
  `grammatik/Grammatik/X86/CasDivergenceRec.lean`; status clean per SNAPSHOT.json).
- VERDICT: ACCEPT — bounded acceptance as stated under "Scope of acceptance".
  No repair required; no minimal-repair list.

## What the candidate does (confirmed against PATCH + file)

New leaf module `Grammatik.X86.CasDivergenceRec` reusing canonical vocabulary only:

- `CasDivergenzRec` (`versuche : Nat`, `schranke : Option Nat`; `none` = honest unbounded).
- `divergenzBetrag r := casKosten r.versuche` (the one cost model, reused).
- `divergenzZulaessig s r`: `some K, some B` requires `versuche ≤ K` and `K ≤ B`, else `false`.
- `CasDivergenceRec_verbindung` (TARGET, 8 premises, all used): covered record bound
  + covering summary retry bound + uniform maximum covering `B + 1`
  + `expandBound s 1 = some k` yields admission `= true` and amount `≤ k`,
  derived via `expandBound_keinVerlust` + `omega`, not assumed.
- `ohneDivergenz_keinKostenAnspruch` (3 premises, all used): unbounded record against a
  summary with `retryBound = none` pricing `retryTry` refuses both `kostenSummeOk`
  (via accepted `kostenSummeOk_verweigert_unbegrenzt`) and transfer admission.
- `CasDivergenceRec_verbindung_zeuge`: joint witness — reached 4-step `eP` run
  (table `konto` written by `eSetze`, slot `0 → 5`) + reached two-core locked-add run
  (word observably moved) + covered record `⟨2, some 3⟩` against `blattSummary`.
- Ends with `CUTS:` + `#print axioms` for all three theorems.

## Independent verification (this lane, queued wrappers, no source touched)

- `./lean-probe .tmp/review/author-785/grammatik/Grammatik/X86/CasDivergenceRec.lean`
  (imports resolve against this clone at the candidate's exact base):
  `== 0 error(s)`, exit 0. Axioms reproduced exactly as reported:
  `CasDivergenceRec_verbindung: [propext, Quot.sound]`,
  `ohneDivergenz_keinKostenAnspruch: [propext]`,
  `CasDivergenceRec_verbindung_zeuge: [propext, Classical.choice, Quot.sound]`
  — all within the standard `gabbro_ziel` set, no new axiom.
- Reused-lemma shapes checked in this tree and matching the candidate's use:
  `casKosten n = n + 1` (LockedOps.lean:107), `cas_schleife_unbeschraenkt`,
  `locked_add_zwei_kerne` (11-component existential = the witness `obtain` pattern),
  `lockAddr`, `kostenSummeOk_verweigert_unbegrenzt`, `expandBound_keinVerlust`,
  `blattSummary` (`retryBound = some 4`, spill/fence 0), `blattSummary_schranke`,
  `ziel_ort_einfaden_zeuge` (8-component shape = the witness `obtain` pattern,
  4-step run with `Erw.schreibSlot` memory change).
- Boundary-tightness probe (scratch file in private `.tmp/`, verbatim copies of the two
  defs against the real `blattSummary`, checked with `./lean-probe`): 0 errors.
  Positive `⟨2, some 3⟩` admits with amount `3`; negative mutations
  `⟨5, some 3⟩` (attempts past record bound), `⟨2, some 5⟩` (record bound past
  summary bound) and `⟨2, none⟩` (unbounded) all refuse. Admission is not vacuous.
- Forbidden tactics: grep over the candidate file finds no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`/`intro _`/`have _ :=` (only English "admit(s)" in comments).
  No `Prop`-typed premise; every premise is used (admission premises via
  `rw`+`simp` closure, bound premises via `omega` over `hkEq`; refusal premises via
  the accepted refusal lemma + `rw`). Conclusion is computed, not a restated premise.
- Architecture review: the file adds NO new hardware semantics — no decoder, evaluator,
  encoding, register/REX/width/flag model, fault class, timing claim, or TSO rule.
  It references `lockSchritt`/`casSchritt` vocabulary without redefining effects, so there
  is no invented determinism and no zeroed/ignored defined effect to fault. Undefined
  hardware state is untouched (out of scope, stated in CUTS). Manual provenance
  (Intel SDM 325462-093US: LOCK Vol. 2A 3-565/3-566, CMPXCHG 3-193/3-194) verified present
  in the local text snapshot; it is context only since no new encoding is claimed.
- Scope: PATCH touches exactly the 3 files above. No diagnostic/gift/example/CLI numbers,
  no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no friend-reserved
  optimiser files. No name collisions: none of the 5 new names occur anywhere in
  `grammatik/` at this base. Import-cycle risk: nil (leaf module, only existing accepted
  imports; root change is one appended import line).
- `./lean-bau` on this (unmodified) base: `== exit 0; 0 error line(s)`,
  `Build completed successfully (484 jobs)` — the candidate's 485th job is its new file,
  whose elaboration I verified via the probe above with identical output to the author's
  build log. I did not apply the PATCH to this tree (reviewer owns no source); full
  integration evidence is the author's logged 485-job green build plus the checks above.

## Scope of acceptance (bounded)

Accepted as: a per-program divergence record with transfer admission, the connection from
a covered record bound to the summary work bound over ONE source step, and the joint
refusal for the unbounded case — with a jointly inhabited non-degenerate witness
(table-writing program, two memory-changing reached runs). NOT claimed and NOT accepted
as: which source step lowers to which CAS loop (no `IR.lean` exists), any
progress/fairness/retry-success promise (a covered bound counts attempts, never promises
success), any silicon correspondence, or any new byte/fault/timing semantics.

## Task assessment

Nothing in the owner task was found wrong. The ZEUGE bar is met (joint, non-degenerate,
memory-changing on both sides). The refusal direction exists as a proved theorem, so
cost-bound claims without a covering record are refused, not merely undocumented. Minor
note (not a defect): the refusal section's doc comment cites `cas_schleife_unbeschraenkt`
as context although the proof goes through `kostenSummeOk_verweigert_unbegrenzt`; the
comment's statement about that accepted theorem is true and nothing is mis-claimed.

## Open / not done by this reviewer

Full-project build WITH the candidate applied (not permitted: reviewer owns no source).
No source, control-plane, or live-registry changes made; only this report is owned.
Scratch probe file left in private `.tmp/` (untracked, outside the commit).
