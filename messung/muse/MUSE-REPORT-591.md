# MUSE-REPORT-591: Independent exact-candidate connection review of 573

Lane 591, clone `/home/simon/Dokumente/gabbro-muse/a591`, branch `muse/591`.
OWN ONLY: `MUSE-REPORT-591.md` (this file). No Lean, Rust, checker, Spec,
goal, emitter, or friend-file change.

CANDIDATE: 573 c873c3ee775f3e2e4fdba7fe56558020b6e7f1ad
VERDICT: ACCEPT

## Scope verified

- Snapshot `.tmp/review/SNAPSHOT.json`: single entry, author 573, pinned head
  `c873c3e...`, base `377b290e...`, files `MUSE-REPORT-573.md`,
  `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/BridgeWrite.lean`, clean true.
- Patch diff confirms owned paths only: one new 323-line module plus one
  additive umbrella import plus report. No source checker, Spec, goal,
  emitter, or `OptimizationRules`/`OptimizationWitnesses` edit.
- Owner task 573 reviewed: consume accepted TSOHistory567 and SourceMemory570
  interfaces with real W access semantics; per-access issue/flush to source W
  write with FIFO order, stutter, visibility-vs-issuing, word guard, value
  representation; two-core reached memory-changing joint witness plus
  tearing/foreign-drain refusal; obstruction labelled blocked if not closable.

## Independent inspection

Read the full candidate `BridgeWrite.lean` (323 lines) against the live
producers in this clone: `TSOHistory.lean` (346 lines), `SourceMemory.lean`
(594 lines), `WordAtomicity.lean` (361 lines), plus `TSO.lean`/`Speicher.lean`
definitions. Every referenced name resolves to a real accepted definition or
theorem: `issueByte`, `flushKern`, `flush_rahmen`, `paket_reisst`,
`fifo_reihenfolge`/`fifo_hist_konsistent`, `histVon`/`sichtVon`/`Lesbar`,
`hist_zeuge_gelenk`, `rep_schritt_bleibt`/`rep_schritt_bleibt_zeuge`,
`repOk`/`RepSlot`/`zahlWort`/`wortZahl`, `WortGuard`, `write64`/`read64`/
`lesbar8`/`schreibbar8`/`ausgerichtet8`, `Fuss`/`schreibEreignisse_acht`,
`sbX`/`sbY`/`sbEins`/`sbStart`/`sbNach2`/`sbGespült`/`wortRiss2`/`wortRiss3`,
`zeugenSpeicher`/`zaunBereit`/`loadByte`, `witD`/`witM`/`witA`/`witVal`/
`witSigma`/`witO`/`witR`/`witI`/`witE`/`witHw`/`witHL`/`witSL`/`witHT`.
No forged decoded input, no guessed ISA or FP fault, no second IR or
duplicated executor, no new TSO transition.

Statements checked:

- `issue_beobachtet_bleibt`, `issue_rep_bleibt`: genuine stutter over
  `issue_kein_speicher`; canonical memory byte-identical, so `read64` and
  `RepSlot` preserved. All premises used (`hm` moves TSO to representation
  memory, `hRep` carried, `h` the step).
- `flush_nur_ein_byte`: one `flushKern` changes at most one address via
  accepted `flush_rahmen`; two distinct changed addresses give `False`.
  Proves the word guard is necessary; a single flush is never a carrier write.
- `riss_im_fuss`, `riss_gemischt_verweigert`: concrete `decide` facts; both
  tearing bytes sit in `Fuss 0`; after first flush word holds mixed halves.
  Real tearing refusal, not a toy shape.
- `bruecke_schritt_rep`: one real `execStmt` over `Stmt.assignSlot` plus
  matching guarded `write64` under checked `WortGuard` yields `RepSlot` plus
  `wortZahl` roundtrip, derived via accepted `rep_schritt_bleibt` (which
  unfolds `execStmt`). No simulation premise taken. All premises used;
  readability from the guard feeds the source step; all four guard facts are
  re-concluded for the consumer. The guard conjuncts in the conclusion
  restate checked premises, but the `RepSlot` plus roundtrip conjuncts are
  genuinely new, so this is not a copied-premise theorem.
- `bruecke_fifo_stutter`: composes accepted `paket_reisst` with
  `fifo_hist_konsistent`; older byte committed and history-readable, younger
  byte still pre-flush stutter. Correct safe direction noted (W admits any
  fresh-timestamp order; TSO FIFO is the admissible choice).
- `bruecke_fremd_kein_wort`: concrete fence-ready core 0 coexisting with
  core 1 forwarding `7` past committed word `0`; forwarded value differs
  from `wortByte w 0`. Proved foreign-drain refusal.
- `bruecke_schritt_rep_zeuge`: joint witness reusing
  `rep_schritt_bleibt_zeuge` (slot `0 -> 42`, bytes changed) plus TSO guard
  state over the same `witM` with empty buffers and decided alignment and
  permissions. Non-degenerate: one table its function writes, reached
  memory-changing run both sides.
- `bruecke_zeuge_gelenk`: pairs accepted `hist_zeuge_gelenk` (two-core
  reached `sbStart -> sbNach2`, stale loads, flush changes `sbX`, history
  readable) with the admitted slot write `0 -> 42` and changed word.
  Non-degenerate both sides; the two sides share word vocabulary but stand
  over different memories, so linkage is side-by-side rather than causal.
  Recorded as a limit, not a defect.
- `BrueckenProfil` (`repOk`) plus `brueckenProfil_zeuge` (int admitted,
  bool refused): exact admitted profile with planted refusal.

Rule checks: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (exact-word
grep clean); no `Prop`-typed premise; no `intro _` or dropped premise; no
`forall rho`/`forall v` contract weakening (concrete `k`/`v` with `hk`/`hv`
at entry); widths correct via `repOk_klingt` and `zahlWort_wortZahl`
(`0 <= lo`, `hi < 2^64`); witnesses jointly instantiate premises on
non-degenerate shapes, so not vacuous; CUTS block present with `#print
axioms` for every main theorem; reported axioms within
`propext`/`Classical.choice`/`Quot.sound`.

Build history in `BUILD-EVIDENCE.json`: intermediate 3-error probe during
development was repaired; final `lean-probe` 0 errors and full `lean-bau`
exit 0, 0 errors, 441 jobs, green. No Rust touched, no network, no push, no
other clones.

## Accepted bounded claim (not full closure)

- Buffered byte issues are stutter at word and carrier level; visibility
  needs a flush.
- One flush moves at most one byte; whole-word claims need the atomicity
  guard; byte-issue sequences tear (proved mixed-halves refusal).
- A guarded whole-word `write64` install that matches a real source
  `assignSlot` step establishes `RepSlot` plus parse-back roundtrip for the
  admitted `.int` profile, with FIFO order and foreign-drain limits as
  proved refusals.
- Explicitly NOT claimed: per-access `SchrittW` (`wahl`/`neu`) assembly from
  drained byte packets, carrier-granular `Frisch` transfer, W/GX run
  induction, lowering map, `valX86_sound`, source-to-final-bytes closure.
  The module CUTS labels this OPEN with the byte-vs-carrier granularity
  obstruction and the needed O-access decomposition. That honesty is why
  this is accept-as-bounded rather than exaggerated closure.

## Producer/consumer interface and next integration

- Producer 573 hands consumer BridgeRead574: `RepSlot`-at-word plus guard
  (`bruecke_schritt_rep`), FIFO/stutter (`bruecke_fifo_stutter`),
  tearing (`riss_gemischt_verweigert`), foreign (`bruecke_fremd_kein_wort`),
  single-flush frame (`flush_nur_ein_byte`), same `histVon`/`sichtVon`/
  `RepSlot` vocabulary.
- Measurable next step as stated: packet-drain lemma (8 ordered flushes of
  one word packet equal one `write64` effect) feeding a `SchrittW`
  constructor once O-access lands; then the load side in 574.

## Minimal follow-ups (not blocking)

- In a follow-up, separate the guard re-export conjuncts of
  `bruecke_schritt_rep` from the derived `RepSlot`/roundtrip, or prove the
  packet-drain equation so the `write64` premise is itself a TSO flush
  consequence rather than an assumed matching install.
- In a follow-up, make the two-core joint witness share one memory
  (`witM` versus `sb*` addresses) if a single-memory joint trace is wanted;
  current pairing is side-by-side and sufficient for non-vacuity.

## Verification by reviewer

- No Lean files changed on `muse/591`; `git status` clean except this
  report. No queued build owed for a report-only lane; candidate build
  evidence above verified from snapshot. No credentials read, no network,
  no push, no other clones touched, no user processes disturbed.
- Last `./lean-bau` result line for this lane: not run (report-only, no
  Lean delta); candidate evidence: `== exit 0; 0 error line(s) in the
  COMPLETE output`, `Build completed successfully (441 jobs)`.
- Nothing in the owner task was wrong; the `SchrittW`-packaging remainder is
  correctly left OPEN and owned by the follow-up bridge.
