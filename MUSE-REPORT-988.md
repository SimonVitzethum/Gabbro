# MUSE-REPORT-988: Exact review of author 838 (atomic-ledger closing)

## CANDIDATE

CANDIDATE: 838 f1fb50980304ea4c0f99dedc2e8d6e4f86b0a0da

## VERDICT

VERDICT: ACCEPT (bounded — see acceptance boundary below)

## What was reviewed

Author 838 task (lane 838, composition closing: atomic-ledger closing):
close every shared atomic access to its ledger entry (ordering, RMW field,
success/failure); unlogged shared access refuses. New module
`grammatik/Grammatik/X86/ComposeAtomicLedger.lean` (408 lines) plus one
import line appended at the end of `grammatik/Grammatik.lean`. TARGET
`ComposeAtomicLedger_verbindung` with companion
`ComposeAtomicLedger_verbindung_zeuge`.

Review material inspected (all inside this clone, no other clones touched):
`.tmp/review/SNAPSHOT.json` (head, base, file list, clean flag),
`.tmp/review/author-838/OWNER-TASK.md`, `MUSE-REPORT-838.md`,
`BUILD-EVIDENCE.json` (22 queued-wrapper runs with outputs), `PATCH.diff`
(496 lines, full new-file content), the snapshot copy of the new Lean file,
and the official local reference index
`.tmp/HARDWARE-REFERENCES/REFERENCES.json` (Intel SDM 325462-093US,
September 2026; AMD retrieval failed, no AMD claim). Every producer name
was resolved against this clone at the snapshot base
(e7c75908456285d1e37c18dc32d4f9c0e10d1fa4, identical to this clone's HEAD).

## Independent verification (static; no execution available)

No command execution was available in this review session (all `bash`
tool calls, including the queued wrappers `./lean-probe`/`./lean-bau`,
were refused by the permission layer), so no build was re-run here.
Verification below is static cross-checking of the exact pinned content
against the base tree, plus the author's recorded wrapper evidence:

- Banned tactics: the candidate Lean file contains no `sorry`, `admit`,
  `axiom` (except `#print axioms` lines), `native_decide`, or `unsafe`.
  Checked by full-text search of the snapshot file.
- Producer lemma shapes, checked against base-tree statements:
  - `lock_xadd_atomar` concludes a 9-conjunct; the candidate's
    `xadd_eintrag_aus_schritt` destructures exactly 9 components and
    takes conjuncts 1/4/5 (`istRmw`/`gelesen`/`geschrieben`). Arity and
    order match.
  - `mfence_ordnung` concludes a 5-conjunct; `zaun_eintrag_aus_schritt`
    takes conjuncts 3/4/5. Match.
  - `cas_erfolg_schreibt` concludes a 4-conjunct; the candidate takes
    conjuncts 1/2. Match.
  - `cas_fehlschlag_stottert` concludes
    `bytes-eq ∧ puffer-eq ∧ bok = false`; the candidate rewrites the
    goal with that equation (`rw [hbok]`) to close
    `(ledgerCasOk a bok).erfolg = some false`. Sound use.
  - `freigabe_braucht_flush` / `zaun_erwerb_liest_kanonisch` / 
    `zaunBereit_iff_leer` applications in `ordnung_eintrag_aus_schritt`
    and in the witness match the accepted signatures argument by
    argument (`sb_schritt1`, `1 ≠ 0` by `decide`, empty-buffer `rfl`,
    readability `by decide`).
- Witness shapes, checked verbatim against `LockedOps.lean`,
  `TSO.lean`, `TSOHistory.lean`:
  - Conjunct 1 = `hist_zeuge_gelenk.1` (`TSOErreichbar sbStart sbNach2`)
    plus `sb_flush_aendert_speicher` (memory-changing flush). Match.
  - Conjuncts 2–5 are exactly `locked_add_zwei_kerne` (two-core
    0 → 12 with per-core RMW events), `cas_erfolg_zeuge` (installs 9,
    read back), `cas_fehlschlag_zeuge` (stutter), `mfence_ordnung_zeuge`
    (fence with foreign pending store). Match verbatim.
  - Conjunct 6 (release-invisible foreign load + fence-ready acquire)
    applies the two accepted ordering facts to `sbStart/sbNach1`.
    Conjunct 7 is the empty-ledger refusal. Non-degenerate: real
    buffered stores, real RMW events, memory-changing steps, a foreign
    pending store. The task's "reached memory-changing runs plus
    planted refusal cases" requirement is structurally met.
- Premise use: every premise of the five producer-connection theorems
  flows into the single accepted lemma it delegates to; no `intro _`
  or dropped hypothesis anywhere in the file.
- Axioms: author's recorded `#print axioms` output for all 16 theorems
  is within `[propext]` / `[propext, Quot.sound]` / none. Standard;
  `gabbro_ziel` is untouched.
- Scope hygiene: diff touches exactly the three owned files; no
  diagnostic/gift/example/CLI numbers, no MARKE_EMIT, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files. Import appended at the end of `Grammatik.lean` as required.
- CUTS: precise, with owning lanes named (bridge 573/574 for per-access
  W/GX refinement, `AtomicPayload` lane 350 for source-carrier
  admission, consumers 776/778/779/784 for fetch/decode linkage), plus
  explicit no-tearing-beyond-guarded-LOCK-word, no-time/fairness/
  progress, no-source/checker/goal-change statements.
- Build evidence: author's `BUILD-EVIDENCE.json` records incremental
  `./lean-probe` runs (including one honest intermediate `rfl` failure
  on `ledgerDeckt` with free variables, repaired with `unfold`+`simp`)
  and a final whole-project `./lean-bau` green at 509 jobs with the
  per-theorem axiom prints. Plausible and internally consistent; not
  independently re-executed here (see blocker note).

## Architecture review (hardware substance, not just Lean green)

- No new byte forms, decoders, executors, register/flag/MXCSR models, or
  interrupt gates are introduced; the module works at TSO-state
  granularity reusing accepted steps. It therefore makes no new hardware
  claim at those layers — correctly, since its CUTS disclaim
  fetch/decode linkage to the named consumer lanes.
- Ordering/RMW/outcome bookkeeping: loads/stores carry their ordering;
  both RMW forms are pinned to `.freigabe`, the accepted
  release/acquire over-approximation of `seq_cst` (owned by
  `ReleaseAcquire`, not re-proved here). The fence entry's release
  order is a ledger convention; no theorem reads it back into a
  hardware conclusion. No invented determinism, no zeroed defined
  effects, no unsound abstraction of undefined state.
- Guards are preserved, not bypassed: every producer connection
  requires the same guards as the accepted step (empty local buffer,
  `read64` hit, 8-alignment, successful `write64`, equality test
  outcome, readability, fence readiness). Pre-fault effects and
  TSO/atomicity semantics stay owned by the producers.
- Negative mutations are genuine computations, not vacuous: a
  relaxed-only ledger refuses an acquire load (ordering field), and a
  plain-store entry refuses an XADD (RMW field, backed by accepted
  `rmw_nur_mit_lock`). Positive control `xadd_eintrag_gefunden`
  present. No guarantee is weakened: the composition claims no W/GX
  refinement and no source-carrier admission (both CUT with owners).
- Minor precision nit (not verdict-relevant): the file header comment
  names `RmwForm`, `WortGuard` (WordAtomicity) and `ReleaseSchreiben`
  (ReleaseAcquire) as reused vocabulary, but none of the three is
  referenced by any definition or theorem body, and the `WordAtomicity`
  import is unused. Documentation overstatement only; no semantic
  effect. Suggested follow-up: correct the header or drop the import.

## Acceptance boundary

ACCEPT covers: the ledger-closing composition as stated — every shared
atomic access closes to its addressed/ordered/RMW-tagged/outcome-recorded
entry over arbitrary admitted inputs, unlogged access refuses, with a
joint non-degenerate reached memory-changing witness. Explicitly NOT
covered (per the file's own CUTS, endorsed): per-access target-to-W/GX
simulation, source-carrier (`GeteiltV`/`AtomicPayload`) admission,
fetch/decode linkage, tearing beyond the guarded LOCK word update, and
any timing/fairness/progress claim.

## What remains open

- Integration of this candidate (merge + fresh publication checks) is
  outside a report-only review.
- The header-comment/import nit above is left for the author or merger.
- No re-execution of the build was possible from this session (blocker
  note below); the merger's standard gates (source build, axioms, tests,
  emission, key scan) still apply before publication.

## Task assessment

Nothing in the lane-838 task was found to be wrong. The ZEUGE companion
requirement is satisfied jointly and non-degenerately as specified.

## Blocker / honest partial status

Command execution was partially available in this session: directory
listing commands were refused, and the queued Lean wrappers
(`./lean-probe`, `./lean-bau`) could not be run from here, so (a) the
green build could not be independently reproduced and review evidence
is the author's recorded wrapper outputs plus static cross-checking.
Committing (`git`, `./commit.sh`) worked; this report is committed as
49d6b052 on `muse/988`. All review findings above are fully stated. The
merger's standard gates (source build, axioms, tests, emission, key
scan) still apply before publication.
