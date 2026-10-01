# MUSE-REPORT-615: Independent closure review of 603

CANDIDATE: 603 e48a5743b73c8a78e0cf23c7ab392f1e6328f4e5
VERDICT: ACCEPT

## Scope and method

Reviewed lane 603 ("Whole-word grouping under actual trace exclusion") against
its committed task (`lanes/603.md`), the review snapshot
(`.tmp/review/SNAPSHOT.json`: head `e48a57…`, base `0044c258`, files
`MUSE-REPORT-603.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/WordAccessGrouping.lean`), the full candidate file
(959 lines, read in full), the PATCH diff, and the author's report and build
evidence. Reproduced the Lean checks independently: candidate file plus its one
import line applied to a fresh checkout of current master (`838a1c22`), then
`./lean-probe` on the file and full `./lean-bau`. Temporary verification files
were reverted afterwards; this commit is report-only.

## Findings

- **Build, reproduced (not trusted from the report):** `./lean-probe
  grammatik/Grammatik/X86/WordAccessGrouping.lean` →
  `== 0 error(s) in the COMPLETE output; exit 0`. Full `./lean-bau` →
  `== exit 0; 0 error line(s) in the COMPLETE output`, 453 jobs,
  `Build completed successfully`. The author's own `BUILD-EVIDENCE.json`
  contains no completed build output (probe attempts hit the tool timeout and
  the commit proceeded without collected green lines), so the report's claimed
  build lines were unevidenced at commit time — now independently confirmed
  green here.
- **No forbidden content:** no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (two grep hits are prose: "admits"). No `intro _` / `have _ :=` discards.
  Only linter warnings are unused-variable notes on `∀`-binders of
  `drain_installiert_aux` (false positives: `hstoer`/`hbuf`/`hmem` are all
  consumed via `hstoer'`/`hhead`/`hmem'` in every `DrainSchritt` case).
- **Axioms:** every `#print axioms` line is `none`, `propext`, or
  `propext + Quot.sound` — a subset of the standard goal set.
- **Execution connection is genuine:** `wortEintraege` pins the exact
  eight-entry own-buffer shape; `FremdFrei` quantifies over real pending
  buffer entries of other cores (`e ∈ s.puffer d → e.addr ∉ Fuss a`); the
  exclusion hypothesis `∀ x ∈ t, FremdFrei x c a` is required at every visited
  trace state and is consumed at each foreign step
  (`drain_installiert_aux`, `drain_fuss_bleibt_aux`). No desired end state or
  source simulation is asserted. No new executor or transition is added:
  `DrainSchritt` wraps only existing `flushKern`/`issueByte`,
  `drain_spur_erreichbar` ties every trace to `TSOErreichbar`.
- **All premises used:** checked `wort_gruppe_liest_zurueck` (group pins start
  buffer, readability feeds the final load, trace + end-membership feed the
  installed-prefix induction, emptiness forces `k = 8`, exclusion covers
  foreign steps) and `wort_gruppe_rahmen` (additionally honest about needing
  the check at the framed footprint `FremdFrei x c b`, after the first frame
  attempt proved false — recorded, not hidden).
- **Witnesses jointly inhabited and non-degenerate:** `grpS2..grpS10` is a
  concrete eight-flush drain with each step `rfl`, `TSOErreichbar`, foreign
  buffers provably empty, `read64 … = some zeugenWort`, and genuine memory
  change (`zeugenSpeicher` zeroed, `zeugenWort = 0x0102030405060708`, byte 0
  `0 → 0x08` closed by `decide`). Tearing refusal reuses the real shared
  `hS2`/`hS3`/`hist_zerreissen` witnesses; `ausrichtung_reicht_nicht` refuses
  an aligned non-group by computed buffer length. The theorems quantify over
  TSO states rather than source syntax, so hard-rule 13's program-syntax clause
  does not strictly apply — the author still exceeded it with reached
  memory-changing runs.
- **Bounded scope, no overclaim:** `GruppeNachW` is an empty inductive with
  `keine_gruppe_nach_w`; no source/checker/contract, no W/GX bridge, no
  hardware multi-byte atomicity, no fairness/LOCK-refinement claims.
  `gruppe_verweigert_lock` keeps byte drains and LOCK updates disjoint.
  Touched paths are exactly the three owned files; the `Grammatik.lean` change
  is one appended import; no Spec/checker/optimiser edits. (Note: the
  snapshot's `Grammatik.lean` copy predates current master, so the merger
  unions the import against the newer tail instead of applying the stale
  context — content is unaffected.)

## Bounded accepted scope

`WortGruppe`/`FremdFrei`/`DrainSpur`, `wort_gruppe_liest_zurueck` (+`_zeuge`),
`wort_gruppe_rahmen` (+`_zeuge`), `realisiert_store_gruppe_treu`,
`gruppe_fuss_form`, `ausrichtung_reicht_nicht`,
`riss_unter_verweigerter_gruppe`, `drain_spur_erreichbar`,
`gruppe_verweigert_lock`, and the explicit `GruppeNachW` gap for bridge owners
573/574. Nothing outside `WordAccessGrouping.lean` plus its import line.

## Open / next (not started, exact ownership for others)

- N1 (new lane, own new file): exclusion-checked drain with interleaved
  foreign issues in the witness (lemmas already cover the shape).
- N2 (bridge owners 573/574): consume `wort_gruppe_liest_zurueck` for the
  per-access W store/read bridge; `GruppeNachW` names the remaining gap.
- Process note (no repair needed): lane 603's build-evidence practice —
  committing claimed green lines without collected output — should not be
  copied; reviewers re-ran everything here.

Last `./lean-bau` result line (with candidate applied, before revert):
`== exit 0; 0 error line(s) in the COMPLETE output` (453 jobs).
Nothing in the task statement is believed wrong.

Co-Authored-By: muse-agent-615 <muse-agent-615@noreply.invalid>
