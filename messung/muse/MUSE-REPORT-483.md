# MUSE-REPORT-483: Independent exact-candidate review of 435 (DecodingCoverage)

## Clone / branch verification

- Clone `/home/simon/Dokumente/gabbro-muse/a483`, branch `muse/483`: MATCH (verified before any other step).
- Candidate pinned HEAD from `.tmp/review/SNAPSHOT.json`: `e964d8d7bbcdb1da3ec2e017484d38470dfb87e5`, base `2b0d29cffaa7b41971f0820d9a752ec685c00ad6`, files `MUSE-REPORT-435.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/DecodingCoverage.lean`, `clean: true`.
- Candidate commit is NOT present in this clone (isolated review, no other clone read, no fetch). Review ran against the supplied exact files under `.tmp/review/author-435/` (PATCH.diff + grammatik/ + MUSE-REPORT-435.md + OWNER-TASK.md + BUILD-EVIDENCE.json). Supplied file is 756 lines; PATCH adds exactly 756 lines for that path, so supplied content matches the pinned diff.
- Base `2b0d29cf` is an ancestor of this clone's HEAD. Canonical dependencies (`Codec.lean`, `Byteschritt.lean`, `Bild.lean`, `Typen.lean`, `Speicher.lean`, `Ausfuehrung.lean`) are byte-identical between base and this HEAD (`git diff --stat base..HEAD` empty for all six), so semantic checks against this clone's models apply to the candidate. The umbrella `Grammatik.lean` tail moved on after the base (now ends with `WordAtomicity`, `RegisterInterference`, `ObservationProjection`, `GateStub`, `ReleaseAcquire`); the candidate's one-line additive import needs a trivial mechanical rebase. No semantic conflict.

## What the author delivered (bounded claim)

New module `grammatik/Grammatik/X86/DecodingCoverage.lean` (756 lines, no other code file touched) plus one additive umbrella import. Verified structure from the supplied file:

- Defs: `eintrittFenster` (loaded-image entry window via `ladenByte`), `eintrittDekodiert` (`decode` over that window capped at `fetchCap`), `decktAb` (coverage shape over all 14 `Befehl` constructors with exact lengths 1 / 1-or-2 / 3 / 10 / 7-or-8 / 5 / 6), witness data `dcReg`, `dcStart`, `dcEintrittCode/Daten/Datei/Bild/Start`, `dcAbholProg/Bytes/Speicher/Start`.
- Theorems: `parseLe32_suffix`, `parseLe32_len`, `parseLe64_suffix`, `parseLe64_len`, `decodeRegReg_abdeckung`, `decodeMem_abdeckung`, `decodeModrm_abdeckung`, `decodeRex_abdeckung`, `decode_abdeckung` (main: length equation + `laengeOk` + `decktAb` + prefix split, decoder side only), `decode_fenster_kongruenz`, `fetch_fenster_kongruenz`, `geholt_schritt_aus_decoder`, `eintritt_abdeckung`, five `decode_nichts_*` refusals, three `_zeuge` witnesses. No new definitions/theorems were added by this reviewer.

## Independent checks performed in this clone

1. Staged ONLY the supplied candidate files temporarily (candidate module + one appended umbrella import), then restored. `git status`/`git diff` empty after restore; this commit contains only this report.
2. `./lean-probe grammatik/Grammatik/X86/DecodingCoverage.lean`: `== 0 error(s) in the COMPLETE output; exit 0`. Per-theorem `#print axioms` reproduced exactly: every theorem depends only on `[propext]` or `[propext, Quot.sound]`; no `sorryAx`.
3. Full `./lean-bau` with candidate staged: `Build completed successfully (418 jobs)` (author measured 393 jobs on the older base; the +25 is later master content, expected).
4. Banned items: `grep` for `sorry|admit|axiom|native_decide|unsafe` excluding `#print axioms` lines returns nothing; no `intro _` / `have _ :=` premise discards; no `Prop`-typed premises; every premise is used (each `h : ... = some ...` drives its case analysis; all binders appear in conclusions).
5. Decoder-side-only claim verified: the file never invokes `encode` or `roundtrip` outside comments; the inner-level uniform statement (`pre.length + OUTER = d.laenge`, OUTER 3/2/1/0) is the correct compositional form and the top level additionally yields the plain length equation.
6. Fail-closed shapes verified new vs `Codec.lean`'s 15 existing refusals: `[73,184,8,7,6,5,4,3,2]`, `[72,139,141]`, `[6]`, `[72,137,69]` (mod=1), `[15,128]` are all distinct byte strings, all `rfl` (kernel-computed, not asserted).
7. Witnesses verified non-vacuous: all three prove a real memory-changing step by `decide` (store 42: pre-state byte 0 at the data address, post-state 42 via `schritt` / loaded-image `schritt` / `byteschritt` through `ausgangByte`), each jointly with a successful decode at exact length 7. Nothing re-models memory or execution; `zeugeSpeicher`/`zeugeFlags`/`geladen` are reused.
8. Trust-boundary check: fetch/entry corollaries reuse the accepted correspondence lemmas `fetchDekodiert_entspricht`, `byteschritt_weiter`, `byteschritt_verweigert_ohne_schritt`; no second IR, no mini-machine, no duplicated executor, no safety weakening (no checker/emitter/Spec/Typen/execution file touched; no `cargo`/emission re-measurement owed).
9. The open gap cited by the author is real: `Codec.lean` CUTS and `Byteschritt.lean` CUTS both leave arbitrary-input length soundness open (`roundtrip_len_ok` covers round-trip instances only). No duplication of proved facts.
10. BUILD-EVIDENCE.json (48 entries) is honest: it shows intermediate red probes with fixes, final green `lean-probe`, green full build, standard `gabbro_ziel` axioms (`propext, Classical.choice, Quot.sound`), empty banned-tactic grep, and a 2-file diff stat. No forged or hidden evidence found.

## Defects / repair directions

- None blocking. Two non-material notes, no repair demanded:
  a) The author edited via `sed -i`/`python3` in bash rather than the edit tool (process nit; final content is clean).
  b) The umbrella import needs a one-line rebase onto the current master tail (mechanical; merger-side).
- Known boundary, already disclosed by the author in CUTS and report: exhaustive fail-closed (every non-canonical byte string refuses) is NOT proved; only five new representative `rfl` refusals plus the positive classification (every success IS a canonical 14-form at exact length). This matches `Codec`'s existing refusal-list sense and the task's "no complete x86 coverage" bound. Recorded here as the precise limit of the accepted claim, not as a rejection reason.

## What remains open (not claimed by the candidate, correctly)

Hardware correspondence, complete-x86 coverage, source correspondence, TSO/multi-byte-atomicity bridge, concurrency, cost/ABI/relocation, whole-image/control-flow validation, execute-permission bridge for entry windows, termination. All listed in the file's CUTS block.

## Task-text assessment

Nothing in the lane-435 task text is believed wrong. The task's "unknown/truncated/unsupported bytes fail closed" demand is met in the bounded refusal-list sense the author plainly documents; the report's "weaker than the task text" section states this explicitly, which is the honest handling rule 4 requires.

## Last build result in this clone

- `./lean-probe` on the staged candidate file: 0 errors, standard axioms only (reproduced).
- `./lean-bau` with candidate staged: `Build completed successfully (418 jobs)`.
- After restore (this commit): candidate files absent, tree clean; no new code committed by this lane.

CANDIDATE: 435 e964d8d7bbcdb1da3ec2e017484d38470dfb87e5
VERDICT: ACCEPT
