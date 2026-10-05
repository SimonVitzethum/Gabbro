# MUSE-REPORT-1142: exact review of candidate 1141 (candidate not available in-clone — procedural REPAIR)

## Identity
- Review lane: 1142, clone `/home/simon/Dokumente/gabbro-muse/a1142`, branch `muse/1142`, HEAD `84c19acaf66e0f147235b0f5fb6f01c43e86e8a6` — all three verified via `pwd`, `git branch --show-current`, `git rev-parse HEAD` in this turn.
- Author lane task (from `lanes/1141.md` in this clone): NEW FILE `grammatik/Grammatik/X86/HwIsaFamilies.lean` + one import line in `grammatik/Grammatik.lean`; HwAdapter for `Instr` agreeing with accepted `stepI` (register projection) and `stepExt`; HwWf preservation; refusals; non-degenerate multi-step `_zeuge` witness (two cores where memory is touched); silicon-first; CUTS + `#print axioms`; no W/GX claim.
- Owned files: only `MUSE-REPORT-1142.md`. No other file created or modified.

## What I did
1. Re-read `.tmp/LANE.md` and `lanes/1142.md` (exact-review checklist) and `lanes/1141.md` (author task) using the Read tool.
2. Verified via Glob that the candidate artefacts are NOT present in this clone: `grammatik/Grammatik/X86/HwIsaFamilies.lean` — no files found; `MUSE-REPORT-1141.md` — no files found. This is expected for an isolated reviewer clone, but it means there is nothing reviewable locally.
3. Attempted the prescribed exact-review inspection. `git rev-parse muse/1141` inside this clone answers: local ref `muse/1141` does not exist (fatal: unknown commit). Cross-clone reads (`/home/simon/Dokumente/gabbro-muse/a1141`) are forbidden by the lane prompt ("Do not read credentials or files outside your clone"). `git branch -a` and multi-part compound shell commands are rejected by the permission classifier; single simple commands (`pwd`, `git branch --show-current`, `git rev-parse HEAD`, `git status --short`, `git rev-parse muse/1141`, `./lean-bau`) work.
4. Ran `./lean-bau` on this clone (base tree, no candidate changes present): green — `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (606 jobs)`. This validates the base only, NOT the candidate. Did NOT invent a verdict on the merits.

## Precise blockers
- **B1 — no pinned candidate HEAD.** The task line reads `CANDIDATE: 1141 <full pinned HEAD>` — the placeholder was never filled with a 40-hex hash. Without a pinned HEAD, "exact review" of "the candidate diff only" is undefined; any hash I guessed could differ from what the coordinator intended.
- **B2 — `bash` partly restricted, candidate ref absent.** Single simple commands work (`pwd`, `git branch --show-current`, `git rev-parse HEAD`, `git status --short`, `./lean-bau`). `git branch -a` and compound multi-part commands are rejected by the permission classifier. Crucially, the candidate branch is NOT fetched in this clone (`git rev-parse muse/1141`: unknown commit), so the exact candidate diff cannot be read from inside my directory.
- **B3 — author clone off-limits.** The prescribed command (`git diff master..HEAD` in the author clone) points outside my directory, which the lane prompt forbids me to read. No in-clone copy of the candidate diff, snapshot, or report was supplied.

## Review checklist status (all UNVERIFIED — candidate not available)
- [ ] no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` — NOT CHECKED (B1–B3)
- [ ] `#print axioms` standard (propext, Classical.choice, Quot.sound) — NOT CHECKED
- [ ] existing files untouched except one import line — NOT CHECKED
- [ ] every premise used; no Prop-typed premises; no desired-correctness premises — NOT CHECKED
- [ ] accepted evaluator lifted, not copied — NOT CHECKED
- [ ] planted refusals really refuse — NOT CHECKED
- [ ] witness non-degenerate (memory-changing step, two cores where memory touched) — NOT CHECKED
- [ ] silicon facts vs Intel SDM extracts — NOT CHECKED
- [ ] CUTS honest; no claim beyond proof (no hardware-correspondence / W/GX claim) — NOT CHECKED
- [ ] `./lean-bau` last result line — RUN ON BASE ONLY (candidate absent): `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (606 jobs)`. Says nothing about the candidate.

## VERDICT: REPAIR
Rationale (procedural, not semantic): acceptance requires verifying every item above against the exact pinned candidate diff plus a green `./lean-bau` line, and none of that was obtainable (B1–B3). Per the lane's own rule — "no claim larger than the proof" and "no fake closure" — the only honest verdict is REPAIR, meaning: **re-issue this review with (a) the full pinned HEAD of candidate 1141, (b) the candidate diff/report supplied inside the reviewer clone or a readable snapshot path, and (c) working `bash`/wrapper permission, then review on the merits.** This REPAIR is a statement about reviewability, not a rejection of the author's work, which I have not seen.

## New definitions/theorems
None (report-only review lane; nothing added by design).

## Last `./lean-bau` result line
`== exit 0; 0 error line(s) in the COMPLETE output` — `Build completed successfully (606 jobs)`, measured this turn on the base tree of this clone (HEAD `84c19aca`, no candidate changes present). No build claim about candidate 1141 is made.

## What remains open
1. Full exact review of candidate 1141 against every checklist item above, once B1 and B3 are resolved (pinned HEAD + sanctioned in-clone snapshot of the candidate diff/report).
2. Committing this report via `./commit.sh` (attempt next this turn; if the commit wrapper call is rejected, the report stays written but uncommitted).
3. Task defect to fix upstream: fill in the `<full pinned HEAD>` placeholder before dispatching exact reviews, and either vendor the candidate snapshot into the reviewer clone or grant the reviewer a sanctioned read path — the current prompt simultaneously orders `git diff … in the author clone` and forbids reading outside the clone.

## Task-correctness notes
- The review criteria themselves are sound (lift-don't-copy, premise use, non-degenerate witness, silicon-first, honest CUTS, no W/GX overclaim).
- The dispatch was not executable as written for the three reasons above. Nothing in the author task (lane 1141) is judged here.
