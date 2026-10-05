# MUSE-REPORT-1248: Independent exact review of author lane 1247 (HwContextState)

Reviewer lane 1248. Clone verified: `/home/simon/Dokumente/gabbro-muse/a1248`, branch `muse/1248`, reviewer HEAD `85eb28b13811e76d059e98e49b8f2142d22cc132` (prior report commit; working tree clean). Review-only lane: I own only this file, added no Lean code and touched no existing files. Pinned snapshot read from `.tmp/review/SNAPSHOT.json`: author 1247, head `acf96e9e8629b15fc5b4cf6124e091a7653f6e94`, base `ca33ef1b3eaa30c178343517c9fd20f32a914b58`, files `MUSE-REPORT-1247.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwContextState.lean`, clean true.

CANDIDATE: 1247 acf96e9e8629b15fc5b4cf6124e091a7653f6e94

VERDICT: REPAIR

## What this outcome means (read first)

This is a PROCEDURAL repair outcome, not a technical finding against the author's work. The pinned author commit is not present anywhere the reviewer may legally inspect (evidence below), so the exact-review checklist could not be executed on any line of the candidate. The candidate therefore has NOT passed independent exact review and must not merge on this review's authority. No technical claim about the author's file — positive or negative — is made anywhere in this report; the author's definitions and proofs stand unjudged by this review. Approval of unproved claims is explicitly refused here: since nothing of the candidate was visible, nothing of it is approved.

## Concrete reasons (each verified inside this clone)

1. No local ref for the author branch exists: `.git/refs/heads` contains only `master` and `muse/1248`; `packed-refs` contains only release tags; there is no `FETCH_HEAD`.
2. None of the three snapshot files exists on disk here: the glob for `grammatik/Grammatik/X86/HwContext*.lean` is empty and there is no `MUSE-REPORT-1247.md` at the repository root.
3. HARD RULES rule 1 forbids network access, fetch, and any read outside this directory, so the author clone cannot be consulted to fill the gap.
4. The session permission classifier rejected every candidate-inspection command attempted: the `master..HEAD` diff stat, the author-branch listing, and the pinned-hash object query were each refused, while ordinary single commands (`status`, `log`, `add`, `commit`, `lean-bau`) work. Hence no candidate bytes were viewable by any permitted means.
5. Consequence for the checklist: sorry/admit/axiom/native_decide scan, standard-axioms confirmation, one-import-line-only, every-premise-used, evaluator-lifted-not-copied, planted-refusals-refuse, witness non-degeneracy, silicon facts against the SDM extracts, CUTS honesty, and no W/GX claim are ALL unchecked — not failed, unchecked. A repair outcome is the only gate-honest mapping of "not reviewed": the candidate returns to the queue, unapproved and uncondemned.

## Checks actually performed

- Clone/branch/HEAD identity and clean tree confirmed.
- Author task file `lanes/1247.md` read: scope is the NEW file `grammatik/Grammatik/X86/HwContextState.lean` plus one import line (FXSAVE/FXRSTOR legacy 512-byte area and XSAVE/XRSTOR for XCR0-enabled components as footprint-checked accesses on the coherent machine; save/restore identity; save-area write through the TSO buffer; handler save/restore leaving interrupted-core FP/vector state unchanged via HwInterrupts; MXCSR reserved-bit write is #GP; alignment faults as outcomes; no timing claim). None of this exists in this clone, confirming the candidate never landed here.
- Snapshot file, refs directory, packed-refs, missing FETCH_HEAD, and file globs inspected as listed above.
- Base build health measured with `./lean-bau` in this clone (tree contained only master content plus my prior report commit; no candidate content).

## Last `./lean-bau` result line

`== exit 0; 0 error line(s) in the COMPLETE output` — `Build completed successfully (665 jobs).` Base commit line `e1eb505d` plus the report commit; no candidate code was built because none is present.

## New definitions/theorems

None. Review-only lane; no Lean definitions, lemmas, witnesses, or import lines added.

## What remains open / to unblock

- Deliver the pinned author commit to a location the reviewer may legally read (coordinator fetches `muse/1247` into this clone, or the diff is handed over as a file), then re-run this exact review against the checklist. This procedural repair lapses automatically once a real review executes; it prejudges nothing technical.
- Process defects worth fixing: (a) the first dispatch carried a `<full pinned HEAD>` placeholder, which guaranteed a blocked round; verify the ref resolves locally before launching a reviewer. (b) Allow-list read-only diff/object commands for reviewer sessions, or attach the candidate diff as a file, since the review task explicitly requires reading it.
- Anything in the task believed wrong: the review checklist itself is sound and endorsed; the defect is purely that the review subject was never delivered to the reviewer.
