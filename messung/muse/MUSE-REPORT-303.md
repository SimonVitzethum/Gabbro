# MUSE-REPORT-303 — Independent review of candidate 287

Lane 303 (`muse/303`, model opencode-go/muse-spark-1.3-contributor).
Scope: review ONLY the exact committed snapshot in `.tmp/review/`
pinned by `SNAPSHOT.json`. No code or central file edits.

## 1. Candidate identity

- `SNAPSHOT.json` pins: author 287, head
  `b9f000da3548b3c90fb474e5f31e7559955a78f3`, base
  `dd02d9120be5540dc3773affcc4c647c4bae940b`, files
  `["MUSE-REPORT-287.md"]`, clean true.
- `BUILD-EVIDENCE.json` (252 entries) last commit entry shows the same
  head hash, same base, `git status` clean after commit. Pin consistent.
- `PATCH.diff` shows exactly one committed file: new
  `MUSE-REPORT-287.md` (224 lines). No `grammatik/` source, no
  `Grammatik.lean` edit, no IR import in the committed diff.
- Reviewer clone check: `grammatik/Grammatik/X86/` contains no
  `IR.lean`; `Grammatik.lean` has no `Grammatik.X86.IR` import
  (grep: no match). Committed scope matches the authorised scope
  (report only, no IR import or interpreter lands).

## 2. Authorised scope applied

Per lane task LATEST AUTHORISED SCOPE, accepted architecture 594/606
supersedes the persistent IR: author 287 must preserve old drafts under
ignored `.tmp/IR287-PRESERVED/` and deliver ONLY an honest committed
`MUSE-REPORT-287.md`. ACCEPT may cover the honest preservation/handoff
report only, never the unaccepted draft. This review applies exactly
that standard; no original IR construction is required.

## 3. Report honesty checks (against snapshot + build evidence)

- Supersession stated up front (§0): no source file delivered, IR
  removed from `grammatik/`, umbrella import reverted, final tree is
  master plus the report. Matches `PATCH.diff` (report-only diff).
- No overclaim: §0 states no compiler built, no bytes validated, no
  full-language claim. §3 states `#print axioms` was never run, so no
  axiom claim is made. §5 lists defects explicitly: `lowerB_mono` red
  with 6 parse-level errors, no statement-level correspondence
  (`scorrW`/`bcorrW` designed only), `ecorrW` expressions-only, stale
  `CUTS` comment, `Bis287`/`Tmp287` superseded scratch. §8 lists L1–L4
  work OPEN. No source/target/cost/TSO/hardware theorem is claimed.
- Build evidence: `BUILD-EVIDENCE.json` entry 81 `./lean-bau` exits 0
  with 0 error lines; entry 247 shows `368 jobs` replayed on the
  restored tree. The report's claimed last-build line (`Build
  completed successfully (368 jobs)`) is consistent with that evidence.
  Long intermediate `lean-probe` history (38 → 0 errors on `ecorrW`
  + witness, then red on appended `lowerB_mono`) is consistent with the
  reported verification history; I did not re-run a full build for prose
  per the task instruction.
- Forbidden tokens in the committed candidate: the only committed file
  is Markdown; occurrences of `sorry`/`admit`/`axiom`/`native_decide`
  in it are prose (the "no file contains …" sentence), not Lean code.
  No Lean file is committed, so proof/witness/axiom gates on committed
  code are vacuous. No name-specific rule, no inferred ensures, no
  weakening: nothing lands that could weaken a guarantee.
- Model identity: report states
  `opencode-go/muse-spark-1.3-contributor`, as required.

## 4. Not verified (explicitly out of acceptance scope)

- Preserved ignored-file details (`.tmp/IR287-PRESERVED/IR.lean` 2689
  lines, md5 `892abbf1962919b74f0625d647a4bbb0`, 6-error `lowerB_mono`
  state; `Bis287`/`Tmp287` sizes/md5s; grep-zero claim over the
  preserved file) cannot be verified from the committed snapshot
  because ignored `.tmp/` paths are not committed by design. This is
  handoff information, not acceptance evidence, and per the authorised
  scope ACCEPT covers the honest report only, never the draft. No
  defect is inferred from these unverifiable details; the report labels
  the draft red/incomplete where it matters (§5).
- The unaccepted draft's theorems (`ecorrW`, `ecorrW_zeuge`,
  `lowerE_mono`, unfinished `lowerB_mono`, witness scene `XD/XV/Xρ/Xσ`)
  are described, not landed. I make no claim about their truth; they
  are not part of the candidate.

## 5. Findings

No material defect in the committed candidate. The bounded delivered
claim — "IR superseded, report only, tree is master plus report, all
further work OPEN" — is true, matches the pinned diff and the build
evidence, and respects the no-IR-lands constraint.

## 6. Verdict

CANDIDATE: 287 b9f000da3548b3c90fb474e5f31e7559955a78f3
VERDICT: ACCEPT
