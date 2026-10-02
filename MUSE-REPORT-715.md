# MUSE-REPORT-715: Independent review of candidate 714 (PR-2 ISA architecture review)

## Verdict: ACCEPT

CANDIDATE: 714 7b49fd615f54c3dd31e75364997739ae08d4c3e7
VERDICT: ACCEPT

Candidate `7b49fd615f54c3dd31e75364997739ae08d4c3e7` (author lane 714:
`dokumente/x86/UPSTREAM-PR-2-ISA-REVIEW.md` + `MUSE-REPORT-714.md`, exact
files from `.tmp/review/author-714`, pinned in `.tmp/review/SNAPSHOT.json`)
is accurate. Its decisive finding (pinned PR-2 commit is RED at the root
target on two exact-name collisions), its file inventory, its per-area
verification, its claim-vs-proof table and its MUST-FIX list I0--I6 all
checked out against the exact snapshots in `.tmp/UPSTREAM-PRS/pr-{1,2}`.
ACCEPT means the audit is accurate; it does NOT approve or merge upstream
PR 1 or PR 2. Every concrete open MUST-FIX (I0--I6, M1--M5, F1) is retained
below by reference; none is closed by this review.

## What was done

Verified clone `/home/simon/Dokumente/gabbro-muse/a715`, branch `muse/715`
before starting. Read the full lane task, the 714 owner task, the complete
714 audit (467 lines) and `MUSE-REPORT-714.md` (107 lines), both
`METADATA.json` bodies in full, and both `PATCH.diff` files. Independently
re-checked every load-bearing audit claim against the exact snapshot source
(`.tmp/UPSTREAM-PRS/pr-1`, `.tmp/UPSTREAM-PRS/pr-2`) by static reproduction
(grep-level proof over exact files, never quotes). No source, import,
witness, test or semantics file was changed; `git status` shows only this
report (plus ignored `.tmp` scratch, none created).

## Independent verification results (all confirm the audit)

- **I0 collision, proved by construction.** `def waehle` exists twice in
  namespace `Gabbro.Grammatik.X86`: `FeatureProfile.lean:72`
  `(hw : HwProfil) (b : BereitProfil)` and `ISASelect.lean:703`
  `(S : List Register) (fe : Bool)`. `def layoutOk` exists twice in the
  same namespace: `TableLayout.lean:80` and `ISARelax.lean:132`. The
  snapshot root `Grammatik.lean` imports all four modules (lines
  396/422/476/478), so the root target must fail with "already contains"
  while per-module builds stay green. No live rebuild was needed: same
  fully-qualified name defined twice, both imported by one target, is a
  deterministic root failure. The PR body's own test recipe
  (`lake build` of exactly four witness modules, never the root target)
  explains the miss, and I confirmed the mechanism in full: no new-file
  closure imports `FeatureProfile` at all; only new `PipelineImage.lean:66`
  imports `TableLayout`, and nothing in its closure imports `ISARelax`.
  `ISARelax` imports `ISASelect` (same side, no clash). Per-module green
  with a red root is therefore necessary, not incidental.
- **Inventory exact.** `git rev-list --count`: 7 commits PR-1, 55 commits
  PR-2, 170 commits behind (`26c58bd4..011ff474`). PR-2 `PATCH.diff`: 27
  file diffs, **zero** deletion lines -- purely additive as claimed; only
  `Grammatik.lean` (+18 imports) and `x86/mod.rs` (+12 mod lines) touched.
  All twelve line counts I sampled match the audit to the line
  (ISA 1744, ISASelect 1293, ISARelax 1211, CompactForms 1407,
  IntegerCore 1142, Pipeline 2478, PipelineImage 2167, PipelineEntry 493,
  ISAWitnesses 690, IntegerCoreWitnesses 550, PipelineWitnesses 936,
  PipelineImageWitnesses 1984).
- **Hygiene exact.** Word-boundary sweep for `sorry|admit|native_decide|
  unsafe|^axiom` over all 18 new Lean files: zero hits (naive matches were
  only the English word "admitted"). `CUTS` blocks present in all 18 files.
  `#print axioms` lines across the 10 core files total exactly 470.
- **Disjointness generality as claimed.** `theorem familien_disjunkt
  (F G : Fam) (bs : List Byte)` (`ISA.lean:1134`) quantifies over arbitrary
  byte strings; `decodeI_eindeutig`, `decodeRex_sig`, `grenze_rexw_movzx`
  and all cited boundary probes exist at the named locations.
- **I2/I1 context real.** The PR-2 snapshot contains no `decodeExt`, no
  `ExtendedExecution`/`HardwareExecution`/`IntegerHardwareForms`/
  `AddressEncoding`; current master has all four plus `def decodeExt`
  (`ExtendedExecution.lean:64`). Two canonical unified integer entry
  points after merge is a genuine architectural conflict, not wording.
- **I3 context self-admitted in-file.** `ausgangVon none = verweigert`
  is stated as a merge of all refusals at `ISAExecution.lean:565` while
  `stepIE_halt_nur_muldiv` (`ISA.lean:183`) keeps `#DE` distinct -- the
  audit's stop-kind finding points at a real, CUTS-admitted collapse.
- **PR-1 reservation claim true.** Snapshot `AGENTS.md:147` still reserves
  both optimizer paths, and PR-1 history contains "Re-applies the first
  friend delivery onto master's rewritten specification". PR-1 files are
  byte-identical between the pr-1 and pr-2 snapshots (`diff -q` clean).
- **Counts honest.** `codec_golden.rs` provenance header states 4059
  vectors itself; 2 codec tests + 8 pipeline tests present; 45
  `pd_fall|pw_fall|q_fall` call sites vs "~40 named cases" and the PR
  body's "42 golden cases" -- consistent within naming tolerance.
  `seitentreu` is the Rust `elf.rs:171` page-faithfulness check with a
  `pilot_images_are_not_page_faithful` test -- the audit cites it
  correctly. Reference provenance artifacts exist clone-locally
  (`intel-instruction-reference.{pdf,txt}`, 26664929 bytes as registered).
- **Audit honesty markers genuine.** The `CodeAt` false positive is
  retracted inside the audit with the namespace reason
  (`Pipeline.CodeAt` vs bare `CodeAt`); the unexecuted cargo run and the
  unmeasured `ElementTiefProben` note are recorded as open gaps, not
  papered over.

## New definitions/theorems added to the clone

None. Review-only lane: no Lean or Rust code added, changed or deleted.

## Last `./lean-bau` result line

No `./lean-bau` run in this clone: nothing was built because nothing was
touched (review-only, same standing as the author lane). The I0 proof above
is static and dispositive; a 476-job fixture rebuild would only re-emit one
already-proven error string. No `./cargo-pruef` run either (no Rust touched;
the author's honestly-recorded cargo gap passes to the merger gate).

## What remains open (for merger/author, unchanged from the audit)

I0 (rename new `waehle`/`layoutOk`) through I6 (Core-vs-IntHw subsumption),
then rebase per I1, dispatcher unification per I2, stop-kind discipline per
I3, path connection-or-scope per I4, friend-owner sign-off per I5, with fresh
`./lean-bau`, `./cargo-pruef`, emission and key gates on the rebased tree.

## Minor nits found (not verdict-affecting, offered to the author)

- Audit section 1 says "six witness files" but lists eight names.
- `ISASelect.lean:52` imports `CompactFormsWitnesses` (a witness file as a
  real build dependency of a core module) -- unusual layering, no
  correctness effect, unflagged by the audit; worth one line in a rebase.

## What I believe is wrong in the task setup

Nothing material. Ownership (only this report) and the report-only ACCEPT /
REPAIR verdict shape were enforceable as written. The lane-714 "repair and
merge where appropriate" overreach the author already flagged is correctly
out of scope here as well; I0--I6 stay repair specs for a follow-up author
lane owning the ISA paths.
