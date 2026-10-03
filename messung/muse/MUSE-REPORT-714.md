# MUSE-REPORT-714: Compiler ISA and instruction selection architecture review

## What was done

Reviewed upstream PR 2 (pinned `987b286df9d8465714a00bab8226f7b9c7f4afc1`)
with its dependency PR 1 (`5d5a72e5889a3063b417b955fa7824e72c52ef7c`)
from the exact snapshots in `.tmp/UPSTREAM-PRS/pr-{1,2}` (plus the
commits where present in local history). Read the complete ISA file
family (`ISA`, `ISAExecution`, `ISASelect`, `ISARelax`, `CompactForms`,
`IntegerCore`, all six witness files, `Pipeline`, `PipelineImage`,
`PipelineEntry`, `ExpressionLoweringDeep`), the PR-1 optimizer files,
and the Rust `codec`/`opt`/`pipeline`/`elf`/`lower` modules with both
golden files. Compared against accepted master modules
(`ExtendedExecution`, `HardwareExecution`, `IntegerHardwareForms`,
`AddressEncoding`, pilot `Befehl`, `Bild`, `EntryExecution`,
`ShiftLogic`/`Ganzzahl`/`NarrowOps`). Checked every ISA fact class the
task lists against the clone-local Intel SDM snapshot
(`.tmp/HARDWARE-REFERENCES`, edition 325462-093US Sept 2026).

Delivered the owned review document
`dokumente/x86/UPSTREAM-PR-2-ISA-REVIEW.md` (only owned file besides
this report). No source, import, witness, test or semantics file in
this clone was changed (enforced: `git status` shows only the two new
`.md` files; all repair experiments stayed in ignored fixture scratch).

## New definitions/theorems added to the clone

None. This lane is review-only: no Lean or Rust code was added,
changed or deleted here. (`CUTS:` not applicable; no `#print axioms`
added.)

## Key finding (decisive, reproduced)

The pinned PR-2 commit **does not build**. Full `./lean-bau` on the
exact snapshot fails the root `Grammatik` target on two exact-name
collisions (the PR's "full build fails only in
`Parser/ElementTiefProben.lean`" claim is false for the pinned tree):

- `Gabbro.Grammatik.X86.waehle`: `FeatureProfile.lean:72`
  (pre-existing) vs `ISASelect.lean:703` (new).
- `Gabbro.Grammatik.X86.layoutOk`: `TableLayout.lean:80`
  (pre-existing) vs `ISARelax.lean:132` (new).

Per-module builds stay green (colliding pairs never import each
other), which is how it slipped through. A namespace-aware
fully-qualified scan finds no further duplicates. Fixture-only
`sed` renames (`waehle`->`waehleI`, `layoutOk`->`layoutOkI`) give a
GREEN full build (`exit 0`, 0 errors, 476 jobs), proving the repair
necessary and sufficient. An early `CodeAt` suspect was checked and
retracted in the review (sub-namespace, false positive).

Verdict in the review: **REJECT the pinned commit as-is; content
conditionally acceptable after repair.** Blocking items I0 (red
build) through I6 (rebase + `decodeI` vs `decodeExt` unification,
stop-kind discipline, pipeline/select/relax connection-or-scope,
PR-1 friend-reservation sign-off, core-vs-IntHw/SIB relation). No
weakening proposed anywhere.

## Build evidence

- No `./lean-bau` in this clone (no Lean files touched; nothing to
  rebuild here). Independent reproduction in disposable ignored
  fixture `.tmp/fixture-pr2` (exact snapshot + copied wrappers +
  warm clone-local `grammatik/.lake`, same toolchain v4.33.1):
  - Run 1 (exact snapshot): `== exit 1; 3 error line(s)...`,
    root fails on `waehle` collision (log
    `.tmp/fixture-pr2/leanbau.log`).
  - Run 2 (fixture-only renames): `== exit 0; 0 error line(s)...`,
    `Built Grammatik (476 jobs)`, zero `sorryAx` (final green log
    `.tmp/fixture-pr2/leanbau4.log`; intermediate `.tmp/fixture-pr2/leanbau2.log`
    captured the `layoutOk` collision that the namespace-aware scan
    then confirmed as the only remaining duplicate).
- Mechanical audits over exact files: zero `sorry`/`admit`/
  `native_decide`/`^axiom`/`unsafe` in all 27 new Lean files; 470
  `#print axioms` lines in the 10 core files; disjointness and
  consumed-length theorems verified present with arbitrary-input
  generality.
- No fixture cargo run (honest gap, recorded in the review): even
  this clone has no warm `programmlogik/.lake`, and the full suite
  runs `gabbro prove` (cold `lake` = network, forbidden). Rust
  findings are static and labelled; the merger's `./cargo-pruef`
  gate covers execution.

## What remains open

- For the merger/author: I0--I6 in the review, then fresh
  `./lean-bau`, `./cargo-pruef`, emission and key gates on the
  rebased tree.
- `Parser/ElementTiefProben.lean` full-build behaviour was not
  re-measured (fixture root built green without tripping it; the
  PR's `-M4096` note is plausible but not independently confirmed).
- The 137-test x86 cargo claim and the 2-failure macOS note were not
  executed (see above); counts of golden vectors/cases were verified
  statically (4059 codec vectors, ~40 named pipeline cases, 8+2
  golden tests).

## What I believe is wrong in the task setup

- The task's "repair and merge where appropriate" exceeds this
  lane's ownership (only the two `.md` files; source changes
  forbidden). Correctly scoped as review-with-repair-spec; actual
  repair belongs to a follow-up author lane owning the ISA paths.
- The PR body's "first complete, verified compiler path" wording
  overclaims integration: the proved complete path is
  source-optimiser-pilot-image-entry; select/relax/ISA are proved but
  unconnected foundations (no theorem composes them). Flagged as M4,
  not as unsoundness.
