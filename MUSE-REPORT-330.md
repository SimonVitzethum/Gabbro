# MUSE-REPORT-330: Actual isolated merge of independently reviewed candidate 327

Scope: actual merge-owner integration only. No design edits, no source/Lean/Rust/
emitter/ledger/central-doc repairs. Owned paths only: `DIRECT-COMPILER-DESIGN.md`
(transferred approved bytes), `messung/muse/MUSE-REPORT-327.md` (moved supplied
author report), and this report `MUSE-REPORT-330.md`.

## Identity (hashes)

- Base (integration target, own HEAD at start): `6a0b028af57bd2e192030c647ba96de9ec837995`
  (equals CANDIDATE.json `integration_base`).
- Author head (approved): `03ab77b03e2f8de9b26f02ec5eb13a177fbcacdc`
  (equals CANDIDATE.json `author_head`; bundle ref `refs/heads/muse/327` matches).
- Reviewer head (reported, bundle not supplied): `dfda84e8b5603413e38e4c588c99e7ebad73098a`
  per CANDIDATE.json; review text in `.tmp/approved/REVIEW-328.md`.
- Approved design blob (`author_blob`): `4a7e189afd6a8bf2b4f6e82407451a8098345674`.
- Resulting design blob after merge: `4a7e189afd6a8bf2b4f6e82407451a8098345674`
  (`git hash-object DIRECT-COMPILER-DESIGN.md`, identical).
- Actual merge commit: `2abfef7d` with parents `6a0b028a` + `03ab77b0` (both retained).

## Verdict gate

- CANDIDATE.json `review_verdict`: `ACCEPT`.
- REVIEW-328.md: `VERDICT: ACCEPT` (line 119, unique). The two other `ACCEPT`
  mentions are historical (review 326 reference, scope sentence). The two
  `REJECT|REPAIR|CHANGES|REQUEST` grep hits are benign prose ("no repair owed"
  nit header; "no Lean changes" build note), not verdicts. No REJECT, no REPAIR
  requested. Gate passed.

## Actual commands and outcomes

1. `pwd` / `git rev-parse --show-toplevel` / `git branch --show-current`:
   `/home/simon/Dokumente/gabbro-muse/a330`, branch `muse/330`. Match, proceeded.
2. `git bundle verify .tmp/approved/327.bundle`: `is okay`, contains
   `03ab77b0 refs/heads/muse/327`, complete history.
3. `git fetch .tmp/approved/327.bundle 'muse/327:integration/327'` (LOCAL file
   only): new branch `integration/327`, 1 unique commit.
4. `git rev-parse '03ab77b0:DIRECT-COMPILER-DESIGN.md'` =
   `4a7e189a...` (matches `author_blob`); `git hash-object .tmp/approved/AUTHOR-327.md`
   = same blob (supplied approved file is byte-identical to the committed design).
5. `git rev-list HEAD..integration/327`: exactly 1 commit (`03ab77b0`);
   its own stat: `DIRECT-COMPILER-DESIGN.md` + `MUSE-REPORT-327.md` only
   (+178/-7). Merge-base with HEAD: `1ab5471a`; HEAD-side changes since
   merge-base (12 files: AGENTS.md, DIRECT-COMPILER.md, Grammatik.lean,
   Byteschritt.lean, lanes/329-334, MUSE-REPORT-319/320) are DISJOINT from the
   candidate's 2 files; HEAD side does not touch the design. No silent revert risk.
6. `git merge --no-ff --no-commit integration/327`: clean, `Automatic merge went
   well`. Staged exactly `M DIRECT-COMPILER-DESIGN.md`, `A MUSE-REPORT-327.md`.
   No conflicts, no semantic resolution performed (none needed).
7. `git mv MUSE-REPORT-327.md messung/muse/MUSE-REPORT-327.md`: staged exactly
   the 2 owned paths (+178/-7 over 2 files).
8. `git hash-object DIRECT-COMPILER-DESIGN.md` after merge = approved blob, exact.
9. `git diff --check`: clean (exit 0).
10. Filenames English (`DIRECT-COMPILER-DESIGN.md`, `messung/muse/MUSE-REPORT-327.md`).
11. Markdown links: 31 relative `](...)` links in merged design, 0 bad
    (matches review 328's 31/31; external Intel/AMD/LLVM refs excluded).
12. German-identifier grep over design: 0 umlaut hits (the one German string is
    the quoted user steering in plain ASCII, per owner task allowance).
13. Staged-name source scan: no `.lean/.rs/.c/.h/.py/.sh` files staged (docs only).
14. `./commit.sh`: committed merge `2abfef7d`, both parents verified
    (`HEAD^1=6a0b028a`, `HEAD^2=03ab77b0`).

## What was integrated

- `DIRECT-COMPILER-DESIGN.md` 698 -> 761 lines: safety-first priority revision
  (user steering qualitative "last 10%", no numeric 90% claim, FULL proved
  validation + FULL safety for EVERY selected profile and EVERY source construct,
  actual parameters/results, no inferred `ensures`, no refusal-to-warning,
  bounded `schritt`/codec helpers PROVED, hardware/source correspondence OPEN).
- `messung/muse/MUSE-REPORT-327.md` (108 lines): author evidence for the above.

## New definitions/theorems

None. Docs-only merge; no Lean file added or changed.

## Last build result

`./lean-bau` NOT run: no Lean/Rust/emitter bytes changed (staged set is 2
markdown files only), so no gratuitous full build per task. Reused source-check
limitation: this lane did NOT re-verify Lean green gates or the §2 pilot table
against `grammatik/Grammatik/X86/` sources; root must inspect source ancestry
and green gates before publication. Review 328's tree checks (14 `Befehl`
constructors, 16 registers, 16 `Bedingung` codes, `Flags.af : Option Bool`,
`roundtrip`/`roundtrip_len_ok` presence) are cited, not re-executed here.

## Open / remaining cuts

- Source-to-binary guarantee OPEN (no validator, decoder, refinement, or cost
  result closed by this merge; CUTS of the design unchanged).
- Independent lane 333 checks the exact merged candidate before root integrates
  and publishes; root publication step pending.
- `integration/327` branch and `.tmp/approved/` bundle retained in this clone
  until root collects the report (per task: keep work until report committed;
  cleanup is root's merge-ward decision, not this lane's).

## Task correctness notes

- `.tmp/approved/AUTHOR-327.md` (761 lines) holds the approved DESIGN bytes,
  not a report; the author report travels inside the bundle commit as
  `MUSE-REPORT-327.md` and was moved from the merged tree. Naming is
  confusing but harmless once hashed: both hash to the approved blob / the
  branch blob respectively.
- CANDIDATE.json `integration_base` equals this lane's starting HEAD, while the
  branch fork point is one step older (`1ab5471a`); the merge is still exact
  because the change sets are disjoint. No extra premise or weakening involved.
- Nothing in the task asked for a weaker claim; none made.

CUTS: no theorem proved; no decoder/validator/refinement/cost result; no runtime
or compiler speed measured. ACCEPT-merge covers only this bounded plan revision,
not a completed compiler or validator.
