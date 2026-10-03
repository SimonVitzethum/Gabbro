# MUSE-REPORT-1033: Exact review of author 883 (loop alignment rule)

CANDIDATE: 883 a501373ef0ea0a44ddede580408e9c70cf64d038
VERDICT: ACCEPT (bounded; see scope below)

## What was reviewed

Exact pinned snapshot from `.tmp/review/SNAPSHOT.json` (base
b040b155159f47629542b0083e2f0a8a607f2b4c, which matches this clone's HEAD):
three files, `PATCH.diff` 412 lines.

- `grammatik/Grammatik/X86/OptLayoutAlign.lean` (new, 323 lines; read in full).
- `grammatik/Grammatik.lean` (one appended line: `import Grammatik.X86.OptLayoutAlign`).
- `MUSE-REPORT-883.md` (claims checked against the file).
- `BUILD-EVIDENCE.json` (probe/build/commit trail, including two red
  intermediate probes that were repaired before the final green commit).
- Owner task `OWNER-TASK.md` (lane 883).

Reference checked: `.tmp/HARDWARE-REFERENCES/REFERENCES.json` (Intel SDM
325462-093US Sept 2026, Intel-profile only, no AMD snapshot, no silicon
claims permitted).

## Architecture review (not just Lean green)

1. Byte forms / operands / flags: the file models NO machine bytes, no NOP
   padding encodings, no REX/register/width/flag semantics. This is sound
   because it claims none: `layoutPad` is the identity on executed source
   syntax, so there is no defined hardware effect being zeroed, ignored, or
   deterministically invented. The Intel NOP-neutrality fact is therefore
   not needed for this lemma and is correctly NOT cited as proved.
2. Canonical execution interaction: genuine reuse, not a mini-model --
   `Semantik.execBlock`, `Syntax.Block`, `ReferenzB` (`refD`, `vertragVon`,
   `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`, `keinRuf`,
   `RufMaschineF`). The preservation conjunct (`execBlock` equality) is
   proved by `rfl` from the identity definition: trivial but not assumed,
   and the formal statement claims exactly outcome equality, nothing wider.
   The broader reading (IEEE/faults/contracts/logs/shared/budget) in the
   header comment follows from both sides sharing one `V`, `O`, `passes`,
   `R` and equal outcomes; acceptable as commentary, not as extra theorem.
3. Side-condition grounding: `kopfOk`/`lastOk`/`gemessen` are validator-held
   Bools with no link from the certificate to the body being a loop head or
   vector load. This matches the task's explicit instruction
   ("validator-decided side conditions", generic rule over arbitrary values,
   source fragment until the IR lands) and the sibling precedent, so it is
   recorded as the known bounded shape, not a defect. The binding premise
   `hbind` ties the two records' class/pad fields together.
4. Premise use: `hz` via `alignZulassen_pad`, `hok` via
   `alignBeleg_adresse`/`alignBeleg_ausgerichtet`, `hbind` destructured by
   `obtain`. No `intro _` / `have _ :=` discards. (Nit, not verdict-relevant:
   after `obtain`, `hba`/`hbp` are not needed to close the goal -- `omega`
   closes from `hcert` alone -- and `alignVerweigert_unvermesssen` carries a
   triple-s typo, used consistently including the probe name.)
5. Witness: `OptLayoutAlign_verbindung_zeuge` jointly instantiates every
   premise (admitted cert by `decide`, accepted head record by `decide`,
   `hbind` by `rfl`, outcome conjuncts from the main theorem) on
   non-degenerate `refD` (`einzahlen` writes via `refEin_schreibt`) beside
   reached F-run `MB` with a memory change (`refB_erreicht`,
   `refB_schreibt`). Body is `Block.nil`; non-degeneracy comes from `refD`
   + `MB` as rule 13 requires. Satisfies the ZEUGE line.
6. Negative mutations, both polarities: admission accept + unmeasured /
   pad-overflow / class-8 refusals; certificate accept
   (4096,5,16,0,4096) + three refusals (pad 16, head 4100 unpadded,
   pad-4-to-4100 misaligned). Refusal is fallback-to-another-translation,
   never a warning; no `ensures` derived (word absent from file); no
   faulting form speculated above a guard; no timing promise (CUTS defers
   per FLOAT-ZEIT 8.2, matching the 7A "no fixed timing promise" row).
7. CUTS precision: excludes relaxation-round convergence (DESIGN 2B),
   level-(c) machine-work bound (same reading as lane 860), timing,
   silicon/TSO-GX/ABI correspondence (stops at `Nat` head arithmetic), and
   checker changes. Matches the file content; no fake closure.
8. Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the full
   323 lines; no `Prop`-typed premise; no new diagnostic/gift/example/CLI
   numbers; no MARKE_EMIT touch; friend-reserved optimiser files untouched;
   import appended at end of `Grammatik.lean` only.

## Evidence basis and honest limitation

- Pinned BUILD-EVIDENCE: final `./lean-probe` 0 errors, `./lean-bau`
  "Build completed successfully (511 jobs)", `#print axioms` standard for
  both mains (`[propext, Classical.choice, Quot.sound]`), helpers
  `[propext]` or none.
- Live re-verification in this clone was NOT possible: `bash` tool calls for
  inspection/build/commit were rejected by the permission gate (two
  rejections on read-only `ls`/`wc`/`git -C` invocations; one earlier
  `git rev-parse` succeeded and confirmed clone
  `/home/simon/Dokumente/gabbro-muse/a1033`, branch `muse/1033`, HEAD
  `b040b155...` = snapshot base). The verdict therefore rests on the
  pinned evidence plus complete read-only inspection of the exact snapshot.
  No network, push, or other-clone access was used or needed.
- Commit of this report via `./commit.sh` needs the blocked `bash` tool;
  attempted if available, otherwise this file is left written but
  uncommitted -- see status line below.

## Bounded acceptance scope

ACCEPT covers: the admission Bool with its three refusal theorems + four
probes; the recomputed `alignOk` certificate with accept/address/alignment/
pad theorems + concrete accept/refuse witnesses; the connection theorem as
the layout-only identity plus recomputed head facts; the joint witness; the
CUTS as written. It does NOT cover any machine-byte, timing, TSO, ABI, or
relaxation-convergence claim -- none is made.

Status: report written to `MUSE-REPORT-1033.md`; commit pending on `bash`
availability (permission gate rejected build/shell calls during this turn).
