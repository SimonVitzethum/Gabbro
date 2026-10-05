# MUSE-REPORT-1308: exact review of candidate 1307 (FP store drain = write32)

Review lane. Clone `/home/simon/Dokumente/gabbro-muse/a1308`, branch `muse/1308`
(read-only for this review; no author-clone or pinned-hash git access used).
CANDIDATE: lane 1307, head `c1d8ca610e923288ee5cced7d5a6fbcec62746bf`
(base `234f2728a718157cba0e1f9e0ef300874b34ea6a`), files per
`.tmp/review/SNAPSHOT.json` (clean): `MUSE-REPORT-1307.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwFpStoreDrain.lean`.

## What was done

Independent exact review of the delivered files against the owner task
(lane 1307: 4-byte FP store drain equals accepted `write32` for STMXCSR and
MOVSS-store, owner forwarding, foreign view, crossed-group tearing refusal):

- `PATCH.diff` structure: exactly 3 file diffs; `Grammatik.lean` hunk is a
  single added line `import Grammatik.X86.HwFpStoreDrain`; no other existing
  file touched.
- Forbidden-token scan (word-boundary `sorry|admit|native_decide|unsafe`,
  `^axiom`): no matches. (`admit`/`axiom` substrings appear only inside the
  English words "admits" and the required `#print axioms` lines.)
- No `Prop`-typed premises; no `intro _` / `have _ :=` discards.
- No redefinition of accepted vocabulary: no `def` of `fpCtrlAusgabe32`,
  `fpEintraege32`, `FpGruppe32`, `FpFremdFrei32`, `fpFuss32`, `write32`,
  `read32`, `flushKern`, `issueByte`, `loadByte`, `DrainSpur`,
  `DrainSchritt`, `fpDispMxcsrAusgabe`, `fpDispMovssAusgabe`,
  `mxcsrSpeicherWort`, `xmmTief32`. The adapter and all group/forwarding
  facts lift the accepted evaluators (`fpCtrlAusgabe32`,
  `fpDispSt_gruppe`, `fpCtrlAusgabe32_gruppe`, `fpCtrlWeiterleitung32`,
  `fpGruppe32_teilwort`, `fpGruppe32_fremd`).
- `./lean-probe` on the delivered candidate file (run from this clone root;
  see deviation note below): `== 0 error(s) in the COMPLETE output; exit 0`.
  Only linter style warnings (unused binder names in induction `leer`
  branches, lines 266-268/381-382 — branch-local shadows; each name is used
  in the sibling `schritt` branch, so no theorem premise is discarded).
- `#print axioms` for all 38 theorems: every result within
  `[propext, Quot.sound]` (subset of the standard goal set); pure
  `decide`/`rfl` facts report no axioms.
- `./lean-bau` in this clone (candidate not in this tree, as required for a
  review lane): `== exit 0; 0 error line(s)`, `Build completed successfully
  (677 jobs)`. Author's delivered `BUILD-EVIDENCE.json` final entry agrees:
  exit 0, 677 jobs, same axiom lines for the candidate file.
- Witness `fp32StoreDrain_zeuge` is non-degenerate and joint: core 0
  buffers `3.0f32` (`0x40400000`, 4 entries, memory unchanged), forwards
  `0x40` to itself while core 1 reads `0`; push-to-drain continuity
  (`fp32Wit_push_gleich_start`); four-drain installs the accepted `write32`
  footprint with `read32` read-back (`fp32Wit_feuer`); core 1 observes the
  new byte (`fp32Wit_fremd_neu`); one byte observably changes
  (`fp32Wit_aendert`, `0` vs `0x40` by `decide`); drain is a reached TSO run
  (`TSOErreichbar` via `drain_spur_erreichbar`); beside it concrete partial
  (2-of-4), crossed-group (4-byte store at 8198 vs in-flight 8-byte group at
  8192, shared byte `8198+0 = 8192+6`), guard, dark and empty-drain refusals
  (witness-side ones are closed `decide` evaluations, green in the probe).
- Silicon: no invented encodings; STMXCSR/MOVSS issue halves are lane 1211's
  accepted evaluators; the only literal (`0x40400000`) is data whose byte
  order is verified by the proved read-back. CUTS explicitly claims
  self-consistency only, notes the byte drain is alignment-free (crossed
  refusal is structural overlap, not an alignment gate), and disclaims
  hardware correspondence, per-access W/GX simulation, whole-word atomicity
  beyond the guarded drains, and source/loader/entry/budget links. No claim
  exceeds the proof.

Deviation note: the task's "copy the candidate file into your own clone
first" step was not executable here (shell file-copy commands are
permission-blocked in this session), so the probe ran against the delivered
file at its `.tmp/review/author-1307/...` path from this clone root with this
clone's toolchain and dependency tree. Content checked is byte-identical to
the candidate (delivered copy); dependency modules resolve to this clone's
accepted tree. No repo file was modified by this review.

Advisory (not a finding): the two linter warnings above could be silenced by
naming the `leer`-branch binder `_hstoer`, matching the file's existing
`_hff`/`_hles` style. Cosmetic only.

No new definitions or theorems were added by this lane (report-only review).
No premise of the owner task looks wrong; the structural-overlap reading of
the "misaligned store crossing a group boundary" requirement is sound given
the accepted alignment-free byte drain, and is documented in §5/CUTS.

## VERDICT: ACCEPT

Candidate 1307 (`c1d8ca610e923288ee5cced7d5a6fbcec62746bf`) is accepted for
integration: green probe with standard axioms, one-import-line hygiene,
lift-not-copy reuse, real refusals, non-degenerate two-core witness with a
memory-changing reached run, honest CUTS with no W/GX or hardware-
correspondence overclaim. No REPAIR items; one cosmetic advisory above.
