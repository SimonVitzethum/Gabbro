# MUSE-REPORT-1136: independent exact review of candidate 1135

CANDIDATE: 1135 9dceb14fb7c97b2a67ae9bfeccd9204c6bda2449
VERDICT: ACCEPT

## Identity and candidate pin

- Clone `/home/simon/Dokumente/gabbro-muse/a1136`, branch `muse/1136`: verified
  (`pwd`, `git branch --show-current`). Own tree clean before and after review.
- Review input only: `.tmp/review/SNAPSHOT.json` pins author 1135,
  HEAD `9dceb14fb7c97b2a67ae9bfeccd9204c6bda2449`,
  base `48a4be7c1c333a602ce0d0816979d154ae1bd959`, 3 files, clean.
  Inspected `PATCH.diff` (793 lines) and the snapshot file copies; no access
  outside this clone. Nothing except this report is added or changed here.

## Scope (from PATCH.diff)

- NEW `grammatik/Grammatik/X86/HwFeatureGates.lean` (703 lines, 14 defs,
  2 inductives, 46 theorems), one appended import line in
  `grammatik/Grammatik.lean`, plus `MUSE-REPORT-1135.md`. No other file
  touched. `Grammatik.lean` change is exactly `+import Grammatik.X86.HwFeatureGates`.

## Checks performed (all independent, in this clone)

- Banned tokens: strict `rg` over the candidate file for `sorry`/`admit`
  (word-boundary), `sorryAx`, `native_decide`, `unsafe`, `split_ifs`,
  `^axiom` — zero hits. The only substring hits are English prose
  ("admitted"/"admits") and `#print axioms`. No new `axiom` declaration.
- Axioms: reproduced with `./lean-probe` on the snapshot file —
  `== 0 error(s) in the COMPLETE output; exit 0`, every theorem
  `[propext]` or `[propext, Quot.sound]` (closing `hwTor_verbindung` and
  `hwTor_verbindung_zeuge` both `[propext, Quot.sound]`). Standard subset,
  no `Classical.choice`.
- Premise use: `hwTor_verbindung` proof consumes every premise
  (`hoff`/`hstep`/`hmem` into the admitted step, `hwf` into Wf,
  `hissue`/`hrd` into `load_nach_issue`, `hflush`/`e`/`hrest`/`hbuf`
  into `flush_schreibt_kopf`, `hstep` into the fault-silence leg).
  No `intro _`, no `have _ :=`, no `Prop`-typed premise, no
  quantified-away contract. Generic refusal `hwTor_verweigert_bei_zustand`
  case-splits all 8 `ExtInstr` constructors (verified the inductive has
  exactly these 8 in `ExtendedExecution.lean`).
- Lift-not-copy: every family fact is an accepted lemma
  (`stepExt_vec`/`stepExt_fp`, `stepVector_pxor`, `fpSchritt_movsdRR`,
  the four `profil`/`laenge_verweigert` lemmas, `vecEintritt_merkmal`,
  `load_nach_issue`, `flush_schreibt_kopf`, `stepExt_verweigert_kein_de`);
  all names resolve in this tree; collision grep for the `hwTor*`/
  `HwTor*`/`adapterFeatureTor` family over `grammatik/` is empty.
  `adapterFeatureTor` follows the `adapterInteger666` register-plug
  discipline plus the gate condition. Exact embedding
  `hwTorSchritt_ok_reg` targets the accepted `HwSchritt.reg` constructor
  (signature verified).
- Planted refusals: `hwTor_unbereit_schritt`/`hwTor_ftz_schritt` prove
  `stepExt = .verweigert` through lifted lemmas; `ud` legs cover OS-off,
  FTZ and absent-observed-bit gates; half-gated machine executes on core 0
  and takes `#UD` on core 1 for the same form. All `decide`/`rfl`
  gate equations re-verified green by the probe run.
- Witness: `hwTor_verbindung_zeuge` (15 conjuncts) jointly instantiates
  every `hwTor_verbindung` premise on concrete values (two family steps
  execute, TSO leg changes actual shared memory 0 to 42 with
  owner-only forwarding, two-core open/closed split). Non-degenerate per
  the task's bespoke criteria.
- Silicon: no new hardware definition; witness lengths/forms satisfy the
  accepted lemmas by computation; closed-gate to `ArchFehler.ud` mapping
  reuses the accepted fault class while step refusal stays
  `klassifiziereExt`-silent (verified in `HardwareFaults.lean`). No new
  silicon claim. The author's disclosed limitation is real and verified:
  accepted `stepExt (.fp f) t b` ignores `b` (matches only on
  `fpSchritt f t`), so the FP `BereitProfil` leg and the observation leg
  are wrapper-enforced by construction, as CUTS states. Nothing was
  weakened to fit.
- CUTS: honest; explicitly disclaims FP-profile/observation/silicon-absent
  step enforcement, memory-form plug use, source/checker/emitter
  correspondence, W/GX bridge, whole-word atomicity beyond TSO bytes,
  image/loader/entry/budget. No hardware-correspondence or W/GX claim.
- `./lean-bau`: `Build completed successfully (602 jobs).` (baseline tree;
  602 vs author's 601 because master moved ahead — see note below.)

## Notes for the merger (non-blocking)

- Candidate base `48a4be7c` predates the 1121–1124 merges now on master
  (`HwFaults`, `HwAddressed` imports). `Grammatik.lean` needs the usual
  import-union; candidate adds no edit to any existing definition, so no
  semantic conflict is expected, but the merged tree must rebuild.
- Closing theorem is vector-specialized; FP is covered by admission plus
  executability conjuncts, exactly as the disclosed accepted-step
  limitation requires. This is scope honesty, not a defect.
- Report prose says "three #UD refusals" for the witness; strictly the
  joint witness packs two refusal legs plus step-level refusals, with the
  third leg as a separate planted-refusal theorem. Prose looseness only.

## Open

- None from this review. Merge-time rebuild and import union belong to
  the serial integration, not to the candidate.
