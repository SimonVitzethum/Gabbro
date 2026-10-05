# MUSE-REPORT-1134: Exact review of candidate 1133

CANDIDATE: 1133 9772755d059b4282205fde0924a304a694bef9d6

Lane 1134, clone `/home/simon/Dokumente/gabbro-muse/a1134`, branch `muse/1134`
(verified). OWN ONLY this report. No Lean code added by this lane.

The reviewed candidate is lane 1133, pinned HEAD
`9772755d059b4282205fde0924a304a694bef9d6` (base `8744590d`), reviewed from
the exact snapshot in
`.tmp/review/author-1133/` (`SNAPSHOT.json`: files `MUSE-REPORT-1133.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwDevices.lean`,
`clean: true`; `PATCH.diff` 1102 lines; `HwDevices.lean` 994 lines, read in
full). The author clone was not directly readable under this lane's
permissions, so the pinned snapshot is the review basis.
This is a re-review: the previous pinned HEAD `d9e7092f` was reviewed and
ACCEPTed; the author then added a repair turn (new HEAD above) after an
integration-gate failure. The re-review below inspects the repair delta
and re-checks every previous finding against the new snapshot.

## Checks (one per task criterion)

1. **No sorry/axiom/native_decide**: grepped the snapshot. In
   `HwDevices.lean` the only matches are prose "admitted"/"admits" and
   `#print axioms` lines. No `sorry`, `admit` tactic, `axiom`, `native_decide`,
   `unsafe`, `split_ifs`, `norm_num`, `ring_nf`, `intro _`, `have _ :=`.
   The `intro c f _` in `witStart1133_wf` discards an introduced
   implication hypothesis of a premise-free theorem and matches accepted
   precedent (`hwWf_aus_zugelassen`, `HardwareExecution.lean`). PASS.
2. **`#print axioms` standard**: author build evidence lists every main
   theorem at `[propext, Quot.sound]` or less (several depend on no axioms).
   Subset of the goal axioms. PASS.
3. **Existing files untouched except one import line**: `PATCH.diff` touches
   exactly the three owned files; the `Grammatik.lean` hunk is one line,
   `+import Grammatik.X86.HwDevices`. PASS.
4. **Every premise used**: manual audit of all theorems. Both named
   assumptions enter `hwDev_zeuge` as premises (`hbus`, `hdma`) and are
   discharged into concrete facts (`ucPinsLaenge`, `dmaAnnahme_verweigert`).
   No Prop-typed premise, no quantified-away contract, no restated premise.
   `obtain` wildcards discard only unneeded conjuncts of helper lemmas, not
   theorem premises. PASS.
5. **Evaluator lifted, not copied**: all 14 cited accepted theorems
   (`ucStore_bypass`, `ucStoreZugriff_erfolg`, `ucLoad_rahmen`,
   `ucLoadZugriff_erfolg`, `busFortschritt_fifo`, `busSchritt_aus/ein_fetch`,
   `latch_aus/ein_sound`, `maschineRegLaden_gleich`,
   `ucLoad_verweigert_bei_ausstehend`, `ucStore_verweigert_ohne_profil`,
   `verweigertAdapter_verweigert`, `setKernDaten_wf`) and ~30 used
   definitions verified present in current-master family files with
   compatible signatures. The candidate defines only new names under
   namespace `HwDev1133`; field orders checked (`MmioMaschine` 6-tuple,
   `HwKern` 5-tuple, `PostedSchreib` triple, `Region` 5 fields). No
   redefinition, no name collision (`HwDev1133` absent from master).
   `DeviceCommonExecution.lean` correctly left out (present in tree but not
   imported in `Grammatik.lean`, confirmed). PASS.
6. **Planted refusals really refuse**: UC-load leg `rfl`-none; non-UC store
   via gate-false; port fetch/forged-decode/permission/pending-buffer gates;
   DMA via `verweigertAdapter`; overlap/profile refusals via the accepted
   refusal lemmas. Refusal shapes re-executed independently (see below).
   PASS.
7. **Witness non-degenerate**: device byte 0 -> 7 AND RAM cell 0 -> 42, two
   cores, owner-only forwarding (core 0 reads 42, core 1 reads 0) before the
   drain; joint `hwDev_zeuge` joins both named assumptions with reached
   `HwDevSchritt` UC-retire and FIFO bus completion beside DMA/kind/overlap/
   profile refusals. PASS.
8. **Silicon facts**: no new hardware facts. UC ordering and DMA stay named
   assumptions; the port pending-buffer gate reuses accepted `zaunBereit`,
   documented against SDM Table 20-1 in the accepted `Bus704` header; SDM
   provenance points at the accepted 676/694/704 headers, extracts present
   clone-locally. PASS.
9. **CUTS honest, no oversized claim**: CUTS block lists proved vs explicitly
   not proved (no hardware correspondence, no WC/WT/WP, no DMA engines, no
   liveness/timing, stateless port plug, no W/GX, no source/checker/goal
   links). Report matches the file. PASS.

## Independent execution

- `./lean-bau` on the clean clone: green,
  `Build completed successfully (634 jobs).`
- Full own-compile of the candidate in this clone was BLOCKED: staging
  `HwDevices.lean` + the import line under `grammatik/` is outside this
  lane's owned files and was denied (bash `cp` and Write both refused).
  Precise blocker, no workaround attempted beyond it (no network, no author
  clone access).
- Instead, scratch probe `.tmp/rev1134-probe.lean` (private scratch, not
  committed) re-executes the candidate's computational core against
  current-master family code: triple-gate facts, exact posted store shape
  via `ucStoreZugriff_erfolg`, FIFO drain (queue empty, log kept, device
  byte 0 = 7), both UC refusals, DMA-kind refusal, RAM-zero start,
  owner-only forwarding, drain-to-42. `./lean-probe`: 0 errors, exit 0.
  This also clears the base-drift question (candidate base `8744590d`,
  601 jobs; review master `de94b21c`, 634 jobs): every relied-upon API is
  present and computes identically here.

## Verdict

VERDICT: ACCEPT

Candidate 1133 at `9772755d059b4282205fde0924a304a694bef9d6` is accepted for
merge: exact lift of the accepted UC/port evaluators onto the coherent
machine with `HwWf` preservation, exact bypass/load-frame/FIFO agreement,
`HwAdapter` plugs with genuine refusals, and a non-degenerate joint
witness; axioms standard; claims match the proof.

## Re-review of the repair turn (new HEAD)

- Delta inspected: `HwDevices.lean` is semantically unchanged (same 994
  lines; identical grep profile — only prose "admitted"/"admits" and
  `#print axioms` lines; spot-checked regions lines 1-120, 410-434,
  888-916 verbatim identical to the previously reviewed snapshot).
  `Grammatik.lean` still exactly one import line. The only delta is the
  author report's new section "Integration-gate failure analysis".
- New build evidence: author re-ran `./lean-probe` (0 errors, full axiom
  dump) and `./lean-bau` (exit 0, 601 jobs green) on the exact new HEAD.
- Integration-gate failure assessed: the gate error is
  `failed to read file .../Lean/Elab/Tactic/Do/ProofMode/Assumption.olean.private`
  at the umbrella `Grammatik` link step in `/home/simon/Dokumente/Gabbro`,
  while this module's own `#print axioms` lines printed in the same log —
  i.e. the module compiled there and the failure is a corrupt
  toolchain-private olean in the integration environment (apparatus fault,
  known AGENTS.md §9 class), not a candidate defect. The author correctly
  made no semantic edit to chase it and claims no full-chain acceptance.
  The coordinator-side fix (repair/replace the corrupt elan toolchain or
  its poisoned cache, then re-run the gate) is outside this lane.
- All nine criteria re-checked against the new snapshot: unchanged PASS.
  Previous ACCEPT verdict reaffirmed on the new hashes, not carried over
  from a stale snapshot.

## Open / notes (not defects)

- The final merge rebuild on current master is the merger's gate; no
  incompatibility found here.
- `wit_art_1133` restates an already-accepted equation
  (`DeviceHardwareForms.lean`) as a witness component under a new name;
  harmless.
- The witness WB leg rides TSO functions directly rather than
  `HwDevSchritt`; the task's owner-only-forwarding requirement is still met
  as computed facts beside reached device steps.
- Scratch file `.tmp/rev1134-probe.lean` left in private scratch, uncommitted.
