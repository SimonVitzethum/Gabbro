# MUSE-REPORT-1122: Exact review of candidate 1121 (addressed loads/stores through TSO)

## VERDICT: ACCEPT

Candidate: lane 1121, HEAD `5fe35f25493157e98c05b7915d89c2685f549d24`
(base `8744590d77cbc7f31d809b4c62cd303bae4ed66f`, per
`.tmp/review/SNAPSHOT.json`). Reviewed from the in-clone exact snapshot
(`.tmp/review/author-1121/`: `PATCH.diff`, `MUSE-REPORT-1121.md`,
`BUILD-EVIDENCE.json`, `OWNER-TASK.md`); the candidate's author clone was not
touched (HARD RULES rule 1). Note: `.tmp/LANE.md` line 25 carries the
placeholder `<full pinned HEAD>`; the pinned hash above comes from
`SNAPSHOT.json`, whose `files` list matches the diff exactly
(`MUSE-REPORT-1121.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/HwAddressed.lean`, `clean: true`).

## What was checked

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`sorryAx`: scanned the
  full 727-line `PATCH.diff` and the 634-line snapshot file. The only matches
  are English prose ("admits", "admitted") and `#print axioms` lines.
- `#print axioms` standard: author-attested final probe shows
  `[propext, Quot.sound]` throughout, `[propext]` or no axioms for guard/witness
  pins — a subset of the goal-standard `propext, Classical.choice,
  Quot.sound`. Every main theorem has its `#print axioms` line (file end).
- Existing files untouched except one import line: diff stat is exactly the new
  `HwAddressed.lean`, `MUSE-REPORT-1121.md`, and one appended
  `import Grammatik.X86.HwAddressed` in `grammatik/Grammatik.lean`. The append
  point matches my clone's file end (`ISARelaxWitnesses`, line 603), so no
  conflict is expected.
- Lifted, never copied: every foreign name resolves to an accepted in-tree
  definition — `adrEff`/`adrEff_basisForm`/`effAddr`/`basisForm`/`skaliertForm`/
  `adrOk` (`grammatik/Grammatik/X86/AddressEncoding.lean:136,155,167,258,272`,
  `Ausfuehrung.lean:29`); `entriesOf`/`concAdmitted`/`concIssue`/
  `concIssue_haengt_an`/`concIssue_kein_speicher`/`concLoad`/
  `concLoad_nach_concIssue`/`concStoreMaschine`/`concLoadMaschine`
  (`ConcurrentIntegerExecution.lean:94,165,198,215,227,280,697,794,983`);
  `mergeRegNarrow` (`NarrowOps.lean:28`); `tsoAnsicht`/`projZustand`/`setTso`/
  `HwWf`/`HwAdapter`/`hwTeilwort_keine_gruppe`/
  `hwGruppe_verweigert_bei_fremdeintrag`
  (`HardwareExecution.lean:51,55,90,108,396,405,815`); `laengeOk`/`ripNach`/
  `regSet_gleich`/`zeugeFlags` (`Ausfuehrung.lean:20,23,139,761`); `addrOff`/
  `Fuss` (`Speicher.lean:15,207`); `wortEintraege`/`WortGruppe`/
  `fuss_mem_offset` (`WordAccessGrouping.lean:26,41,93`); `flushKern`
  (`TSO.lean:76`); `basisHw`/`basisBereit` (`FeatureProfile.lean:113,116`);
  `kontextReset` (`Gleitprofil.lean:66`). The candidate defines only its own
  layer (`hwAddrOf`, `hwAddrStore`, `hwAddrLoad`, `HwAddrEreignis`,
  `adapterAddr`, witness defs). Bridge theorems use the exact accepted
  signatures (`concStoreMaschine m c b base src disp len`,
  `concLoadMaschine m c b dst base disp len`); the `rfl`-closed bridges are
  credible because the author reshaped `hwAddrStore`/`hwAddrLoad` to the
  accepted construction (`{ setTso m s' with kerne := ... }`) — the recorded
  intermediate probes show the earlier structural mismatch failing and the
  final probe at 0 errors.
- Every premise used; no `intro _` / `have _` (grepped, zero hits); no premise
  has type `Prop` itself (`hwf : HwWf m` matches accepted precedent, and
  `exact hwf` is legitimate since `HwWf` depends only on `m.hw`/`m.bereit` —
  same shape as accepted `setKernDaten_wf`/`setTso_wf`,
  `HardwareExecution.lean:111-117`). `adapterAddr_store` (proof `h`) is a
  definitional adapter projection, precedented by `verweigertAdapter_verweigert`
  (`rfl`, `HardwareExecution.lean:823-825`) and the `adapterInteger666`/
  `adapterFp668` construction pattern — the exact-embedding statement the owner
  task asked for, not a rule-4a vacuity.
- Refusals really refuse: bad length both directions, refused gate both
  directions (as `= none`), refused adapter event (`rfl`), tearing and overlap
  as `¬ WortGruppe` lifts of the accepted guards with `decide`-closed side
  conditions in the witness.
- Witness non-degenerate (`hwAddrWit_zeuge` joins 11 conjuncts): two cores,
  SIB form `rbx + rcx*8 + disp8(0)` naming address 8200
  (8192 + 1*8 + 0; scale 8 and disp8-with-base are valid SIB/mod=01 shapes;
  width-4 access fits the 8192..8208 data permission), 4 buffer entries, RIP
  4096 -> 4103 past `len = 7` (`laengeOk` admits 1..15), owner-only forwarding
  (core 0 reads `0x01020304`, core 1 reads 0), 4-flush drain changing the
  shared byte 0 -> `0x04` with both cores observing the new value afterwards,
  beside both refusals and `HwWf`. The initial-zero pin makes the
  memory change observable. The `decide` pins evaluated green in the recorded
  final probe.
- Silicon facts: consistent with the accepted canonical forms; scale,
  displacement class, widths (1/2/4/8 via `Breite`), and TSO ordering all come
  from accepted definitions. No hardware correspondence beyond
  self-consistency is claimed — CUTS says so explicitly, and no W/GX, codec,
  LOCK/RMW, fault, loader, entry, or budget claim is made.

## Build evidence

- Candidate-attested: `./lean-probe grammatik/Grammatik/X86/HwAddressed.lean`
  `== 0 error(s) in the COMPLETE output; exit 0`; `./lean-bau`
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (601 jobs)` (BUILD-EVIDENCE.json, with the
  iteration history from 5 errors down to 0 preserved).
- Reviewer-run: `./lean-bau` on my clean base (without the candidate file —
  applying it would violate OWN ONLY): green,
  `Build completed successfully (600 jobs)`. The delta of exactly one module is
  consistent with the candidate's 601-job build. I did not independently rebuild
  the candidate tree; the 601-job green result is author-recorded, not
  reviewer-reproduced.

## Observations for the merger (non-blocking)

- BUILD-EVIDENCE's last `git status` shows `M grammatik/Grammatik.lean`
  unstaged (untracked report + new file) while `git log` shows the lane commit
  `5fe35f25`. Confirm the import line is inside the committed HEAD before
  merging; `SNAPSHOT.json` claims `clean: true` at that hash.
- `hwAddrWitM0_wf` uses `intro c f _` (premise discarded because `basisHw`
  has every feature — a stronger unconditional fact). Same shape as accepted
  `hwWf_aus_zugelassen`; not a finding.

## Owned files touched

- `MUSE-REPORT-1122.md` (this file) — only file owned and only file written.
  No Lean, Rust, or document changes made.
