# MUSE-REPORT-1298: Exact review of candidate 1297 (paging: large pages, SMEP/SMAP)

## Verdict: ACCEPT

Candidate 1297 (`97599d0b512ea48a2c74ef9e3da70f865efbfb9b`, base `234f2728`,
files `MUSE-REPORT-1297.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/HwPagingLarge.lean`) meets the task: large-page
walks plus per-access SMEP/SMAP as new functions that provably equal the
accepted 4 KiB walk where it applies, with fault codes, machine embedding
and a non-degenerate joint witness. No fake closure found.

## What was checked

- Clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a1298`,
  branch `muse/1298`. Author clone and pinned hash never touched; the
  candidate was reviewed from `.tmp/review/author-1297/` files only.
- `./lean-probe .tmp/review/author-1297/grammatik/Grammatik/X86/HwPagingLarge.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`. All 41 `#print axioms`
  lines are standard subsets (none / `propext` / `propext`+`Quot.sound`).
- `./lean-bau` on the clean review tree:
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (678 jobs).`
- Grep over the candidate file: no `sorry`/`admit`/`native_decide`/`unsafe`/
  `axiom` (only the English word "admits" in comments); no `split_ifs`/
  `norm_num`/`ring_nf`/`intro _`/`have _`.
- Existing files: PATCH shows exactly one added line in
  `grammatik/Grammatik.lean` (`import Grammatik.X86.HwPagingLarge`);
  everything else is the new file plus the author report.
- Lift, not copy: the file reuses `blattPruefung`, `gangEbenen`,
  `seitenTabEintrag`, `seitenGangTab`, `seitenGang_fst`,
  `seitenGangTab_nichtOk`, `verweigertAdapter`, `HwSchritt`,
  `hwSchritt_wf`, `pfCodeBits`, `eintragKodieren`/`eintragDekodieren`,
  index/offset/canonicality helpers and the `hwWit*` two-core run. All
  resolve in this clone (probe elaborated the file against this tree's
  `HwPaging.lean`/`HardwareExecution.lean` with 0 errors). Agreement is
  proved, not asserted: `grossBlatt_ohne_schutz` (via `blatt_ok_payload`),
  `gangGross2M_gleich`, `gangGross1G_gleich`, `gangGross_gleich`,
  `seitenGangGross_gleich`, plus exact two-way machine embedding
  (`hwGrossSchritt_einbettung_vor`, `hwGrossSchritt_alt_invert`,
  `hwGrossSchritt_einbettung_zurueck`) and `hwGrossSchritt_wf`.
- Every theorem premise is used (spot-checked: `h1`/`h2`/`hg1`/`hg2`
  rewrite in the `gleich` lemmas; `hsmep` in `grossBlatt_ac_gleich`;
  `hwf` in all three `wf` branches; `hg` in both `gp_verweigert`
  conjuncts). No conclusion restates a premise; no `Prop`-typed premise.
- Refusals really refuse: `adapterGross_verweigert` (adapter admits
  nothing), `grossSeitenGp_verweigert` (no walk/fault step on `#GP`),
  `wit_gross_nichtkanonisch_gp` (`2^47` evaluates to `.gpFehler` by
  `decide`).
- Witness `hwGross_zeuge` is non-degenerate: two mapped large pages of
  different sizes (2 MiB `.ok 2097152`, 1 GiB `.ok 2^30`), three fault
  classes (RSVD misalignment, SMEP fetch, SMAP data), joined with the
  accepted two-core TSO run (owner-only forwarding, foreign-observed
  stale value, memory-changing drain `0 -> 42` visible from both cores).
- Silicon honesty: entry bit positions, alignment multiples, SMEP/SMAP/AC
  rule shape, error-code cause mapping and canonical width are all named
  assumptions in CUTS; no Vol 3A provenance claimed (none was supplied to
  either lane); no hardware-correspondence and no W/GX claim. The pinned
  error codes 13/17/3 are `decide`d against the accepted `pfCodeBits`.

## Minor notes (non-blocking)

- Four `decide`-closed witness theorems (`wit_gross_nichtkanonisch_gp`,
  `wit_gross_zugriff_gesetzt`, `wit_gross_schmutzig_gesetzt`,
  `wit_gross_unberuehrt_still`) have no `#print axioms` line; harmless
  since `decide` proofs are axiom-free, but the per-theorem print
  convention is not fully uniform.
- This tree's baseline `./lean-bau` already contains one pre-existing
  `Classical.choice` dependency in another module
  (`btWit_zeuge`, `IntBitTest.lean`, not part of this candidate).

## Open

- Nothing open on this review. Integration (merge of 1297) is the
  coordinator's serial step, not this lane's.
