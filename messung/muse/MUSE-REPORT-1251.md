# MUSE-REPORT-1251: Discharge of the DRF/checker premises of the W-to-GX refinement

## Clone / branch

- Clone: `/home/simon/Dokumente/gabbro-muse/a1251`, branch `muse/1251` (verified at start).
- Owned files only: `grammatik/Grammatik/X86/TsoGxChecker.lean` (new),
  `grammatik/Grammatik.lean` (one appended import line), this report.

## What was done

Follow-up of lane 1215 (`TsoGxRefine.lean`, unmerged — no such file exists in
this clone, so the discharge is proved against the accepted vocabulary the
refinement premises are stated in). New file
`grammatik/Grammatik/X86/TsoGxChecker.lean` proves the checker-side premises
from accepted checker/footprint facts only, reusing them unchanged:

- `abgK_von_akzeptiert`: checker Bool `C.akzeptiert E … = true` gives
  `AbgK E.P fs.1 (reachB E.P fs.1 w)` for every root `w`, via `Pruefer.korrekt`
  (soundness against `AkzeptiertSpec`). Content is the Bool-to-Prop step, not a
  restatement.
- `fussSX_von_akzeptiert`: the same Bool gives
  `FussSX E.P E.S (lokW E.P fs.1 E.ws) (GeteiltV E.P E.ws) f` for every `f`,
  via the accepted embedding `akzeptiertSpecX_of_spec`
  (`Zielsatz/AtomarAkzeptiert.lean`, itself via `fussSX_of_fussS`).
- `kein_geteiltV_von_akzeptiert`: with a complete member list, the same Bool
  gives `¬ GeteiltV E.P E.ws c` for every carrier, via the accepted
  `geteiltV_leer` (`Zielsatz/BeweisAtomar.lean`).
- `checker_liefert_wgx_pruefer`: the three jointly (closed call graphs,
  footprint with the rely, empty admitted set).
- `checker_liefert_wgx_pruefer_zeuge`: joint witness on the non-degenerate
  two-thread unit — concrete checker `akzeptiert_pruefer` accepts `mE`
  (`mP_akzeptiert`, decided), member lists complete (`mFs_voll`,
  `mLocks_voll`, `mCs_voll`), and `hauptA` writes table `privA`
  (`TraegerSchreibt … = true` by `rfl`; cf. `zweiFaeden_bewegt_gilt` for the
  memory-changing run). Note: the bare name `mE` resolves to the `Merkmal`
  predicate, so the witness uses `Zielsatz.mE` explicitly.

## Last build result

- `./lean-probe grammatik/Grammatik/X86/TsoGxChecker.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (644 jobs).`
- `#print axioms` for all five theorems: exactly
  `[propext, Classical.choice, Quot.sound]` (standard).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise is used.

## What remains open (FINDINGs, not assumptions)

- FINDING 1 (`GutO`): the oracle bound is a named hardware assumption (goal
  shape (c)), not a checker fact — no checker Bool constrains oracle answers.
  Holds per-oracle by construction only (`zO_gut`, `mO_gut`). Stays an
  explicit premise of any refinement use; assumed nowhere here.
- FINDING 2 (`StartExklusiv`): property of the thread-start assignment, not of
  the checked unit (`wurzeln` constrains declared starts, not `init`). Holds
  per-program by construction (`zInit_exklusiv`, `mInit_exklusiv`) at the
  `Laufzeit` leg (goal shape (d)). Assumed nowhere here.

## What in the task is wrong / mismatched

- The CONTEXT/MECHANISM paragraphs (`HwAdapter`, `HwWf` preservation,
  two-core forwarding witness) are generic connection-wave boilerplate for
  hardware-family lanes and do not apply to this checker-side discharge: the
  file adds no machine steps, so no `HwAdapter` is instantiated (the refused
  default stands) and no `HwWf`/forwarding witness is owed by this file. This
  is recorded in the file's CUTS block. The TASK paragraph (discharge or
  FINDING, assume nothing) is fully delivered.
- Lane 1215's `TsoGxRefine.lean` is not in this clone (unmerged); the
  discharge targets the accepted premise vocabulary (`GutO`, `AbgK`,
  `FussSX`/`GeteiltV`, `StartExklusiv`) so it applies once that file lands.
