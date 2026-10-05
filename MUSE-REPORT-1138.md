# MUSE-REPORT-1138: Exact review of candidate 1137 (coherent machine fetching from the loaded image)

## VERDICT: ACCEPT

CANDIDATE: lane 1137, HEAD `485dd06fde7b75f0381245508dd5926b0dd80e79`, base `48a4be7c1c333a602ce0d0816979d154ae1bd959`
(reviewed from the staged exact snapshot `.tmp/review/author-1137/`: `PATCH.diff`, `OWNER-TASK.md`,
`MUSE-REPORT-1137.md`, `BUILD-EVIDENCE.json`; author clone itself not touched).

## What was checked

- Read the full candidate file (595 lines) and the complete `PATCH.diff` (705 lines).
- Grepped the candidate for `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`split_ifs`/`norm_num`/`ring_nf`:
  clean except the English word "admits" in two comments (doc line 290, witness line 351).
- Verified every reused accepted name exists in-tree with a matching signature:
  `hwPilot_weiter`, `hwByteschrittReg_rechtfertigt`, `hwByteschrittReg_verweigert`,
  `fetchExt_erfolg`, `decodeExt_kanonisch`, `fetch_leer_ohne_exec`, `pin_ext_nichts_leer`,
  `hwSchritt_wf`, `ComposeImageFetch_verbindung`, `adapterInteger666`, `byteschritt_weiter`,
  `bildZustand`/`projZustand`/`projFp`/`setKernVonFp`, `hwWitBild`, `hwWitReg0`/`hwWitXmm0`/`zeugeFlags`,
  `hwRipOut`/`hwRegOut`/`hwXmmTiefOut`, `tsoAnsicht`/`issueByte`/`loadByte`/`flushKern`,
  `extZugelassen`/`extLen`/`laengeOk`/`ausfuehrbarN`, `geladen`/`dateiByte`/`holeFetchAux`/`fetchCap`.
- Verified the dispatch-inversion case order against the accepted `decodeExt` definition
  (`ExtendedExecution.lean`: pilot, narrow, muldiv, shift, setcc, cmov, fp, vector) --
  the candidate's inversion proofs follow exactly this priority.
- Verified the `Grammatik.lean` hunk is exactly one appended import line; confirmed the new
  file is absent from master (true new file).
- Ran `./lean-bau` in this clone (base tree): green, last line
  `Build completed successfully (602 jobs).`
  Candidate build evidence (staged, at pinned HEAD): final `lean-probe` 0 errors, all 30
  `#print axioms` within `[propext]` / `[propext, Quot.sound]` (no `Classical.choice`,
  no `sorryAx`), final `./lean-bau` green at 601 jobs, clean commit `485dd06f`.

## Per-criterion result

1. No `sorry`/`axiom`/`native_decide`; axioms standard. PASS.
2. Existing files untouched except one import line (`PATCH.diff`: exactly 3 files;
   `Grammatik.lean` hunk adds only `import Grammatik.X86.HwLoadedImage`). PASS.
3. Every premise used: all hypotheses of all 30 theorems are consumed
   (`simp`/`rw` rewrites, `fetchExt_erfolg`/`ComposeImageFetch_verbindung` applications,
   refusal applications); no `intro _`, no discarded haves. PASS.
4. Accepted evaluator lifted, not copied: no decoder/executor/loader redefinition;
   every step cites accepted lemmas by name. PASS.
5. Planted refusals really refuse: `hwBild_ohne_exec_verweigert` proved generally;
   `hwBild_kern1_verweigert` and `hwBildWx_verweigert` are `decide`-closed
   (machine-checked at pinned HEAD under the green probe). PASS.
6. Witness non-degenerate: `hwBild_zeuge` joins an accepted image, two reached
   register steps (`decide`-closed RIP/rax/xmm observations), owner-only forwarding
   (core 0 sees 42, core 1 sees 0), and a drain changing shared loaded memory 0 to 42
   observed from both cores -- two cores, memory-changing reached run. PASS.
7. Silicon facts: no new encodings; witness bytes are the accepted `hwWitBild`
   (`encodeNarrow (.mov32rr .rax .rcx) ++ fpEncodeMovsdRR .xmm0 .xmm1`, 7 bytes);
   all byte claims `decide`-checked against accepted definitions. No hardware
   correspondence claimed. PASS.
8. CUTS honest, no W/GX claim: the CUTS block disclaims hardware correspondence,
   per-access W/GX simulation, whole-word atomicity beyond the reused guard,
   source/ABI/entry/budget links and the LOCK path. The report claims no more. PASS.

## Remarks (not verdict-changing)

- `hwBildSpeicherGleich`/`hwBildKernGleich` are stated as defs but the theorems take the
  unfolded equalities directly; harmless packaging, no rule violated.
- The task's MECHANISM offered a new event type or an embedding; the author reuses
  `ExtInstr` + `adapterInteger666` with a written no-duplication justification, and
  `hwBild_reg_pilot_ist_byteschritt` is the exact embedding. Honest reading, accepted.
- The obstruction lemma pins narrow only; the other six families are named as open in
  CUTS. Within the one-family scope, accepted.
- INTEGRATION NOTE: master has moved since the candidate base -- `Grammatik.lean` now
  ends with two further imports (`HwFaults`, `HwAddressed`, 605 lines total), so the
  candidate's import line needs mechanical re-append at merge (union, no conflict).
  Job count delta (601 candidate vs 602 base) is this drift, not a defect.

## Open (remains open, as the candidate itself states)

Per-family obstruction lemmas beyond narrow; per-access target-to-W/GX simulation;
source/IR/ABI/entry/budget links; LOCK RMW path. None claimed, none required for ACCEPT.
