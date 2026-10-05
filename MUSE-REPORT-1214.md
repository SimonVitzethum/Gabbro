# MUSE-REPORT-1214: Independent exact review of candidate 1213

CANDIDATE: 1213 255c9ec93e60ad2430f7e15b6be7697661e1d17f

## Candidate

- Author lane 1213, pinned HEAD `255c9ec93e60ad2430f7e15b6be7697661e1d17f`,
  base `988d75ef42521f5d437a0cb4b9d92b5d5c2e38f2` (per
  `.tmp/review/SNAPSHOT.json`).
- Files (per snapshot, confirmed in `PATCH.diff`): `MUSE-REPORT-1213.md`
  (new), `grammatik/Grammatik.lean` (one appended import line),
  `grammatik/Grammatik/X86/TsoRmwLink.lean` (new, 441 lines).
- Review basis: exact candidate diff only
  (`.tmp/review/author-1213/PATCH.diff`, 571 lines) plus author's
  `MUSE-REPORT-1213.md`, `BUILD-EVIDENCE.json`, `OWNER-TASK.md`, cross-checked
  against the base tree in this clone (`TsoRmwBridge.lean`, `HwLockRmw.lean`,
  `Speichermodell/Sicht.lean`, `Speichermodell/MaschineW.lean`).
- This reviewer owns ONLY this report. No other file was created or modified.

## Checks performed (each against the exact diff)

1. **Forbidden tactics/axioms.** Grep over the candidate file for
   `^axiom`, `^unsafe`, `native_decide`, `sorry` finds nothing. The only
   matches for `admit`/`admitted` in the diff are English prose
   ("admitted step", "admit no link event"), not the `admit` tactic. No
   `split_ifs`, `norm_num`, `ring_nf`. No `intro _` / `have _ :=`.
   PASS.
2. **`#print axioms` standard.** Author evidence (`lean-probe` output in
   `BUILD-EVIDENCE.json`): main link/chain/witness theorems depend on
   `[propext, Quot.sound]`; history pins on `[propext]`; the two `rfl`
   pins on no axioms. All within the goal's standard set (`propext`,
   `Classical.choice`, `Quot.sound`). The file ends with `#print axioms`
   for every theorem (14 lines). PASS.
3. **Existing files untouched except one import line.** `Grammatik.lean`
   diff is exactly one appended line
   `import Grammatik.X86.TsoRmwLink`. Everything else is the new file plus
   the author report. PASS.
4. **Every premise used.** Verified per theorem from the diff:
   `rmwLink_adapter_wf` (both premises feed the lifted lemma);
   both refusals (all premises feed the lifted refusal lemmas);
   `rmwLink_xadd` / `rmwLink_cmpxchg_erfolg` /
   `rmwLink_cmpxchg_fehlschlag_nur_liest` (machine guards feed the
   accepted step equation via `obtain`, history guards `hwahl/hmem/hle/
   hlt/hne` each feed one `RmwLink` field; `rw [hwahl]` + `rfl`
   close the value/adjacency links); `rmwLink_kette` (h1 feeds write
   pairing + first adjacency, h2 feeds read pairing + second adjacency +
   written value, `hkette_ts`/`hkette_wert` feed the rewrites; both
   `omega` goals use the cited adjacencies); `rmwLink_kette_ohne_puffer`
   (all 38 arguments passed explicitly by position to
   `tsoRmw_kette_ohne_verlust`, including `hbuf1`/`hbuf2` as the
   no-intervening-store guards). No `Prop`-typed premise, no discarded
   hypothesis. PASS.
5. **Accepted evaluator lifted, never copied.** The file imports only
   `Grammatik.X86.TsoRmwBridge` and `Grammatik.Speichermodell.Sicht`,
   defines no machine/evaluator of its own, and cites only accepted
   names — each confirmed present in this clone's base tree:
   `tsoRmwAdapter_wf`, `tsoRmw_puffer_bleibt_verweigert`,
   `tsoRmw_unaligned_bleibt_verweigert`, `tsoRmw_xadd_einzel_rmw`,
   `tsoRmw_cmpxchg_erfolg_einzel_rmw`,
   `tsoRmw_cmpxchg_fehlschlag_rmw`, `tsoRmw_kette_ohne_verlust`, plus the
   reached-run witnesses (`hwLockWitStart`, `tsoRmwWitEv1/Ev2`,
   `hwLockWit_nach1_eigen/fremd_sicht`, `hwLockWit_puffer/unaliagned`
   family). `hwLockSchrittEv` shapes and `Fuss` footprints are reused.
   PASS.
6. **Planted refusals really refuse.** `rmwLink_puffer_verweigert`
   (pending own store, `m.puffer c = e :: rest`) and
   `rmwLink_unaligned_verweigert` (`ausgerichtet8 = false`) both conclude
   `tsoRmwAdapter.schritt … = none` by lifting the accepted refusal
   lemmas, and both refusal shapes reappear as conjuncts of the joint
   witness on reached states. PASS.
7. **Witness non-degenerate.** `rmwLink_zeuge` joins on the accepted
   reached two-core run: event words 10 → 15 → 22 across cores 0/1
   (`tsoRmwWit_ev1_gelesen/geschrieben`, `tsoRmwWit_ev2_gelesen`), both
   steps changing actual shared memory on different cores; owner-only
   forwarding (`eigen` sees byte 99, `fremd` sees 0); `HwWf`; both
   planted refusals; history value link (`witWahl_lesbar`) and `rmw`
   adjacency (`witNeu_frisch` via `witNeu_adj`). `Lesbar`/`Frisch`
   definitions in `Sicht.lean` confirm the witness pins are the real
   shapes (`v x ≤ ts`, `v x < ts` + freshness), discharged by
   `decide`/case split, not by assumption. PASS.
8. **Silicon facts.** No new silicon claim: provenance stated as Intel SDM
   325462-093US via the accepted 662 module + lane 1145; aligned
   whole-word atomicity explicitly kept as a selected-profile contract
   (`ausgerichtet8` + empty own buffer), never a hardware proof.
   Only the accepted `xadd64`/`cmpxchg64` forms are linked. PASS.
9. **CUTS honest, no overclaim.** The file header SCOPE block and the
   CUTS block state the exact boundary: link proved over the generic
   history shape (`Nachricht`/`Lesbar`/`Frisch` at `Adresse`/`Wort`);
   the `rmw` field of a full `SchrittW` (which quantifies over Gabbro
   `Glob`s, confirmed at `MaschineW.lean:191`) is *shaped, not
   discharged*; no per-access target-to-W/GX simulation, no hardware
   correspondence beyond self-consistency, no fetched-byte dispatch, no
   fairness/retry bound, no source/checker/contract/budget/goal change.
   The author's task critique (report §"Task critique") correctly notes
   the task bullet overreaches as stated and records what IS proved
   instead. No W/GX or hardware-correspondence claim. PASS.

## Last `./lean-bau` result line

- Re-run in this review session (shell available again):
  `./lean-bau` in this clone → `Build completed successfully (640 jobs).`
  This covers the base tree in this clone (the candidate module is not
  merged here, so this confirms a green base, not the candidate module
  itself).
- Candidate-module build per author evidence (`BUILD-EVIDENCE.json`,
  committed with the candidate): `./lean-probe
  grammatik/Grammatik/X86/TsoRmwLink.lean` →
  `== 0 error(s) in the COMPLETE output; exit 0` (after an honest
  recorded repair of the 2-error `assumption`-unification failure, fixed
  by explicit positional arguments, no premise added, no conclusion
  weakened); `./lean-bau` → `Build completed successfully (640 jobs).`
  The probe output lists the per-theorem axiom dependencies quoted in §2
  above. I cross-checked every review bullet statically against the exact
  diff and the base tree in addition to the build evidence.

## Blocker (resolved)

- `bash` was refused by the permission classifier earlier in this session
  (candidate-external `git -C …/a1213` access, correctly refused per HARD
  RULES §1; then even plain in-clone commands). Shell access recovered on
  retry: `./lean-bau` re-run green (see above) and this report is
  committed via `./commit.sh` below. No remaining blocker.

## What remains open (candidate's own, endorsed)

- No accepted x86-address → Gabbro-carrier map: source/table-write
  consumer lanes own it; full per-access target-to-W/GX simulation OPEN.
- Narrower widths, other addressing modes, split-lock detection,
  fetched-byte dispatch, fairness/retry bounds: OPEN as before.

## Task critique

- The review task is sound. Its requirement to read "the candidate diff
  only … in the author clone" conflicts with HARD RULES §1 (touch nothing
  outside this directory) when the author clone is a sibling directory;
  the reviewed snapshot under `.tmp/review/author-1213/` inside this
  clone is the correct resolution and is what was used (pinned HEAD
  recorded above).

## Verdict

VERDICT: ACCEPT

Candidate 1213 at `255c9ec93e60ad2430f7e15b6be7697661e1d17f` is accepted:
exact diff reviewed, all nine review bullets pass, axioms standard, CUTS
honest with no hardware-correspondence or W/GX overclaim. Integration may
proceed through the normal serial checked-publication gate (which will
re-run the build this session could not).
