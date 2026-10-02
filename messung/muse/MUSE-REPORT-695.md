# MUSE-REPORT-695: Exact review of author 694 (UC MMIO access and ordering)

Lane 695, clone `/home/simon/Dokumente/gabbro-muse/a695`, branch `muse/695`.
OWN ONLY: this report. No source, control, or registry changes.

CANDIDATE: 694 83a21c4c5173368b1135c3d0f9ad549ad3639397
VERDICT: ACCEPT

## 1. What was reviewed

- Pinned snapshot: `.tmp/review/SNAPSHOT.json` (author 694, base
  `122c224220c3f5c73844a9f70aba9b7e765d4a6d`, files
  `MUSE-REPORT-694.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/MemoryTypeHardwareExecution.lean`, clean true).
- Exact material: `.tmp/review/author-694/PATCH.diff` (1578 lines, 3 files),
  `.tmp/review/author-694/grammatik/Grammatik/X86/MemoryTypeHardwareExecution.lean`
  (1440 lines, read in full in 4 ranges),
  `.tmp/review/author-694/OWNER-TASK.md`, `MUSE-REPORT-694.md`,
  `BUILD-EVIDENCE.json` (27 commands, final `lean-probe` 0 errors,
  `lean-bau` green, 8 commits ending `83a21c4c`).
- Base cross-checks inside this clone (read-only): all reused names exist —
  `fetchExt`/`stepExt`/`geholt` (`Byteschritt`/`ExtendedExecution`),
  `effAddr`/`ripNach` (`Ausfuehrung`), `mergeRegNarrow` (`NarrowOps`),
  `trunc` (`Wort`), `merkmalZugelassen`/`basisHw`/`basisBereit`
  (`FeatureProfile`), `wortByte`/`disjunkt_von_intervallen` (`Speicher`),
  `zeugeFlags`/`kontextReset`, `fpEncodeMovsdSpeichere`
  (`ScalarFloatCodec`), `Befehl.load64/store64`, `store32`, FP `movsd` rows.
- Manual: `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
  (Intel SDM 325462-093US, Sept 2026, sha verified 2026-10-02) plus
  `intel-instruction-reference.txt` (17.7 MB). Spot-searched claimed passages.

## 2. Architecture (not just Lean green)

- Byte forms: fetched level handles exactly pilot `load64`/`store64` plus
  narrow `store32` through accepted `fetchExt`/`stepExt`; every other form
  (incl. all FP rows not to UC, vector register-only rows) delegates.
  8/16-bit fetched and 32-bit fetched loads have access-level
  `geraetLiest`/`geraetSchreibt` rows but no byte path and refuse there —
  stated openly in CUTS, not silently dropped.
- Width/register semantics: UC load answers via architectural
  `mergeRegNarrow` into `dst` (`maschineRegLaden_gleich`); narrow store
  posts `trunc .b32`. Width admission is silicon+readiness
  (`breiteZugelassen` over accepted `HwProfil`/`BereitProfil`), with both
  projection lemmas used at every UC gate.
- Memory access/order: UC membership by explicit software region list
  (`istUc`/`decktUc`, WB default, `istUc_leer/kopf/mem`); every UC step
  re-checks membership + `imFenster` + width admission — no trusted
  `osMemoryOk` Bool. CPU-retired UC stores POST (`ausstehend`), never
  WB-buffered, never device-applied (`ucStore_bypass` proves pending,
  device, counter, CPU unchanged; log/posted grow by exactly one).
  FIFO `busFortschritt` alone completes; overlapping UC loads refuse
  (`ucLoad_verweigert_bei_ausstehend`, no silent forwarding). UC-UC order
  is the event log; pending WB stores preserved by every UC and bus step
  (stale `[9000]:=7` entry seeds the witness and survives,
  `wit_pending_erhalten`). No universal fence claimed.
- Posted vs completed: `wit_s1_geraet_noch_null` (retired, device still 0)
  vs `wit_bus_geraet` (device 42 after bus) proves the distinction is
  observable, not definitional.
- FP/flags: all seven accepted FP DOUBLE memory rows to UC refuse
  (`fpUcBetroffen`, `mmioByteschritt_fp_uc_verweigert`); GP paths preserve
  flags/XMM/FP control (`ucLoad_rahmen`, `maschineSchrittWeiter_*`). No
  invented x87/SIMD device semantic, no zeroed defined effects.
- No duplicate interpreter: fetch/decode/step/addr/RIP/merge/trunc all
  reused; no import of unmerged lane 676, no edit outside owned files.
  `Grammatik.lean` diff is one additive import line.

## 3. Soundness checks

- Forbidden tokens: grep over the candidate file for
  `sorry|admit|axiom |native_decide|unsafe` returns only English
  "admit/admitted" prose — no Lean misuse. Build evidence shows `sorry`
  only in intermediate failing probes, absent from the final file.
- Premises all used: spot-checked `ucStore_bypass`, `ucLoad_rahmen`,
  `mmio_uc_speichern/laden_fakten` — every hypothesis feeds a rewrite or
  case split; no `intro _`/`have _ :=` discard; no Prop-typed premise;
  conclusions are frame/bypass/selection facts, not restated premises.
- Axioms: file ends with 22 `#print axioms`; claimed `propext` or
  `propext + Quot.sound` — within the standard
  (`propext`, `Classical.choice`, `Quot.sound`) as a subset. No new axiom.
- Witnesses (joint, reached, memory-changing, all `decide`-computed from
  fetched bytes): `wit_joint_zeuge` bundles RAM `8192`: 0 → 42
  (`wit_anfang_ram` + `wit_s3_ram`), device byte 0 → 42 with retired≠
  completed, log `[schreibe, lese]` in program order, RIP 4096 → 4117,
  `rcx = 42`, counter = 2. `ucStore_bypass_zeuge` and
  `busFortschritt_fifo_zeuge` jointly inhabit the two main mechanisms.
  Non-degenerate (tables/profile/pending present, real memory change).
- Negative mutations (8, all `decide`): wrong-kind (empty profile),
  FP-to-UC, past-image, width straddle (65543+2), 64-bit wrap
  (`2^64-4`), missing profile, missing silicon (`⟨false,…⟩`), overlapping
  posted write; plus footprint disjointness `wit_fuss_disjunkt`.
- CUTS: exact, bounded (§6 of file) — selected 8-byte window only;
  WC/WT/WP/NT/DMA absent; fetched 8/16 + 32-bit loads refuse at byte
  path; no liveness/fairness/timing; no interrupt/LOCK/fence beyond
  bypass/preservation; no UC code-fetch gating; device richer semantics
  refine the counter interface; no source/checker/goal/emitter
  correspondence; AMD absent. Matches the task's "missing essential MMIO
  keeps milestone OPEN".

## 4. Manual provenance (checked locally)

- "Chipsets may post UC writes / processor never buffers I/O writes /
  strict ordering enforced by processor": VERIFIED verbatim near
  `may post` (Vol.1 p.20-5, ORDERING I/O). Minor imprecision: author
  cites §20.5; the passage sits under §20.6 (20.5 is Protected-Mode I/O).
  Substance correct; suggest fixing the section number at integration.
- Table 14-2 UC ("appear on the bus in program order without reordering;
  no speculative accesses") + x87/SIMD NOTE ("implementation dependent;
  use GP-register loads/stores for UC with side effects"): VERIFIED
  verbatim at Vol.3A §14.3. Only GP forms admitted to UC — faithful.
- §14.3.3 code-fetch limits noted, fetch gating left OPEN — as claimed.
- §§11.1.2/11.2.5 lock serialization with no universal fence — consistent
  with the file claiming no fence; not independently page-verified here,
  but nothing in the file contradicts it.

## 5. Bounded acceptance and residual scope

ACCEPT covers: selected UC-vs-WB over the explicit 8-byte window at
65536, posted/FIFO/ordering discipline, fetched pilot-64 + narrow-32
device paths with FP-to-UC refusal, joint reached witness, planted
refusals, standard axioms. It does NOT close: fetched 8/16-bit and
32-bit-load byte paths, WC/WT/WP/NT/DMA, completion liveness/timing,
interrupts/LOCK/fences, UC code-fetch gating, richer device semantics,
or any source/checker/goal/emitter correspondence. The author's
"fetched 8/16/32/64" limitation rationale (no accepted decoder rows;
inventing decoders would collide with codec lanes) is the correct
reading, and the refusal is explicit, so this is bounded ACCEPT rather
than REPAIR. Minimal correction at integration: `Vol.1 §20.5` → `§20.6`
in the header comment (provenance only, no semantic effect).

## 6. Reproduction

No source edits were made or needed (report-only lane). Verification was
read-only: full file reads, base-definition greps, manual text searches,
PATCH/snapshot inspection. Queued build wrappers were not re-run because
the candidate module is absent from this clone's `grammatik/` by design
(it lives under `.tmp/review/author-694/`); the author's
`BUILD-EVIDENCE.json` records the final green `lean-probe` (0 errors) and
`lean-bau` (467 jobs) plus axiom prints. No red build, no bypass, no
guarantee weakening, no desired-correctness premise found.

Report-only exact review as recorded in the header lines above.
No unsupported desired-correctness premises, no weakened guarantees,
no fake closure. Acceptance is bounded as stated in section 5.
