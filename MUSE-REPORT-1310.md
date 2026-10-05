# MUSE-REPORT-1310: Exact review of lane 1309 (page-fault delivery)

Lane 1310, clone `/home/simon/Dokumente/gabbro-muse/a1310`, branch `muse/1310`
(verified: `pwd` + `git branch --show-current`; `git status --short` clean
before writing this report).

CANDIDATE: 1309, pinned HEAD `6954375bb72b1d4bf81a72e105adb07988324ecc`
(from `.tmp/review/SNAPSHOT.json`; base `234f2728a718157cba0e1f9e0ef300874b34ea6a`).
Changed files per SNAPSHOT: `MUSE-REPORT-1309.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwPageFaultDelivery.lean`.
The author clone and the pinned hash were NOT read (HARD RULE 1): all checks
ran against the delivered FILES under `.tmp/review/author-1309/`
(`PATCH.diff`, the copied tree, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`).
No `git show/log/diff` on the pinned hash was used.

## VERDICT: ACCEPT

## What was checked

- Forbidden patterns: grepped the candidate file for
  `\bsorry\b|\bnative_decide\b|\bunsafe\b|^axiom |\badmit\b` — no matches
  (the only `admit`-substring hits are English words "admitted"/"unadmitted").
  Grepped for `intro _`, `have _ :=`, `forall rho`, `Prop`-typed premises,
  `split_ifs`, `norm_num`, `ring_nf` — no matches.
- `#print axioms` standard: `./lean-probe` on the delivered file ends
  `== 0 error(s) in the COMPLETE output; exit 0`, and the tail shows every
  theorem at `propext` + `Quot.sound` at most, several axiom-free
  (`pfVektor_vierzehn`, `pfAnfrage_vektor`, `pfAnfrage_code`,
  `pfWit_anfang_null`, `pfWit_hst`, …), `pfLiefer_zeuge` at
  `[propext, Quot.sound]`. No `sorryAx`. Per-theorem `#print axioms`
  lines are present for all 76 named results.
- Existing files untouched except one import line: `PATCH.diff` shows
  exactly one added line in `grammatik/Grammatik.lean`
  (`import Grammatik.X86.HwPageFaultDelivery`), one new file, and the
  author report. No edits to accepted modules.
- Every premise used: spot-checked the proof terms — success lemmas feed
  all hypotheses into `simp [hl, hr, hcur, hp, hs, hk, hpush]`;
  `pfLieferung_erhaelt` destructures every stage; `hwPfSchritt_cr2`
  uses `hst` in the `HwPfSchritt.pf` constructor; `adapterPf_wf` uses
  both `h` and `hwf`; `pfMitDf_doppelt` uses `h`. No discarded premises.
- Evaluator lifted, not copied: no `def` of `liefere`, `asyncMasch`,
  `schiebeRahmen`, `pruefeTor`, `waehleStapel`, `seitenGang`,
  `pfCodeBits`, `dfVektor`/`dfCode` in the new file (grep clean); the
  file imports `HardwareExecution`, `HwPaging`, `HwPreciseFault`,
  `HwNestedInterrupts` and applies `liefere_zugestellt_wechsel/_behalten`,
  `asyncMasch_rip/_rsp_neu/_wf`, `przFehler_*`, `wit_schreibe_ro_pf`,
  `wit_code_ro` unchanged.
- Planted refusals really refuse: eight `pfSchritt_verweigert_*`
  theorems (limit, gate-read, descriptor, stack, canonical x2, frame x2)
  each conclude `= none`, plus `adapterPf_verweigert_limit`; the
  witness instantiates three of them by `decide`
  (`pfWit_limit_verweigert`, `pfWit_tor_verweigert`,
  `pfWit_dunkel_verweigert`) with `#DF` escalation to vector 8 / code 0
  (`pfWit_dunkel_df_vektor/code`), all machine-checked by the green probe.
- Witness non-degenerate: `pfLiefer_zeuge` jointly proves the walk fault
  (address 8192, RO-write code 7), handler entry (RIP 8192, RSP 16336,
  IF cleared, IST switch), CR2 load (`pfWit_relation`: `cr' 0 = 8192`),
  empty buffers on both cores, six-word frame read-backs, an observable
  memory change (`pfWit_aendert_ss`), IF-bypass success, three refusals,
  `#DF` escalation, owner-only forwarding (core 1 sees 42, core 0 sees 0)
  and drain observed from both cores (42), `HwWf`, and the reached
  extended step. Two cores touch memory; two steps change shared-memory
  bytes (frame push + TSO drain). Non-degenerate.
- Silicon facts: S1–S6 are stated as named SDM-provenance assumptions in
  the file header (vector 14; error-code order = accepted `pfCodeBits`;
  interrupt gate clears IF; delivery fault escalates to #DF 8/zero via
  accepted `dfVektor`/`dfCode`; CR2 loads the faulting address; no TSO
  drain). Checks-before-effects ordering; gate bytes read from machine
  memory, never carried; six-word frame (five words + error code).
- CUTS honest, no oversized claim: the CUTS block claims only
  self-consistency of the lifted model — no hardware correspondence, no
  nested #PF, no handler execution, no W/GX bridge, no timing/TLB/
  SMEP-SMAP/large-page/shadow-stack, `gabbro_ziel` untouched.

## Notes on the task (no finding)

- The owner-task phrase "pushes the error code and the interrupt frame
  through the TSO buffer as the interrupt lane models" is implemented as
  the interrupt lane models it: frame pushed to canonical memory, every
  per-core TSO buffer untouched (`pfLieferung_puffer_still`, witness
  buffer lengths zero). Documented in report and CUTS (S6). Honest.
- `asyncSchritt` is not reused for vector 14 because its admission gate
  excludes vector 14; the delivery mirrors its stage order with
  synchronous-exception admission while reusing `asyncMasch`, `liefere`
  and all stage lemmas unchanged. Documented; not a fake closure.

## Last `./lean-bau` result line

`Build completed successfully (677 jobs).` — green on this clone.
`./lean-probe .tmp/review/author-1309/grammatik/Grammatik/X86/HwPageFaultDelivery.lean`
ends `== 0 error(s) in the COMPLETE output; exit 0` (head and tail runs;
the probe ran against the delivered copy in place — `lean-probe`
resolves any absolute path via `lake env lean`, so no repo copy was
needed and this clone's tree holds only this report).

## What remains open

Nothing for this review. The candidate's own CUTS list (no hardware
correspondence, no nested #PF, no handler execution, no W/GX, no
timing/TLB/SMEP-SMAP/large-page/shadow-stack) is accepted as the
boundary of the claim.
