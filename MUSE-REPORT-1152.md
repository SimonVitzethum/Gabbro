# MUSE-REPORT-1152: exact review of candidate 1151 (system forms)

## VERDICT: ACCEPT

CANDIDATE: 1151, pinned HEAD `6b0a4e10da43c4ef9d22fba6dd3fd3c146508a9a`
(base `062b979a6271b7b3044ab06be3f3cde411a0d4f1`, snapshot `clean: true`).
Reviewed from `.tmp/review/author-1151/` (PATCH.diff + snapshot file copy);
no other source was read for the verdict. Identity verified first:
clone `/home/simon/Dokumente/gabbro-muse/a1152`, branch `muse/1152`.

## What was checked

Scope: exactly 3 files (`MUSE-REPORT-1151.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwSystemForms.lean`,
1401 lines). The `Grammatik.lean` diff is one appended line,
`import Grammatik.X86.HwSystemForms`; no other existing file is touched.

- Banned patterns: no `sorry`, `admit`, `axiom` declaration,
  `native_decide`, `unsafe`, `split_ifs`, `norm_num`, `ring_nf`,
  `intro _`, `have _ :=` in the new file (only comment words
  "admitted/admits" and `#print axioms` lines match). No premise has
  type `Prop` itself (the one `: Prop` hit is the `SysWf` def result).
- Axioms: all 18 `#print axioms` outputs are within
  `propext, Classical.choice, Quot.sound` (most use a subset).
- Lift, not copy: accepted `pruefeTor`, `waehleStapel`,
  `schiebeRahmen`, `rahmenWorte`, `liesTorBytes`, `torAdresse`,
  `witMem`, `basisHw`, `basisBereit`, TSO `issueByte`/`loadByte`/
  `flushKern` are called, never redefined (no `def` of any accepted
  name; all new names are `Sys`/`sys`-prefixed).
- Premise use: every hypothesis is consumed by its proof
  (spot-checked `schrittSysret_ok` uses `hk`, `schrittHlt_gp`/
  `schrittIf_gp` use `h` in `simp`); no discarded premises.
- Refusals really refuse: six closed `decide` observations
  (`sysWit_ud_frei`, `sysWit_gp_hlt`, `sysWit_gp_cli`,
  `sysWit_gp_rdtsc`, `sysWit_gp_int3`, `sysWit_gp_sysret`) are
  machine-checked — none would compile if the leg admitted.
- Witness non-degenerate: two cores deliver INT 2 (frame bytes in
  shared memory observed: `sysWit_int_frame_rsp/rip`), core 1 then
  HLT-halts; TSO stage shows owner-only forwarding
  (`sysWit_weiterleitung`/`sysWit_fremd_alt`) and a drain that changes
  actual shared memory 0 -> 42
  (`sysWit_spuelung_aendert_speicher`); all joined in `sysWit_zeuge`.
- Silicon vs Intel SDM 093 extracts (clone-local): HLT privileged /
  CPL 0 / saved IP past the form / per-core halt; SYSCALL
  RCX:=next-RIP, RIP:=LSTAR, R11:=RFLAGS, FMASK mask, CPL:=0, #UD
  unless 64-bit+SCE; SYSRET `RFLAGS := (R11 & 3C7FD7H) | 2` with
  #UD/#GP(0)/canonical-RCX classes — all match, including the mask
  constant. Serialisation stays a named assumption (S-SERIAL-*) with
  proved buffer equations; no drain is claimed. CUTS is honest and
  claims nothing beyond self-consistency (no W/GX bridge, no hardware
  correspondence, #NP/#TS folded to #GP disclosed, IRET five-word
  frame disclosed, 64-bit non-FRED only disclosed).

## Verification runs (this lane)

- `./lean-probe .tmp/review/author-1151/grammatik/Grammatik/X86/HwSystemForms.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
  (18 axiom lines, all standard; matches BUILD-EVIDENCE.json).
- `./lean-bau` on the reviewer clone (candidate not applied; base check):
  `Build completed successfully (610 jobs).`
  (610 vs the author's 608: the base moved forward since the
  candidate base; the candidate adds only one file plus one import.)

## What remains open

Nothing for this review. The author's two task notes are accurate
(`HwRegAusgang` superseded in-tree; the TSO stage is honestly labeled
witness scaffolding, not a family effect) and need no action.

## Task correctness note

The lane task's `CANDIDATE: 1151 <full pinned HEAD>` placeholder
carries no hash; the hash above comes from
`.tmp/review/SNAPSHOT.json`. Everything else in the task is correct.
