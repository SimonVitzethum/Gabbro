# MUSE-REPORT-1316: Exact review of candidate 1315 (IntMemForms)

CANDIDATE: 1315 bae01144de14240e742b57518bc336730b304297
VERDICT: ACCEPT

Pinned HEAD is the hash on the machine-readable line above
(base `f92c2649c25c822f0ff7791f82dfecad9c7d4c31`).
Scope: NEW `grammatik/Grammatik/X86/IntMemForms.lean` (1996 lines),
one `import Grammatik.X86.IntMemForms` line in `grammatik/Grammatik.lean`,
`MUSE-REPORT-1315.md`. PATCH.diff contains exactly these three files.

## Identity and method

- Clone `/home/simon/Dokumente/gabbro-muse/a1316`, branch `muse/1316`,
  tree clean before and after (this report is the only owned file).
- Never touched the author clone or pinned hash; reviewed only the
  delivered FILES under `.tmp/review/author-1315/` plus OWNER-TASK.md,
  BUILD-EVIDENCE.json, SNAPSHOT.json.
- Read the candidate file end to end (all 1996 lines). Shell file
  operations (`cp`) are blocked in this lane, so instead of copying I
  ran `./lean-probe` directly on the delivered path
  `.tmp/review/author-1315/grammatik/Grammatik/X86/IntMemForms.lean`
  (`lake env lean` resolves imports via LEAN_PATH, so this elaborates
  the full file against my clone's newer master `f49f7549`).

## Findings per review dimension

- Banned tokens: none in code. `grep` for
  `sorry|admit|axiom|native_decide|unsafe|sorryAx` finds only the
  English word "admit" inside two comments ("only admit the pilot
  shape"); `pruefe-kein-sorry.py` strips comments before matching, so
  the merge gate is unaffected. No `Prop`-typed premises; every
  premise of the spot-checked theorems is used (`hwf` via `exact hwf`,
  step hypotheses via `rfl`-closure or `simp`).
- Axioms: all 36 `#print axioms` lines standard. Live probe output:
  value/event/adapter/witness theorems depend on `[propext,
  Quot.sound]`, pure codec round trips and LOCK refusals on `[propext]`
  only. Subset of the allowed set.
- Existing files: PATCH confirms Grammatik.lean gains exactly one
  import line; nothing else touched.
- Lift, not copy: `rotVollNeu` applies `rolB`/`rorB`/`rclB`/`rcrB`
  (per-arm agreement theorems plus `rotVollFlags_gueltig` reusing
  `rotFlags_gueltig`); `carryVollNeu` applies the accepted
  `adc/sbb/inc/dec` Wert/Flags layer (`rfl` agreements, CF
  preservation for INC/DEC); `signVollNeu` IS `extendNarrow .sign`
  (= `sext`); `xchgVollNeuReg` IS the `mergeRegNarrow` install (full
  word at 64 bits). Addressing via accepted `adrEff`/`adrOk`/
  `encodeAdr`/`parseAdrTail`/`rexFuer`; TSO events via accepted
  `concLoad`/`concIssue` with exact `entriesOf` footprints
  (`rotVollSchritt_puffer`, `carryVollSchritt_puffer`,
  `xchgVollSchritt_puffer`), canonical memory untouched, RIP
  advanced, `HwWf` preserved.
- Refusals that really refuse (all closed `rfl`/`decide`/`simp`):
  bad length for all four families, refused load gate, 64-bit sign
  source at encode (`signVollOk_verweigert_b64`), decode
  (`decodeSignVoll_b64_verweigert`) and step level, `rsp`-as-index
  and `rbp`-without-displacement for every family, LOCK prefix on all
  four tags (`decode*_lock_verweigert`, any suffix by case split).
- Witness non-degeneracy: two cores; SIB INC then SIB ROL on core 0
  with owner-only forwarding (`intMemWit_e1/f1`, `e2/f2`) and two
  observable drains (byte 0->1->2 at 8200); core-1 RIP-relative XCHG
  (7 for 2, drained to 7) plus sign load back (`rax=7`).
  `intMemWit_zeuge` jointly proves 23 conjuncts: both effective
  addresses, admission, zeroed start, buffer/RIP observations,
  forwarding pairs, all three drains, register installs, adapter
  agreement (`intMemWit_adapter_m1`), LOCK refusal, SIB refusal,
  `HwWf`. Memory-changing, two-core, non-degenerate.
- Silicon (checked against `.tmp/HARDWARE-REFERENCES/` SDM text):
  LOCK = F0H = 240 confirmed (SDM 2.3, lines 33314/33349); the
  refusal byte 240 is correct. REX/admission/legality delegated to
  the accepted modules; value-layer silicon assumptions explicitly
  inherited, not re-litigated. Tags 113-116 are NEW canonical bytes
  read by no accepted decoder (nothing shadowed); the file and CUTS
  claim self-consistency only. No hardware-correspondence claim, no
  W/GX claim, no atomicity claim for XCHG. Honest.
- CUTS block present and complete; `#print axioms` per main theorem
  present (36 prints). No claim larger than the proof.

## Verification evidence (mine, not the author's)

- `./lean-probe .tmp/review/author-1315/grammatik/Grammatik/X86/IntMemForms.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`, all 36 axiom
  prints standard. Note: this ran against a NEWER master than the
  candidate base (merges 1197/1198) and still passes unchanged.
- `./lean-bau` (baseline tree, candidate not copied in):
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (692 jobs).`
- Full `lean-bau` WITH the candidate was not run here (shell copy
  into `grammatik/` blocked); the probe fully elaborates every proof
  in the file, and the author's BUILD-EVIDENCE records the green
  688-job build with the one-line import. The serial merge build
  re-verifies integration anyway.

## Minor observation (not verdict-relevant)

- Section headers are misordered: `## 8. Reached witness` (line 1440)
  precedes `## 7. The adapter plug` (line 1683). Cosmetic only; the
  CUTS block and report describe the sections correctly.

## Task feedback

Nothing in the owner task or lane task was wrong. One apparatus note:
`cp` and compound shell file commands were permission-blocked in this
lane, but `./lean-probe <delivered-path>` elaborates the candidate
in place via LEAN_PATH, which proved sufficient for independent
verification (0 errors, full axiom output).
