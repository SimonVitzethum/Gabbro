# MUSE-REPORT-996: Exact review of author 846 (Composition closing: patch-bytes closing)

CANDIDATE: 846 e050fd5a773f4bf58538d38f4731e4fee17c0e5c

VERDICT: ACCEPT (bounded: whole-region patch-to-redecode closing over all
three `RelocArt` classes, jump field-level displacement agreement,
permission-carrying execution leg, planted overrun/forged-opcode refusals;
`valX86` closing, call/conditional field agreement, TSO/GX bridge, source
correspondence remain OPEN as the file states).

## What was done

Report-only exact review of the pinned snapshot
(`.tmp/review/SNAPSHOT.json`, base `e7c75908`, files `MUSE-REPORT-846.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/ComposePatchBytes.lean`,
recorded clean). Independently inspected the owner task, the complete PATCH
(489 lines, exactly 3 files), the full new Lean file (384 lines), the
candidate's build-evidence trajectory (12 recorded wrapper runs, red to
green), and every reused producer/consumer definition and lemma in-tree:
`Relokation.patchAt`/`patchRel32`/`patchAt_bereich`/`patchAt_stelle`/
`patchAt_rahmen`/`patchRel32_stelle`/`rel32Bytes_laenge`,
`BranchLayout.rel32Bytes_dispSigned`/`dispSigned`,
`RelocatedExecution.relocBytes`/`relocBefehl`/`relocLen`/`relocBytes_len`/
`relocBytes_decode`/`dispVonFit`/`ruf_schritt_zeuge`,
`DecodingCoverage.decode_abdeckung`/`decode_fenster_kongruenz`,
`Byteschritt.kanonisch_schritt_ueberein`/`byteschritt`/`ohne_exec_verweigert`/
`opcode_geaendert_verweigert`/`sprungziel_folgt_byte`/`sprungStart`/
`ohneExecStart`/`ketteStart`/`ketteStartFalsch`/`zustandRuf`. All 16 reused
names exist in this clone with signatures matching the candidate's usage.

## Architecture findings (checked, not just Lean-green)

- Byte forms correct: opcode 233 is `0xE9` (JMP rel32), 5-byte jump/call and
  6-byte conditional lengths, rel32 fit window `-2147483648 <= disp <
  2147483648`. Target arithmetic in the witness pair is exact RIP-relative
  semantics: 4096 + 5 + 16 = 4117, displacement 17 gives 4118.
- `relocBytes a d` is definitionally `encode (relocBefehl a d)`
  (`RelocatedExecution.lean` line 57-58), so the execution leg's application
  of `kanonisch_schritt_ueberein` and the `relocBytes_len`-typed length fact
  need no hidden coercion: the patched bytes ARE the canonical encoding.
- The exact-region re-decode conjunct is genuinely derived: window
  congruence (`take ++ rest = whole`) plus the taken-region equality rewrites
  the goal back to the admitted decode hypothesis. No decoder internals are
  unfolded anywhere; displacement agreement goes through decoder-as-function
  determinism (`Option.some_inj` on syntactically identical inputs) plus the
  accepted byte bridge `rel32Bytes_dispSigned`. No invented determinism.
- Sound abstraction directions throughout: overrun patches to `none` (never
  wrapped), forged opcode decodes to `none`, readable-but-not-executable
  refuses, mutated byte refuses while intact bytes step. No success is
  invented for undefined hardware state.
- No guarantee weakened: the PATCH touches nothing except the report, one
  appended import line in `Grammatik.lean`, and the new file. No existing
  theorem edited, no refusal lifted, no diagnostic/gift/example/CLI numbers,
  no MARKE changes, no source/checker/Spec/emitter edits, no friend-reserved
  files.
- No desired-simulation assumption: the execution leg's admitted `schritt`
  outcome is an explicit universal premise (the task-sanctioned "arbitrary
  admitted inputs" shape), and the producer premise stays load-bearing
  through the region equality and the patch-range conjunct. The witness
  grounds execution with real byte runs rather than the leg's conclusion.
- Premise use traced for all three main theorems: every premise feeds its
  proof; conclusions (region equality, length equation, exact re-decode,
  range, site, frame, coverage, displacement identity, fit, opcode survival)
  are derived, never premise restatements. No `Prop`-typed premises.
- Witness is non-degenerate and joint: concrete 5-byte jump image patched
  `E9 00 00 00 00` to displacement +16 with both closing premises decided by
  `decide`; region/agreement/length facts derived THROUGH the closing
  theorems; a reached memory-changing call run (`ruf_schritt_zeuge`: return
  address `0x1005` stored at `0x1FF8`, read back, observed byte change);
  patch/decode/permission/execution refusals plus the byte-moves-target
  pair. A memory-changing run through a jump patch itself is impossible by
  hardware semantics (jumps write no memory); the call run is the correct
  non-degeneracy analog at this layer, and the author says so plainly.
- Final axiom sets are standard subsets: `patchRel32_passt` none,
  `ComposePatchBytes_verbindung`/`_feld_verbindung` propext + Quot.sound,
  `_schritt`/`_zeuge` propext + Classical.choice + Quot.sound,
  overrun refusal none, forged-opcode refusal propext only. `gabbro_ziel`
  intact per the recorded `BeweisAtomar` probe.

## Reproduction note (honest boundary)

The candidate file is not in this review tree and the task forbids touching
source, so no wrapper re-execution of the candidate was possible here.
Verification was: full proof-script audit against the real in-tree
producer/consumer signatures (all shapes match, including the subtle
`decode_fenster_kongruenz` window-congruence use), plus inspection of the
candidate's recorded wrapper trajectory, which shows genuine red-to-green
repair rounds (unknown-identifier, rewrite-pattern, omega-counterexample and
pair-notation errors, each fixed) ending in `./lean-probe` 0 errors, full
`./lean-bau` green (509 jobs), and clean `git status` with only the 3 owned
files. No `./lean-bau` was run in this review lane; there was nothing owned
to build.

## Bounded acceptance and non-blocking observations

1. `ComposePatchBytes_schritt` has no dedicated packaged joint witness; its
   premises are satisfiable (region fact from the witnessed closing,
   `sprungStart`-shaped fetched windows with execute permission, `schritt`
   admittance implied by the stepping byte runs) but are not combined into
   one theorem. Strengthening suggestion, not a repair: the required ZEUGE
   (`ComposePatchBytes_verbindung` + `_zeuge`) exists and is joint.
2. Field-level agreement covers the jump class only; call/conditional legs
   are explicit CUTS using the same determinism pattern. Within the claimed
   boundary.
3. The author's report is accurate: claim matches proof, CUTS list the real
   boundary (`valX86`, call/conditional fields, TSO/GX, source
   correspondence, contracts, cost/time), and the two friction notes
   (witness-name collision, pair notation) are factual.

## Task feedback

Nothing in the review task was wrong. The pinned snapshot plus the
exact-candidate directory made this review fully self-contained.
