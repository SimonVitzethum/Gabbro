# MUSE-REPORT-1202: Independent exact review of lane 1201

CANDIDATE: 1201 9df936c9b33ea629753c9651547aa5f09cf080fd

Lane 1202 is a report-only exact review. Owned file only:
`MUSE-REPORT-1202.md`. No Lean code written by this lane.
Review basis is the exact pinned snapshot in this clone
(`.tmp/review/SNAPSHOT.json`: author 1201, head `9df936c9`,
base `4ed3590d`, `clean: true`): `MUSE-REPORT-1201.md`,
one import line in `grammatik/Grammatik.lean`, new
`grammatik/Grammatik/X86/PipelineFloatNaN.lean` (617 lines),
plus `OWNER-TASK.md`, `BUILD-EVIDENCE.json` and `PATCH.diff`.
I read the new file end to end, checked the patch scope, the
owner task against the work delivered, every cited family lemma
against this clone, the silicon facts against the Intel SDM
extract, and the build evidence. My own tree is unmodified
(`git diff --stat master..HEAD` empty).

## Checklist findings

- Forbidden tokens: none. Search over the snapshot file for
  `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `split_ifs`, `norm_num`, `ring_nf`, `intro _`, `have _ :=`
  finds only prose ("admitted") and `#print axioms` lines.
  No new axiom declaration. `HwZweiNanWahl` is a `def` of a
  `Prop`-valued predicate over an abstract silicon function,
  stated and used, never proved -- exactly the sanctioned
  named-assumption shape, not an `axiom`.
- Axiom footprint: standard. Per the recorded build evidence the
  `#print axioms` lines are subsets of `[propext, Quot.sound]`
  (decide-closed facts depend on no axioms at all). No
  `Classical.choice` anywhere. Consistent with the family.
- Existing files: `Grammatik.lean` gains exactly one appended
  `import Grammatik.X86.PipelineFloatNaN` line (patch hunk at
  line 627-630); no other existing file touched, no existing
  theorem weakened or deleted, optimiser files untouched.
- Premise use: every premise of every new theorem is consumed.
  Checked the non-obvious cases: `nanAdd_rechts` uses `ha`
  via `absurd hka ha` in the `.nan` branch; `nanSub_rechts`
  threads `hb` through `klasse_neg`; `silizium_zweiNan_bleibtNan`
  uses `hHw` via `rcases` and both class premises; the
  pipeline corollaries pass `hne`/`hok`/`hfp` into
  `pipelineNaN_seq`. No discarded premise.
- Lifting, not copying: all semantic work delegates to accepted
  family lemmas, each verified present in this clone:
  `Gleitkomma.add/sub/mul/div/neg`, `klasse_neg`
  (`Gleitkomma.lean`), `fpRechne`/`fpRechne_gleitRechne`,
  `muster64_bites64`, `ucomiFlags_ungeordnet_links`,
  `fpSchritt_profil_verweigert`/`fpSchritt_laenge_verweigert`,
  `fpSchritt_movsdSpeichere_erfolg`, `read64_nach_write64`
  (`ScalarFloat.lean`, `Speicher.lean`), `senkGleitOp`,
  `floatPipeOk_reset`, `pipelineFloat_seq`, `fpZeuge_laenge`,
  `fpZeuge_effAddr`, `fpZeugeKern`, `zeugenSpeicher`
  (`PipelineFloat.lean`, `ScalarFloat.lean`), `mxcsr_ftz_verweigert`
  (`Gleitprofil.lean`). New definitions are only `senkNanSeq`,
  `nanPipeOk`, `nanStill`, `HwZweiNanWahl`, `nanZeugeXmm`,
  `nanZeugeT`, `nanZeugeSpeicherNach`. (Nit: the header reuse
  list also names `nanQ`, which never occurs in code -- doc
  only, see remarks.)
- Refusals: `pipelineNaN_refuses_profil` genuinely fires -- the
  probe `pipelineNaN_probe_profil` goes through the theorem
  (FTZ profile `0x9F80` refused under length-ok). For the length
  side see the remark below; a genuine bad-length refusal
  (`divsdRR` with length 16) is proved from the accepted lemma.
- Witness: `pipelineNaN_zeuge` jointly instantiates the lowered
  add sequence on `nanZeugeT` (payload NaN `0x7FF8000000000001`
  in `xmm0`, `1.0` in `xmm1`, `rax` at 8192, admitted profile),
  lands the payload word via `pipelineNaN_seq`, stores it at
  8192 through the accepted store-success lemma, reads it back
  (`nanZeuge_liest`), and shows one observably changed memory
  byte (`nanZeuge_speicher_aendert`, `decide`-closed:
  footprint top byte `0x00` to `0x7F`). Non-degenerate:
  payload word computed by the lowered run, stored, read back,
  memory really changed. No theorem quantifies over the listed
  source-syntax types (`GleitOp`/`FpBefehl` range over model op
  and target form), and the task names no `ZEUGE:` target, so no
  further witness duty applies. Two cores are not relevant: no
  concurrency/TSO claim is made (see CUTS).
- Silicon facts, checked against the Intel SDM extract
  (`.tmp/HARDWARE-REFERENCES`, edition 325462-093US): quiet bit
  is bit 51 (MSB of the binary64 fraction field) -- the
  `0x7FF8...`/`0x7FF4...` test words are correct quiet /
  signalling-like NaNs; both classify NaN since the fraction is
  nonzero. The UCOMISD unordered row for a NaN operand matches
  the accepted `ucomiFlags_ungeordnet_links` equation lifted
  verbatim. The file's characterisation of the accepted codecs
  (single `.nan` class, no quiet-bit discipline) matches
  `ScalarFloat.lean` ("the model has a single `.nan`"). The
  two-NaN silicon choice is a hypothesis, never discharged
  against silicon -- no hardware-correspondence claim is made.
  On SDM Table 4-8 (SSE: first source operand wins, SNaN
  quieted by setting the MSB fraction bit): the bit-exact
  "one of the two input words" hypothesis does not model SNaN
  quieting, which is precisely what the CUTS disclaim ("Silicon
  SNaN quieting ... is NOT modelled and NOT claimed"); the
  silicon-facing theorem concludes only class preservation
  under the named hypothesis. Honest scope, no overclaim.
- Scope honesty: CUTS state plainly what is not proved -- no
  loaded image/byte fetch/relocation (`laufFp` over constructed
  `FpDecodiert`, never decoder bytes), no TSO/concurrency, no
  f32, no SNaN quieting, `sub`-right as sign-flip only, no
  reassociation/fast-math, no sticky flags/costs/timing, and
  that bit-exactness is source-model against SSE2-model (the
  same accepted function both sides, verbatim by construction).
  The report states the same two readings the author had to fix
  (no invented SNaN/QNaN forms; assumption over abstract
  silicon, not the model). The claim is not larger than the
  proof; no W/GX or hardware-correspondence claim.
- Task fidelity: `OWNER-TASK.md` matches the registered lane
  task; the deliverable (lowering `senkNanSeq`, validator
  `nanPipeOk`, `pipelineNaN_seq`-family correctness,
  `pipelineNaN_refuses_*` refusals, probes, joint witness,
  CUTS, `#print axioms`) is exactly what was asked. The
  correctness theorem relates the source model result to the
  lowered run rather than `execBlock`-to-loaded-bytes; the CUTS
  (like parent lane 1161's) say so explicitly instead of
  faking the rung.
- Build evidence: `BUILD-EVIDENCE.json` shows honest per-step
  `./lean-probe` work (several red mid-lane probes with real
  elaboration errors, each repaired) ending in 0 errors, and a
  final whole-`grammatik/` `./lean-bau` with `== exit 0; 0 error
  line(s)`. The pinned HEAD is the report commit on top of that
  green state. The author's note on two transient toolchain
  Std-olean read failures (green retry, no code change) is
  apparatus, not code.

## Remarks (not verdict-blocking)

1. `pipelineNaN_refuses_laenge` has premise `laengeOk 4 = false`,
   uninhabited in practice (`fpZeuge_laenge : laengeOk 4 = true`;
   the sequence hard-codes length 4), so the theorem as stated
   can never fire -- it is true but vacuous, and the length
   probe demonstrates the accepted mechanism on a different
   form (`divsdRR`, length 16) rather than through the
   candidate's own theorem. Visible in the code, not hidden;
   suggested follow-up: note the vacuity in CUTS or thread a
   variable-length first step. The profile refusal is fully
   genuine.
2. Header reuse-list nit: `nanQ` is named but never used.
3. The bit-exact "first NaN wins" order is a property of the
   accepted model proved here; silicon's two-NaN answer is
   first-operand per SDM Table 4-8 (with SNaN quieting),
   which the named assumption deliberately does not encode --
   correctly left as assumption, per the task.

## Outcome

My own `./lean-bau` (baseline tree without the candidate):
`== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (630 jobs).`

VERDICT: ACCEPT
