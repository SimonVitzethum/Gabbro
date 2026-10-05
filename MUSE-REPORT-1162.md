# MUSE-REPORT-1162: Exact review of candidate 1161 (Pipeline: IEEE float expressions)

Lane 1162, clone `/home/simon/Dokumente/gabbro-muse/a1162`, branch `muse/1162`.
Report-only exact review. Owned file: this report only.

## Candidate

- Author lane 1161, pinned HEAD `e1737519eb03c8f2bb1de67b35e31a78b76a2446`
  (matches last commit in BUILD-EVIDENCE.json).
- Files (per `.tmp/review/SNAPSHOT.json`, `clean: true`):
  `MUSE-REPORT-1161.md`, `grammatik/Grammatik.lean` (one appended import line),
  `grammatik/Grammatik/X86/PipelineFloat.lean` (458 lines).
- Reviewed the snapshot `PATCH.diff` and
  `.tmp/review/author-1161/grammatik/Grammatik/X86/PipelineFloat.lean`
  (identical, 458 lines); no access outside this clone was needed.

## Checks performed

1. **No sorry/admit/axiom/native_decide/unsafe**: grepped snapshot code;
   only prose occurrences of "admitted". Pass.
2. **Axioms standard**: build evidence prints every main theorem;
   max `[propext, Quot.sound]`, several axiom-free
   (`konvBreiteOk_nur64`, `pipelineFloat_konv_zeuge`). Subset of the
   `gabbro_ziel` set. Pass.
3. **Existing files untouched except one import line**: diff touches only
   `Grammatik.lean` (`+import Grammatik.X86.PipelineFloat`) plus the new file
   and the author report. No optimiser file touched. Pass.
4. **Every premise used**: read each proof; `hne` feeds
   `xmmSchreibeTief_fremd`, `hok`/`hfp` feed every step lemma, comparison
   hypotheses feed the flag rows, `h` in `konvBreiteOk_nur64` feeds
   `of_decide_eq_true`. No `intro _`, no `have _ :=`, no `forall rho/v`
   weakening. Pass.
5. **Accepted evaluator lifted, not copied**: all machine facts come from
   accepted theorems verified present in this tree (`ScalarFloat.lean`:
   `fpSchritt_movsdRR/addsdRR/subsdRR/mulsdRR/divsdRR/ucomisdRR/cvtsi2sd/
   cvttsd2si`, `fpRechne_gleitRechne`, `ucomiFlags_ungeordnet_links/kleiner/
   gleich`, `cvttPaket_gleicht_gleitRoh`, `cvtsiErg_42`, `fpZeugeT/laenge/fp`,
   `div_eins_durch_null`, `add_plusnull_minusnull`, `fpZeuge_liest/
   speicher_aendert`, `fpSchritt_movsdSpeichere_erfolg`,
   `fpSchritt_movsdLade_verweigert`; `Gleitprofil.lean`:
   `mxcsr_ftz_verweigert`, `bites64_muster64`; `EinpassenVoll.lean`:
   `fle_flt`). The new `laufFp` is a thin `rfl` runner over `fpSchritt`. Pass.
6. **Refusals really refuse**: `pipelineFloat_refuses_profil/laenge/
   validator/lade` derive `none` from the accepted `verweigert` lemmas;
   poison probes are concrete (`0x9F80` FTZ profile, 16-byte form). Pass.
7. **Witness non-degenerate**: `pipelineFloat_zeuge` jointly instantiates
   every premise of `pipelineFloat_seq` (div, xmm0/xmm0/xmm1, witness state,
   `decide` inequality, checked length, admitted profile), computes
   `1.0/+0.0 = +inf`, stores it at 8192, reads it back, and proves one
   observably changed byte. Pass (single-core FP leg; no two-core relevance).
8. **Silicon**: checked against the supplied Intel SDM extract. `Flags`
   order is (cf, pf, af, zf, sf, of); unordered `⟨true, true, some false,
   true, false, false⟩` = ZF,PF,CF=111, OF/SF/AF=0; less-than row = CF
   only. Matches SDM UCOMISD Operation block exactly (UNORDERED 111,
   LESS_THAN 001, EQUAL 100, OF,AF,SF:=0). One-op = one-machine-op, no
   contraction/fast-math. Pass.
9. **CUTS honest, no oversized claim**: no loaded-image/byte-fetch, no TSO,
   no f32, class-level NaN only, no hardware-correspondence or W/GX claim.
   Pass.

## Known deviation (disclosed, not a repair)

The owner task asked for a `pipeline_correct_entry`-style theorem (source
`execBlock` to byte-level run on the loaded image); the candidate delivers a
`pipeline_correct`-style existential over constructed decodings and records
the byte/image connection as OPEN in CUTS and in its report. The gap is
stated plainly, no guarantee is weakened, nothing is claimed beyond the
proof. Follow-up work (byte fetch, relocation, image closing theorem) remains
with the pipeline family, not with this candidate.

## Verification

- Candidate evidence: `./lean-probe .../PipelineFloat.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`;
  `./lean-bau`: `Build completed successfully (608 jobs).`
- Reviewer baseline in this clone: `./lean-bau` ends with
  `Build completed successfully (612 jobs).` (612 vs 608: this base is newer;
  zero errors, green).

CANDIDATE: 1161 e1737519eb03c8f2bb1de67b35e31a78b76a2446

VERDICT: ACCEPT
