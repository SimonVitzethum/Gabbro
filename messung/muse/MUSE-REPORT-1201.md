# MUSE-REPORT-1201: Pipeline float — NaN payload and bit-exact agreement

## What was done

NEW FILE `grammatik/Grammatik/X86/PipelineFloatNaN.lean` (617 lines) plus one
`import Grammatik.X86.PipelineFloatNaN` line appended to `grammatik/Grammatik.lean`.
Follow-up of lane 1161 (`PipelineFloat.lean`): NaN agreement there was class-level
only (`fpRechne_klasse`); this file proves BIT-EXACT agreement of the source IEEE
result (`gleitRechne`) and the SSE2 result (`fpRechne`) INCLUDING NaN payload
propagation, as the accepted codecs define it. No existing file was touched
(except the import line); `OptimizationRules.lean`/`OptimizationWitnesses.lean`
untouched; no new IEEE model, no second interpreter, no optimiser change.

- §1 Model propagation (verbatim, first NaN wins): `nanAdd_links/_rechts`,
  `nanMul_links/_rechts`, `nanDiv_links/_rechts`, `nanSub_links/_rechts`,
  `nanNeg_nutzlast`. Left-NaN proofs are `unfold + rw` only (the match resolves
  without inspecting the second operand); right-NaN needs the 5-way class split
  with the `≠ .nan` premise used in the `.nan` branch.
- §2 Word-level bit-exact: `fpRechne_nan_links` (all four ops return the left
  word), `fpRechne_add/mul/div_nan_rechts` (right word verbatim),
  `fpRechne_sub_nan_rechts` (`muster64 (neg …)`, sign flip only).
- §3 Quiet/signalling AS THE CODECS DEFINE IT — i.e. no distinction:
  `nanStill` (bit 51) plus decides that quiet and signalling-like words share
  one `.nan` class, propagate verbatim (`nanNutzlast_quiet_add`,
  `nanNutzlast_signalisierend_add`, `nanNutzlast_rechts_mul`) and take the same
  UCOMISD unordered row (`nanUcomi_signalisierend`).
- §4 Named hardware assumption `HwZweiNanWahl` (two-NaN silicon answer is one
  of the two input words), stated and USED by `silizium_zweiNan_bleibtNan`,
  never proved.
- §5 Pipeline: new lowering `senkNanSeq` (two-step, reuses `senkGleitOp`),
  validator `nanPipeOk` (reuses `floatPipeOk`) with `nanPipeOk_zulaessig`,
  `pipelineNaN_seq` (source word bit for bit, via `pipelineFloat_seq`),
  `pipelineNaN_nutzlast_links` (all ops) and `_rechts_add`.
- §6 Refusals `pipelineNaN_refuses_profil/_laenge` + poison probes for both
  (`pipelineNaN_probe_profil/_laenge`).
- §7 Joint witness `pipelineNaN_zeuge` over `nanZeugeT` (payload NaN in `xmm0`,
  `1.0` in `xmm1`, `rax` at 8192): lowered add sequence lands the payload word,
  store writes it at 8192, reads back, one observably changed byte
  (`nanZeuge_liest`, `nanZeuge_speicher_aendert`, both `decide`/`rfl`-closed).

## Exact new names

Defs: `senkNanSeq`, `nanPipeOk`, `nanStill`, `HwZweiNanWahl`, `nanZeugeXmm`,
`nanZeugeT`, `nanZeugeSpeicherNach`.
Theorems: `nanPipeOk_reset`, `nanAdd_links`, `nanAdd_rechts`, `nanMul_links`,
`nanMul_rechts`, `nanDiv_links`, `nanDiv_rechts`, `nanSub_links`,
`nanSub_rechts`, `nanNeg_nutzlast`, `fpRechne_nan_links`,
`fpRechne_add_nan_rechts`, `fpRechne_mul_nan_rechts`,
`fpRechne_div_nan_rechts`, `fpRechne_sub_nan_rechts`, `nanStill_quiet`,
`nanStill_signalisierend`, `nanKlasse_quiet`, `nanKlasse_signalisierend`,
`nanKlasse_nutzlast2`, `nanKlasse_eins`, `nanNutzlast_quiet_add`,
`nanNutzlast_signalisierend_add`, `nanNutzlast_rechts_mul`,
`nanUcomi_signalisierend`, `silizium_zweiNan_bleibtNan`,
`senkNanSeq_klingt`, `nanPipeOk_zulaessig`, `pipelineNaN_seq`,
`pipelineNaN_nutzlast_links`, `pipelineNaN_nutzlast_rechts_add`,
`pipelineNaN_refuses_profil`, `pipelineNaN_refuses_laenge`,
`pipelineNaN_probe_profil`, `pipelineNaN_probe_laenge`, `nanZeuge_tief0`,
`nanZeuge_tief1`, `nanZeuge_fp`, `nanZeuge_liest`,
`nanZeuge_speicher_aendert`, `pipelineNaN_zeuge`.

## Last `./lean-bau` result

`== exit 0; 0 error line(s) in the COMPLETE output` —
`Build completed successfully (627 jobs)`, whole `grammatik/` green.
`./lean-probe` on the new file: 0 errors. All `#print axioms` are subsets of
`[propext, Quot.sound]` (several depend on no axioms at all). No `sorry`,
`admit`, `axiom`, `native_decide`, `unsafe` (grepped).

Note: two `./lean-bau` runs before the final one failed while READING
toolchain Std oleans (`ExtTreeMap/Lemmas.olean`, then
`DTreeMap/Internal/Balancing.olean.private` — a different file each run,
both present and readable). Third run, no code change: fully green.
Apparatus flake under load, not a code issue.

## What remains open (see CUTS in the file)

No loaded-image/byte-fetch/relocation claim; no TSO/concurrency; no f32;
silicon SNaN quieting unmodelled and unclaimed; pipeline right-side payload
proved for `add` (word level covers the rest); `sub`-right has no bare-word
equation. Rule 13: no theorem quantifies over the listed source-syntax types;
`pipelineNaN_zeuge` is the non-degenerate memory-changing witness.

## Task remarks (nothing believed wrong)

Two readings had to be fixed to stay honest, both recorded in CUTS: (1) the
"quiet/signalling behaviour as the codecs define them" is the ABSENCE of a
discipline (single `.nan` class) — inventing SNaN/QNaN forms would contradict
the accepted model; (2) the "operand-order choice for two NaN operands" exists
only in silicon (the model is deterministic, first wins), so the named
assumption ranges over an abstract silicon function, not over the model.
Bit-exactness proved is source-model ↔ SSE2-model (same function both sides).
