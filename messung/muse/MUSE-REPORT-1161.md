# MUSE-REPORT-1161: Pipeline: IEEE float expressions

Lane 1161, clone `/home/simon/Dokumente/gabbro-muse/a1161`, branch `muse/1161`.
Owned files only: `grammatik/Grammatik/X86/PipelineFloat.lean`,
`grammatik/Grammatik.lean` (one import line), this report.

## What was built

NEW FILE `grammatik/Grammatik/X86/PipelineFloat.lean` (~460 lines) plus
`import Grammatik.X86.PipelineFloat` in `grammatik/Grammatik.lean`.
It lowers source f64 expressions to the accepted scalar SSE2 forms and
proves the source IEEE model equals the target result bit for bit under
the MXCSR control-state premise. No existing file was otherwise touched;
no second source interpreter, no new IEEE model, no optimiser edit.

Definitions: `senkGleitOp` (one source op = one `*sdRR` machine op),
`senkGleitCmp`/`FloatCmp` (both comparisons to `ucomisdRR`),
`senkGleitVon`/`senkGleitNach` (accepted 64-bit conversions only),
`senkGleitLit` (correctly rounded literal word), `laufFp` (decoded-list
runner) with `laufFp_nil`/`laufFp_cons`, `floatPipeOk` (MXCSR + length
admission), `konvBreiteOk` (64-bit-only width check).

Theorems: `floatPipeOk_reset/profil_verweigert/laenge_verweigert`,
`pipelineFloat_seq` (main correctness: the `movsd`+op run reaches a
successor holding `muster64 (gleitRechne …)` in `dst`, RIP past both
forms, control word/memory/registers preserved),
`pipelineFloat_cmp_schritt/ungeordnet/lt/le`,
`pipelineFloat_von/nach` (links to `gleitAusInt`/`gleitRoh`),
`pipelineFloat_lit_rund`, `konvBreiteOk_64/32/nur64`,
`pipelineFloat_refuses_profil/laenge/validator/lade`,
poison probes `pipelineFloat_probe_profil/laenge`,
`pipelineFloat_nullzeichen` (`+0 + -0 = +0` at source level),
`pipelineFloat_konv_zeuge` (`42.0` pattern),
`pipelineFloat_zeuge` (joint non-degenerate witness: lowered divide
computes `1.0/+0.0`, stored `+inf` reads back, one byte changed).

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineFloat.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (608 jobs).`
- `#print axioms`: at most `[propext, Quot.sound]` (subset of the
  `gabbro_ziel` standard); several witnesses depend on nothing.
- No `sorry/admit/axiom/native_decide/unsafe`; every premise is used.

## Open (see CUTS in the file)

No loaded image / byte fetch / relocation (`laufFp` runs constructed
decodings); no TSO bridge; no f32 lowering (`Ty.fl` is widthless
binary64, so genuine binary32 has no source semantics here); NaN
agreement is class-level only; no reassociation/contraction/fast-math.

## Notes on the task

Two findings, both handled, no weakening: (1) multi-line
`{ s with … }` record literals fail to parse in this file while the
identical single-line form works (observed twice, deterministic) — all
records are single-line; (2) eager `rfl` components elaborate before
deferred `by simp` blocks assign the existential witness, misassigning
it — the run equation is pinned in a standalone `have` first. The task
asks for byte-level runs on the loaded image "in the style of
`pipeline_correct_entry`"; the delivered form is the
`pipeline_correct`-style existential over constructed decodings, with
the byte/image connection honestly listed as OPEN rather than claimed.

Commits: skeleton `9dbe720e`, seq `ed86dc44`, comparisons `72efe6ad`,
conversions `706d413e`, refusals/witnesses `134060aa`.
