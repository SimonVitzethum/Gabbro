# MUSE-REPORT-166: kernel-computable IEEE-754 model (floats)

Branch `muse/166`. All work committed here; `./lean-bau` green.

## What was built

A replacement for the `Float`-opaque float model (`Semantik.lean`
`gleitRechne`/`gleitPasst`), WITHOUT switching the model yet (as tasked).
New file `grammatik/Grammatik/Gleitkomma.lean` (+ `import Grammatik.
Gleitkomma` in `grammatik/Grammatik.lean`), new script
`instrumente/pruefe-gleitkomma.py`, new design section
`dokumente/GLEITKOMMA.md`.

Definitions (`Gabbro.Grammatik.Gleitkomma`): `Format` (`p`, `emax`),
`f32`/`f64`, `Format.emin/bias/bexpMax/fracBits/ebits`, `GBits`
(sign/bexp/frac), `Klasse`, `klasse`, `wf`, `zuBits`, `Exakt`
(dyadic), `Bruch` (general rational), `wertExakt`, `bitlenAux/bitlen`,
`rundeInt`, `findeExpBei/findeExp`, `normQD/normQ/subQ`,
`rundeBruchKern/rundeBruchBei/rundeBruch`, `exaktBruch/rundeExakt`,
`neg`, `exaktAdd/exaktMul/divBruch`, `nanQ`, `add/sub/mul/div`,
`ofInt/ofRat`, `flt/fle`.

Theorems: `rundeInt_fall/steig/tie/monoton`, `bitlenAux_null/succ/
null_all`, `zweiHoch_succ`, `bitlenAux_obere/untere`,
`bitlen_obere/untere`, `findeExpBei_unten_nonneg`, `findeExp_unten`,
`klasse_null/subnormal/normal_bits`, `rundeBruch_finite`,
`ofInt_bruch`, `ofInt/ofRat_finite`, `exaktBruch_nenner_pos`,
`add/mul/div_finite`, `klasse_neg`, `wertExakt_neg_some`,
`sub_finite`, `divBruch_nenner`, 20 `zeuge_*` witnesses by `decide`.
`#print axioms`: `[propext, Quot.sound]` everywhere (witnesses:
`[propext]`).

Measurements: syntax «F» (SYNTAX.md), emitter lowering (`f32->float`,
`f`-suffix rule, mixed-width refusal, `KOPF_GLEITKOMMA` prelude,
manifest `-ffp-contract=off`), FMA probe + `sonde_mxcsr_rne` +
`sonde_keine_ueberbreite`, corpus `beispiele/` 4x f32 + 33x f64,
`messung/` 40x f32 + 36x f64.

Differential check: 12200 vectors (4 ops x 2 widths x ~1500
random/edge pairs + int conversions), model (`lake env lean --run`)
vs C (`-std=c11 -ffp-contract=off -O2`): 11848 exact, 352 both-NaN,
0 mismatches. The known signed-zero cut (`-0 + -0`: model `+0`, C
`-0`) verified on constructed vectors and classified by the script.

## Last results

* `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s) in the
  COMPLETE output`, `Build completed successfully (155 jobs).`
* `python3 instrumente/pruefe-gleitkomma.py`: `vectors: 12200 exact:
  11848 both-NaN: 352 known-signed-zero: 0 MISMATCH: 0`, exit 0.
  `--selbsttest` passes both directions.
* `pruefe-waechter.py` static table: `ok pruefe-gleitkomma.py`
  (after hardening: FRIST timeouts, LC_ALL, exit-2 setup aborts,
  two-direction Selbsttest). The file sits with 3 pre-existing tools
  in the informational "4 bleiben offen" cut-surface bucket (my
  exit-1 prints the full measurement first; wrapping it in another
  tool's `fahre()` would be gaming the guardian).
* `pruefe-kennungen.py`: ALL PASS. `pruefe-englisch.py`: nothing new.
  `pruefe-praemisse.py` and `cargo`-based guardians cannot run on the
  build server (ssh/`cargo` unavailable); premise use was audited by
  hand instead (two genuinely redundant premises dropped:
  `0 < den`/lower-remainder in `rundeInt_monoton`, `0 < d` in
  `findeExp_unten`).

## Open (see also `CUTS:` in the file)

No assembled "nearest representable float" theorem (integer-level
decision + finite preservation proved); no `findeExp` upper bound;
overflow-boundary/tie-at-half-min-subnormal rest on algorithm +
witnesses + differential test; signed-zero inputs and NaN payloads
are documented cuts; no `flt`/`fle` theorems; no `f16`/80-bit; the
`Float`-model switch is a later task.

## Where I believe the task is wrong

1. "Exact value as a rational (Int numerator, power-of-two exponent)"
   cannot cover division: `1 / 3` is not dyadic, and `1/3` is an
   explicitly demanded witness. The file provides both `Exakt`
   (dyadic, for `add`/`sub`/`mul`/finite values) and `Bruch`
   (general, for `div`/`ofRat`).
2. "Monotonicity of rounding" unqualified would need a rational order
   over the formats; the load-bearing core is same-denominator
   significand monotonicity (`rundeInt_monoton`), proved with the
   minimal premise set (upper remainder normalised only).
3. Process slip: commits `b498def7`/`2b8c6a3b` share one message
   (stale `.commitmsg` reused); contents differ as logged.
