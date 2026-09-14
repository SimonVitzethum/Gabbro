# GLEITKOMMA: a kernel-computable IEEE-754 model and its assumption

Lane 166, 2026-09-14. The model lives in
`grammatik/Grammatik/Gleitkomma.lean` (no semantics switch yet -- a later
task does that); the differential check is
`instrumente/pruefe-gleitkomma.py`. English throughout.

## 1. Why a new model

The current model computes floats with Lean's built-in `Float`
(`Semantik.lean`: `gleitRechne`, `gleitPasst`, `bruch`, `Float.ofInt`;
`Syntax.lean`: `Ty.fl`, `GleitOp`, `Block.gleit/gleitLit/gleitVon/
gleitNarrow`, `fllt/flle`). Lean's `Float` is opaque to the kernel:
nothing about float values can be proved and no witness computed without
`native_decide` (forbidden). Gabbro floats are finite and range-carrying
(`finite`, `rounded`, no NaN four-way compare), which is exactly what the
replacement models -- as data.

## 2. What was built

* Formats as data: `Format` (`p` significand bits incl. the hidden one,
  `emax`; `emin = 1 - emax`), `f32 = (24, 127)`, `f64 = (53, 1023)`.
* Values as bit triples: `GBits` (sign `Bool`, biased exponent and
  significand as `Nat`) with the five IEEE cases (`Klasse`:
  null/subnormal/normal/unendlich/nan), `wf`, `zuBits`/`ebits`.
* Exact values: `Exakt` (dyadic: `Int` numerator with a power-of-two
  exponent -- every finite float and every exact `add`/`sub`/`mul`
  result) and `Bruch` (general rational -- division needs it, `1/3` is
  not dyadic), `wertExakt` (none for infinity/NaN).
* Rounding: `rundeBruch` (round-to-nearest-ties-to-even from an exact
  rational) via `findeExp` (exact binary exponent by integer comparison
  around `bitlen`) and the isolated significand decision `rundeInt`.
  Structural/fuel recursion only (`bitlenAux`), no well-founded
  recursion -- it reduces in the kernel.
* Ops as "exact result, then round": `add/sub/mul/div/ofInt/ofRat/neg`,
  `flt/fle` (NaN unordered, infinities by sign, finite by exact
  cross-multiplication, signed zeros equal), with the IEEE special-case
  tables (`inf + -inf`, `0 * inf`, `0 / 0` are NaN; xor signs).
* Theorems: `rundeInt_fall/steig/tie` (the exact RNE decision),
  `rundeInt_monoton` (minimal premises -- the upper remainder
  normalised; brute-force checked that the lower needs no bound),
  `bitlenAux_obere/untere`, `findeExpBei_unten_nonneg/findeExp_unten`,
  `rundeBruch_finite` (in-range exact values round to
  normal/subnormal/null, never inf/NaN), and per-op finite-in-range
  theorems (`add/mul/div/ofInt/ofRat_finite`, `sub` via `neg` with
  `klasse_neg`/`wertExakt_neg_some`). Axioms: `[propext, Quot.sound]`.
* Witnesses by `decide` (20): `0.1 + 0.2 = 0x3FD3333333333334`,
  `1/3` in both widths, `0.1f`, ties both directions
  (`1 + 2^-53 -> 1.0`, `1 + 2^-52 + 2^-53` up), min subnormals both
  widths, subnormal addition, overflow to `+inf`, `0/0` NaN, `1/0` inf,
  `0.2 - 0.1 = 0.1`, `1/3` via `div`. The `2^1074`-scale decides need
  two elaboration-only options (`maxRecDepth`, `exponentiation.
  threshold`) recorded at the witness section.
* Differential check: 12200 vectors (4 ops x 2 widths x ~1500
  random/edge pairs, plus int conversions), model via
  `lake env lean --run` against C compiled with the manifest flags:
  11848 exact, 352 both-NaN, 0 mismatches. One constructed vector
  confirms the documented signed-zero cut (`-0 + -0`: model `+0`,
  hardware `-0`).

## 3. Measured surface (inputs to this design)

* Syntax (`dokumente/SYNTAX.md` "F"): `f32`/`f64` with optional `in`
  range, `rounded` compulsory at inexact literals, `finite` behind
  `narrow`, total comparisons (`fllt`/`flle` -- finite by type, no NaN
  quadrant), `hardware ieee` when a result leaves its range or is not
  finite.
* Corpus: `beispiele/` 4x `f32` + 33x `f64`; `messung/` 40x `f32` +
  36x `f64`. One example file (`26-gleitkomma.gab`).
* Emitter (`crates/gabbro-check/src/emit.rs`): `f32 -> float`,
  `f64 -> double`; per-unit float prelude (`KOPF_GLEITKOMMA`) when a
  unit touches floats; float literals get the `f` suffix exactly when
  the node computes in `float` (else C would lift to `double` and round
  twice -- the Figueroa argument for `(float)0.1 == 0.1f` is recorded
  there); mixed `float`/`double` arithmetic is refused (`CForm
  doubleTyp`); `-ffast-math` forbidden in prose.
* Manifest (`manifest.rs`): two generated float assumptions (below)
  plus the `fp_contract` profile key carrying `-ffp-contract=off`.

## 4. The NAMED ASSUMPTION for the closing theorem

One assumption per machine fact the model reads but never proves.
Proposed names in `manifest.rs` style (the first two exist, the rest
are new):

1. `gleitkomma_rundungsmodus_ist_rne` (exists): every `+ - * /` and
   every conversion computes in round-to-nearest-ties-to-even.
2. `gleitkomma_x86_rechnet_mit_sse2` (exists): on x86, in SSE2, never
   on the x87 stack (which rounds twice).
3. `gleitkomma_keine_kontraktion` (new): no operation fuses with a
   neighbour (FMA/FMAP); each source-level op rounds separately.
4. `gleitkomma_flt_eval_method_null` (new as an entry; the content is
   pinned today, see below): `FLT_EVAL_METHOD == 0`, no excess
   precision on any target.
5. `gleitkomma_kein_fast_math` (new): no reassociation, no
   value-changing optimisation of float code (`-ffast-math` and
   friends off).
6. `gleitkomma_subnormal_erhalten` (new): subnormal inputs and results
   are preserved (no FTZ/DAZ).
7. `gleitkomma_rundungsmodus_stabil` (new, or folded into 1): nobody
   changes MXCSR/FPCR between operations (the mode is process-global
   state; the probe reads it at probe time, not continuously).

Explicitly OUT of the assumption (open by standard or by construction):

* NaN payloads and quiet bits (IEEE leaves them open; the model
  propagates input bits, the hardware need not).
* Signed-zero input combinations beyond what the model computes (the
  documented cut; the closing proof must carry it or exclude it).
* `libm`: the language has no transcendentals (`sin`, `exp`, `pow`
  would each need a correctly-rounded implementation or their own
  named assumption -- PLAN-BITS.md section 5, item 5).
* Decimal literal conversion: C's strtod-style conversion is correctly
  rounded per IEEE, and the emitter's `f`-suffix rule keeps `f32`
  literals single-rounded; the `rounded` word marks exactly the
  literals that are not exactly representable.

## 5. What is pinned today and what is not (measured 2026-09-14)

| # | Fact | Pin today |
|---|---|---|
| 1 | RNE mode | PINNED twice: `sonde_mxcsr_rne` reads MXCSR + x87 control word AND rounds two ties that separate all four IEEE modes, with an arm that sets each violating mode first (600 000/600 000 per SONDENDECKUNG.md, plus `LD_PRELOAD` outside controls) |
| 2 | SSE2, no over-width | PINNED twice: `sonde_keine_ueberbreite` (`(1+2^-53)+2^-53`, x87 positive control, 200 000/200 000) AND `_Static_assert(FLT_EVAL_METHOD == 0)` in every float unit's prelude |
| 3 | No contraction | PINNED at build time: `instrumente/sonde-fma.c` (the `a*b; r=p+c` shape with `volatile`, differing fused vs separate result) compiled with the manifest flags `-std=c11 -ffp-contract=off -O2 -mfma` and run; plus a positive control that MUST fuse under `-ffp-contract=fast` (`pruefe-emission.sh` speech-probe section) |
| 4 | `FLT_EVAL_METHOD == 0` | PINNED per unit (static assert, fails the build under `-mfpmath=387`/`-m32`); NOT yet a manifest assumption entry of its own |
| 5 | No `-ffast-math` | DECLARED (prelude prose, manifest flag binding) but NOT probed: no build-time check fails if the flag is added |
| 6 | No FTZ/DAZ | NOTHING: no probe, no assert, no manifest entry -- the cheapest new probe of the set (one subnormal round-trip) |
| 7 | Mode stability | NOT covered: the sonde reads the mode at probe time; a library call changing MXCSR mid-run is undetected by construction |

## 6. How the assumption meets the model

The model computes exactly what assumptions 1-6 promise: every op is
the exact result rounded once to nearest-even. The switch task (model
replaces `Float` in `Semantik.lean`) therefore needs no change to the
model -- it needs the seven assumptions above as the bridge, each
either probed (1-4) or newly pinned (5-7), plus the two documented
model cuts (signed-zero inputs, NaN payloads) carried alongside.
