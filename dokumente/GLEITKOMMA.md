# GLEITKOMMA: a kernel-computable IEEE-754 model and its assumption

Lane 166, 2026-09-14. The model lives in
`grammatik/Grammatik/Gleitkomma.lean`; the differential check is
`instrumente/pruefe-gleitkomma.py`. English throughout. **Since the lane
after 166 (same day) the semantics computes with this model (section 7),
the emitted C float forms have a semantics and correspondence lemmas
under the assumption of section 4 (section 8), and nested arrays have a
model (section 9).**

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
  11848 exact, 352 both-NaN, 0 mismatches. ~~One constructed vector
  confirms the documented signed-zero cut (`-0 + -0`: model `+0`,
  hardware `-0`).~~ **The cut is closed** (section 7.1): the population
  now carries every signed-zero pairing and the comparisons `<`/`<=`;
  21128 vectors, 20736 exact, 392 both-NaN, 0 mismatches, and the
  tolerated "known signed zero" class no longer exists.

## 3. Measured surface (inputs to this design)

* Syntax (`dokumente/SYNTAX.md` "F"): `f32`/`f64` with optional `in`
  range, `rounded` compulsory at inexact literals, `finite` behind
  `narrow`, total comparisons (`fllt`/`flle` -- finite by type, no NaN
  quadrant), `hardware ieee` when a result leaves its range or is not
  finite -- since 2026-09-15 `logik bereich` in the model (verdict F1 of
  `messung/URTEIL-OPUS-2026-09-15b.md`: the kernel IEEE model decides the
  range from the program's values, so it is the user's logic, not a
  hardware stop; `gleitkomma_ieee` stays the C-side assumption).
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
* ~~Signed-zero input combinations beyond what the model computes (the
  documented cut; the closing proof must carry it or exclude it).~~
  Closed: the model follows IEEE 754-2019 section 6.3 (section 7.1).
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

## 7. The switch: the semantics computes with this model

### 7.1 Signed zeros first

`add` of two zeros is `-0` exactly for `(-0) + (-0)`; every other exact
zero sum is `+0` (round-to-nearest; `rundeExakt` of an exact zero), so
`x - x = +0` for every finite `x` (`sub_selbst`); `mul`/`div` carry the
xor of the signs; an underflow keeps the sign of the exact result.
Theorems `add_null_null`, `rundeExakt_null`, `sub_selbst`; 17 witnesses
(`zeuge_nullN*`, `zeuge_xMinusX64`, `zeuge_unterlaufNeg64`, ...). `fle` is
false on a NaN operand (lane 166 answered `true`). The mutant without the
zero rule fails six witnesses at build.

### 7.2 What the semantics now reads

| before (`Float`) | now | file |
|---|---|---|
| `Gleit.x : Float`, `x.isFinite`, `bruch lo ≤ x` | `x : GFloat` (`GBits f64`), `gleitEndlich x`, `gleitLe (bruch lo) x` | Typen.lean |
| `bruch q = ofInt q.1 / ofInt q.2` (two roundings) | `rundeBruch f64 ⟨q.1, q.2⟩` (one rounding, the C literal) | Typen.lean |
| `Float.ofInt` | `gleitAusInt = ofInt f64` | Typen.lean |
| `gleitRechne : Float` ops | `add/sub/mul/div f64` | Semantik.lean |
| `fllt/flle` by `decide (<)` | `gleitLt/gleitLe` (`flt/fle f64`) | Semantik.lean |
| `roh` of a float `x.toInt64.toInt` | `gleitRoh`: truncation toward zero, saturated to `Int64` | Semantik.lean |

`Ty.fl` carries no width, and `Float` was binary64, so the model computes
every `Ty.fl` in binary64 (an `f32` program's model value is its binary64
value -- the one named width cut). `gleitPasst` keeps its shape: finite
and inside the rounded bounds, or `none` -- NaN and the infinities take
the `hardware ieee` outcome (or a `narrow`'s `else`), exactly as before.
Every theorem carried: the switch was the one-token rename
`Float.ofInt -> gleitAusInt` in 13 files, and `Satz.gleit_endlich`
restated; no proof changed.

`Format.ebits` is now `bitlen bexpMax` instead of `Nat.log2 (bexpMax+1)`:
`Nat.log2` is well-founded recursion, and the KERNEL, when a proof made it
compare two different `match`es over a stuck float, evaluated it and
recursed out of its stack (15 GB, measured on ki-pc-fisch-101).

### 7.3 Witnesses that were impossible before (GleitZeuge.lean)

* `lauf01_gespeichert`: `let a = 0.1 rounded; let b = 0.2 rounded;
  let c = a + b in 0 .. 1; G := c;` runs through `execBlock` and stores
  exactly `0x3FD3333333333334` in `G` -- by `decide`.
* `lauf01_ueber03`: the same sum declared in `0 .. 3/10` takes
  `hardware ieee` (`0x3FD3333333333334 > (double)0.3`).
* `lauf01_vergleich(Expr)`: `0.1 + 0.2 < 0.3` is false as an expression
  of the language; `laufVon_rundet`: `(double)(2^53 + 1) = 2^53`;
  `laufDurchNull`: `1 / 0` is not finite, `hardware ieee`; `roh_trunc`.

## 8. The C side: float forms and the assumption as a premise

The C semantics (`CFormen.lean`) holds a float as its bit pattern
(`fEin`/`fAus`, inverse on well-formed triples: `ausBits_zuBits`,
`GleitkommaBits.lean`, and every op result is well-formed:
`add_wf` ... `rundeBruch_wf`). Four forms: `CX.fbin` (`a op b` in
`double`/`float`), `CX.fcmp` (the six comparisons, NaN unordered),
`CX.fvon` (integer to float), `CX.fin` (`isfinite`), computing Annex F by
this model. A float local is a `uint64_t` bit container for the model's
conversion at `=`.

**The assumption as a premise.** `gleitkomma_ieee (u : FloatUnit)`
(`CFormenF.lean`) says: on binary32 and binary64 the float unit of the
built binary computes exactly `cFloatBin`, `cFloatCmp`, `cFloatVonInt`,
`cFloatEndlich` -- what section 4's items 1-7 jointly promise. It is
satisfiable (`gleitkomma_ieee_annexF`), and `maschine_fbin/fcmp_*/fvon/
fin` turn it into "the machine's result on the bits of two Gabbro values
is the bits of Gabbro's result". The C semantics itself is Annex F by
definition; the assumption is exactly the gap between Annex F and the
machine, and it now has one Lean name.

Correspondence lemmas (the `BlockSemG`/`ExprCorr` judgements of
CFormenR/I), one per emitted form:

| emitted C | Gabbro | lemma |
|---|---|---|
| `double c = a op b;` | `Block.gleit` | `gsem_gleit` |
| `double c = LIT;` | `Block.gleitLit` | `gsem_gleitLit` |
| `double c = n;` | `Block.gleitVon` | `gsem_gleitVon` |
| `a < b`, `<=`, `>`, `>=` | `Expr.fllt/flle` | `ecorr_fllt/flle/flgt/flge` |
| `if (!(x >= LO && x <= HI)) {…}` | `Block.gleitNarrow` | `gsem_gleitNarrow` + `narrowCondF_ge_le` |
| `if (!isfinite(x)) {…}` | `Block.gleitNarrow` (own range) | `gsem_gleitNarrow` + `narrowCondF_endlich` |
| `return x;`, a float local | (existing) | `scorr_ret`, `ecorr_var` (ValCorr's float case) |

Witness on the emitted C of a corpus program (the smallest with `f64`,
`beispiele/26-gleitkomma.gab`, `klemmen`): `klemmen_corr` (CFormenFZeuge
.lean) -- both branches, every context, every parameter range;
`klemmen_lauf` computes the C condition on `2.0` and `0.25`;
`klemmen_maschine` applies `gleitkomma_ieee`.

`instrumente/pruefe-cformen.py` classifies floats by `double` names and
float literals (before, `if (!(x >= 0.0 && x <= 1.0))` counted as an
INTEGER `if`): lemma rows `stmt:float-decl-arith/-lit/-conv`,
`stmt:float-narrow-range/-finite`, `expr:float-cmp`; dated uncovered rows
`expr:float-lit-inline` (the model binds a constant, C inlines it --
covered per program) and `stmt:float` (binary32, floats in memory).

**What the assumption now covers, and what it does not.** Covered: every
float operator, comparison, integer conversion and class test the
emitter writes in `double`, as a premise of the correspondence. Not
covered: binary32 correspondence (width cut), floats stored in tables
or globals, NaN payloads (never produced by a finite Gabbro value), and
the decimal literal conversion beyond "correctly rounded" (the literal's
bits are pinned per witness: `kHalb_bits`).

## 9. Nested arrays (lane 170's surface)

`[[T; N]; M]` is a table with `count M*N`, `M[i][j]` its cell `i*N + j`
(`Verschachtelt.lean`) -- a stated flattening, not a product index (that
would need a new index type in `Ty`). `flach_bereich` (the two `M103`
bounds), `flach_injektiv` (no aliasing), `flach_zerlegung` (every cell is
one element), `nestIdx`/`eval_nestIdx` (the flat index as a Gabbro
expression), `ev_idx_nested` (C's row-major `a[i][j]` is the flat access);
witnesses `nv_lauf`, `nv_bijektiv`, `nv_c_adresse`. The memory relation of
a static C array is the pre-existing uncovered `expr:array-read`.

