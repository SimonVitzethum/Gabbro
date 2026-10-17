# Floating point: a kernel-computable IEEE-754 model, its assumptions, and why floats are different

*Rewritten 2026-10-17; absorbs the old `dokumente/GLEITKOMMA.md`. English throughout. Status: **floats are in
scope and built**: `f32`/`f64` are in the language, the Lean semantics computes with a kernel-computable
IEEE-754 binary model, the legacy C backend has float forms with correspondence lemmas under one named
assumption, and the LLVM backend lowers floats directly. The first memo (2026-08-18) concluded "do not build:
measured need zero, price a second fact logic"; the need was re-decided on 2026-09-14 (Simon: floats are in
scope), and its landmines section is what survived.*

## 1. The surface

(`SYNTAX.md` sections for «F» and «SG-17»; example `beispiele/26-gleitkomma.gab`.)

* Types `f32`, `f64`, each with an optional range `in lo .. hi` (`floatty`). Only these two exist: there is no
  `f16` and no `long double` in the grammar (a plan-level refusal, below).
* **In the core a float type always carries a range, and every value of it is finite and inside it** (`Ty.fl lo
  hi`, `Gleit lo hi`); `f64` without `in` is sugar for the widest finite range. So there is no NaN quadrant:
  `<`/`<=` are total (`Expr.fllt`, `Expr.flle`).
* `rounded` is compulsory at a literal that is not exactly representable; `narrow x to finite` and float range
  narrowing are checked branches (`Block.gleitNarrow`); `let y = a op b`, `1.5 rounded`, `f64(n)` are
  `Block.gleit`/`gleitLit`/`gleitVon`.
* A result that leaves its declared range or is not finite is **`logik bereich`**: the program's own logic under
  the kernel IEEE model, which the user proves never happens. (Until 2026-09-15 it was a hardware stop,
  `hardware ieee`; verdict F1 of `dokumente/BEWEIS.md` moved it, since the model decides it from
  the program's values. `gleitkomma_ieee` stays the machine-side assumption.)
* Floats in `accumulates` are refused: `F004` (the fold has no order; section 6).
* Manifest/profile: `fp_contract off` and `rounding nearest` are profile entries (`SYNTAX.md` section 12.2); a
  profile that contradicts the float assumption (an `fp_contract` other than `off`) is refused.
* Bitwise operations on floats and `finiteness` of a non-float have no lowering in the LLVM backend (`Y104`).

## 2. The model (`grammatik/Grammatik/Bausteine/Gleitkomma/Gleitkomma.lean`)

**Why a new model.** The first model computed with Lean's built-in `Float`, which is opaque to the kernel: nothing
about float values can be proved and no witness computed without `native_decide` (forbidden). The replacement is
data, and reduces in the kernel.

* Formats as data: `Format` (`p` significand bits including the hidden one, `emax`, `emin = 1 - emax`);
  `f32 = (24, 127)`, `f64 = (53, 1023)`.
* Values as bit triples `GBits` (sign, biased exponent, significand) with the five IEEE classes (null, subnormal,
  normal, infinity, NaN), `wf`, `zuBits`/`ebits`. (`Format.ebits` is `bitlen bexpMax`, not `Nat.log2`: well-founded
  recursion made the kernel recurse out of its stack, 15 GB measured.)
* Exact values: `Exakt` (dyadic: every finite float and every exact `add`/`sub`/`mul` result) and `Bruch`
  (general rational; division needs it).
* Rounding `rundeBruch` (round-to-nearest-ties-to-even from an exact rational) via `findeExp` and the isolated
  significand decision `rundeInt`; structural/fuel recursion only.
* Operations as "exact result, then round": `add/sub/mul/div/ofInt/ofRat/neg`, `flt/fle`, with the IEEE
  special-case tables (`inf + -inf`, `0 * inf`, `0 / 0` are NaN; xor of signs).
* **Signed zeros** follow IEEE 754-2019 section 6.3: `add` of two zeros is `-0` exactly for `(-0) + (-0)`, every
  other exact zero sum is `+0`, so `x - x = +0` for every finite `x` (`sub_selbst`, `add_null_null`,
  `rundeExakt_null`); `mul`/`div` carry the xor of signs; an underflow keeps the sign of the exact result; `fle` is
  false on a NaN operand.
* Theorems: `rundeInt_fall/steig/tie`, `rundeInt_monoton`, `bitlenAux_*`, `findeExp_*`, `rundeBruch_finite`
  (in-range exact values round to normal/subnormal/null, never inf/NaN), per-op finite-in-range theorems
  (`add/mul/div/ofInt/ofRat_finite`, `sub` via `neg`), well-formedness of every result (`add_wf` ...
  `rundeBruch_wf`, `GleitkommaBits.lean`). Witnesses by `decide` in `GleitZeuge.lean`, among them
  `0.1 + 0.2 = 0x3FD3333333333334`, `1/3` in both widths, ties in both directions, minimal subnormals, overflow
  to `+inf`, `0/0` NaN, `1/0` inf; a mutant without the zero rule fails six witnesses at build.
* **Differential check:** the model against hardware C over 21,128 vectors (4 ops x 2 widths, random and edge
  pairs, every signed-zero pairing, the comparisons) gave 20,736 exact, 392 both-NaN, 0 mismatches (lane 166 and
  its follow-up). The driver script `instrumente/pruefe-gleitkomma.py` is **not in the tree today**; the number is
  the recorded result.

## 3. What the semantics reads (the switch from `Float`)

| Before (`Float`) | Now | File |
|---|---|---|
| `Gleit.x : Float`, `x.isFinite`, `bruch lo <= x` | `x : GFloat` (`GBits f64`), `gleitEndlich x`, `gleitLe (bruch lo) x` | `Kern/Syntax/Typen.lean` |
| `bruch q = ofInt q.1 / ofInt q.2` (two roundings) | `rundeBruch f64 <q.1, q.2>` (one rounding, the C literal) | same |
| `Float.ofInt` | `gleitAusInt = ofInt f64` | same |
| `gleitRechne` ops | `add/sub/mul/div f64` | `Kern/Semantik/Semantik.lean` |
| `fllt/flle` by `decide (<)` | `gleitLt/gleitLe` | same |
| `roh` of a float | `gleitRoh`: truncation toward zero, saturated to `Int64` | same |

`Ty.fl` carries no width, so the model computes every `Ty.fl` in binary64 (an `f32` program's model value is
its binary64 value: **the one named width cut**). `gleitPasst` keeps its shape: finite and inside the rounded
bounds, or `none` (NaN and infinities take the out-of-range outcome, or a `narrow`'s `else`). Every theorem
carried over with a one-token rename; witnesses impossible before now run through `execBlock` by `decide`
(`lauf01_gespeichert`, `lauf01_ueber03`, `lauf01_vergleich`, `laufVon_rundet`, `laufDurchNull`, `roh_trunc`).

## 4. The named assumption, and what pins it

One assumption per machine fact the model reads but never proves:

| # | Fact | Pin today |
|---|---|---|
| 1 | `gleitkomma_rundungsmodus_ist_rne`: every `+ - * /` and conversion rounds to nearest-even | manifest entry, falsifier `sonde_mxcsr_rne` (reads MXCSR and the x87 control word and rounds two ties that separate all four modes, with an arm that sets each violating mode first) |
| 2 | `gleitkomma_x86_rechnet_mit_sse2`: SSE2, never the x87 stack (80 bits, rounds twice) | manifest entry, falsifier `sonde_keine_ueberbreite`; in the C backend also `_Static_assert(FLT_EVAL_METHOD == 0)` in every float unit's prelude (`KOPF_GLEITKOMMA`) |
| 3 | no contraction (no FMA fusing a neighbour) | C backend: build flag `-ffp-contract=off`, probed by `instrumente/sonde-fma.c`; LLVM backend: no `contract` flag is ever emitted |
| 4 | `FLT_EVAL_METHOD == 0` | pinned per C unit by the static assert; not a manifest entry of its own |
| 5 | no fast-math (no reassociation or value-changing optimisation) | declared in the C prelude and the manifest flag binding, **not probed**; the LLVM backend emits no fast-math flags (grep of `llvm.rs`) |
| 6 | no FTZ/DAZ (subnormals preserved) | **nothing**: no probe, no assert, no manifest entry |
| 7 | the rounding mode stays stable (MXCSR/FPCR is global state) | **not covered**: the probe reads the mode at probe time, not continuously |

Only items 1 and 2 exist as generated manifest entries (`crates/gabbro-check/src/manifest.rs`, emitted when a
unit touches floats). Items 3-7 are stated here but are not entries of their own: proposed names
(`gleitkomma_keine_kontraktion`, `..._flt_eval_method_null`, `..._kein_fast_math`, `..._subnormal_erhalten`,
`..._rundungsmodus_stabil`) were never added to the manifest.

**Out of the assumption by standard or by construction:** NaN payloads and quiet bits (IEEE leaves them open; a
finite Gabbro value never produces one); `libm` (the language has no transcendentals: `sin`, `exp`, `pow` would each
need a correctly-rounded implementation or their own assumption); decimal literal conversion beyond "correctly
rounded" (the `rounded` word marks exactly the literals that are not exactly representable; the C backend's `f`
suffix rule keeps `f32` literals single-rounded: `(float)0.1 == 0.1f`).

## 5. The backends

**Legacy C11 backend** (`C-SPEICHERMODELL.md`): `f32 -> float`, `f64 -> double`; a per-unit prelude
(`KOPF_GLEITKOMMA`) forbids `-ffast-math` and fixes `-ffp-contract=off`; float literals carry `f` exactly when the
node computes in `float` (else C would lift to `double` and round twice); mixed `float`/`double` arithmetic is
refused. The Lean C semantics holds a float as its bit pattern (`fEin`/`fAus`) and has four forms: `CX.fbin`,
`CX.fcmp` (six comparisons, NaN unordered), `CX.fvon`, `CX.fin` (`isfinite`), computing Annex F by this model
(`CFormenF.lean`).

**`gleitkomma_ieee (u : FloatUnit)`** says: on binary32 and binary64 the float unit of the built binary computes
exactly `cFloatBin`, `cFloatCmp`, `cFloatVonInt`, `cFloatEndlich`. It is satisfiable (`gleitkomma_ieee_annexF`),
and `maschine_fbin/fcmp_*/fvon/fin` turn it into "the machine's result on the bits of two Gabbro values is the bits
of Gabbro's result": the assumption is exactly the gap between Annex F and the machine, and it has one Lean name.

| Emitted C | Gabbro | Lemma |
|---|---|---|
| `double c = a op b;` | `Block.gleit` | `gsem_gleit` |
| `double c = LIT;` | `Block.gleitLit` | `gsem_gleitLit` |
| `double c = n;` | `Block.gleitVon` | `gsem_gleitVon` |
| `a < b`, `<=`, `>`, `>=` | `Expr.fllt/flle` | `ecorr_fllt/flle/flgt/flge` |
| `if (!(x >= LO && x <= HI)) {...}` | `Block.gleitNarrow` | `gsem_gleitNarrow` + `narrowCondF_ge_le` |
| `if (!isfinite(x)) {...}` | `Block.gleitNarrow` (own range) | `gsem_gleitNarrow` + `narrowCondF_endlich` |

Witness: `klemmen_corr` (`CFormenFZeuge.lean`) for `beispiele/26-gleitkomma.gab`. Covered: every float operator,
comparison, integer conversion and class test written in `double`, as a premise of the correspondence. Not
covered: binary32 correspondence (the width cut), floats in tables or globals, NaN payloads, and the literal
conversion beyond the per-witness bits (`kHalb_bits`). `pruefe-cformen.py` classifies float forms by `double`
names and float literals (rows `stmt:float-decl-arith/-lit/-conv`, `stmt:float-narrow-range/-finite`,
`expr:float-cmp`; dated uncovered rows `expr:float-lit-inline` and `stmt:float`).

**LLVM backend** (`LLVM-BACKEND.md`): `float`/`double` cells, hex-float literals, `fpext`/`fptrunc` between the
widths, `Ty.fl` not built by the G exporter (direct surface lowering); range narrowing with constant or runtime
bounds. Which machine facts the compiler relies on are items 1-7 above, unpinned where the table says so.

## 6. Why floats are different: the landmines

IEEE 754 is fully deterministic: at a fixed rounding mode each base operation gives exactly one bit pattern, so
floats are logically no harder than bit vectors with an unwieldy interpretation function. What is hard is the
SPECIFICATION (two semantics, real and machine, plus the relation) and these surroundings:

| | |
|---|---|
| **Non-associativity** | `(a+b)+c != a+(b+c)`: any reordering by a compiler is unsound, `-ffast-math` is dead in a verified context, parallel reductions are deterministic only with an explicit order |
| **libm** | IEEE 754 does not require correct rounding for `sin`, `exp`, `log` (2019 only recommends it); verification ends at the libm edge unless axiomatised or verified |
| **Rounding mode** | MXCSR/FPCR is an implicit input to every operation; nearly all proofs pin round-to-nearest-even and verify the pinning separately |
| **Excess precision** | x87 at 80 bits and double rounding: why CompCert presupposes SSE2 on x86; ignoring `FLT_EVAL_METHOD` is a hole |
| **NaN payloads** | implementation-defined; bit-exact statements about them are platform-specific |
| **NaN breaks negation** | with a NaN operand all comparisons are false, so `!(x < y) => x >= y` fails and `m1::fakten_aus(..., negiert = true)` would be unsound: that is the machinery every narrowing in this language uses. Gabbro avoids it by construction: a float type carries a range and is finite, so the comparison is total and the NaN quadrant does not exist (section 1) |
| **`accumulates`** | the proved template `accumulates.monoid` rests on the premise "the operator comes from `max`/`min`/`add`/`or`/`and` (the vocabulary is closed) AND all number types are integral". Over floats `add` is not associative and `max` with NaN is no lattice, so `F004` refuses `accumulates` over a float type, mechanically. (The comment in `schablonen.rs` that says "there is no floating-point type" is stale.) |
| **ABI** | a function `f64 -> f64` takes its arguments in `xmm0`/`xmm1` on a normal x86_64 target and in `rdi`/`rsi` on a soft-float one: two calling conventions, equal symbol names, silent corruption. Two units with different float decisions talk past each other; the library ABI owes this question (not measured again in this rewrite) |
| **Kernels** | verified kernels (seL4 included) keep floats out of the trusted base for reasons independent of verification: the rounding mode is user-controlled global state to be saved and normalised on kernel entry, lazy FPU switching has its own leak class (LazyFP, CVE-2018-3665), and FP context makes preemption dearer |

**Refusals that are the answer, not gaps.** `long double` is not a type but a platform lottery (80-bit x87 on x86
Linux, 128 bit elsewhere, `double` on others) and *is* the excess-precision hole: someone who needs 80 bits names
them, as another type with another promise. `f16` is on most targets a storage form plus a conversion; computing
in `f32` makes `f16 -> f32 -> f16` a double-rounding landmine, and as pure storage it belongs to `format`. Neither
word is in the grammar.

**Fixed point stays available and needs no float logic:** M1 computes with the declared RANGE, not the type width,
so `type Q16 = i64 in -2147483648 .. 2147483647;` with `(a * b) >> 16` needs no run-time check; the carrier is the
width, the range is the promise. What people usually want when they say "float" is a decimal place.

**Open design idea, cheap and independent of arithmetic:** the rounding mode in the type (`f64<RNE>` that cannot
mix with `f64<RTZ>`), the fourth instance of a pattern the language already follows (`ptr<normal, rw>`, `atomic
... seq`, `format ... endian big`): the property stands at the type or declaration, not in environment state. It is
not built; today the mode is the profile entry `rounding nearest` plus assumption 1. Guest code behind `entrust`
(a JIT or a GPU shader) has a rounding mode too, and nothing says anything about it.

## 7. Nested arrays (lane 170's surface)

`[[T; N]; M]` is a table with `count M*N`, `M[i][j]` its cell `i*N + j`
(`grammatik/Grammatik/Nebenlaeufigkeit/Allgemein/Verschachtelt.lean`): a stated flattening, not a product index (that
would need a new index type in `Ty`). `flach_bereich` (the two `M103` bounds), `flach_injektiv` (no aliasing),
`flach_zerlegung`, `nestIdx`/`eval_nestIdx`, `ev_idx_nested` (C's row-major `a[i][j]` is the flat access); witnesses
`nv_lauf`, `nv_bijektiv`, `nv_c_adresse`. The memory relation of a static C array is the pre-existing uncovered
`expr:array-read`.

## 8. Open

* binary32 in the model (the width cut) and its C/LLVM correspondence; floats in tables and globals;
* assumptions 3-7 as manifest entries with probes (the cheapest: one subnormal round-trip for item 6);
* a differential driver for the model against hardware (the old script is gone);
* the float ABI question for the library boundary, and the rounding mode in the type.
