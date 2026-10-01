# FLOAT-ZEIT: floats and time for direct x86-64 validation (lane 278)

*Owner: lane 278. Scope: map the existing IEEE model and the exact claimed
time/progress conclusions onto the selected direct-x86 target; name every
control-state, contraction, ordering and timing obligation; propose checked
cost summaries and hardware-profile data with unproved bounds marked. No
source-guarantee change, no new checker rule, no emitted-C change.*

*Wave-A contract (dokumente/x86/WELLE-A.md): the canonical pilot vocabulary
is `grammatik/Grammatik/X86/Typen.lean` (`Gabbro.Grammatik.X86`); it
currently admits only integer/control `Befehl` constructors — **no float
instruction is in the pilot**. Everything in §§4–5 below is therefore a
proposal with explicit gaps, not a completed correspondence. The Rust
mirror stays unwired until its Lean part and correspondence are reviewed;
existing C behaviour stays green.*

*Language: English only. All file references are to this checkout.*

---

## 0. What is claimed here and what is not

Claimed:

- (a) An exact inventory of the source float surface, the kernel-computable
  IEEE model, and the stop outcomes the goal theorem actually relies on
  (§§1–3), each tied to its file and line.
- (b) A per-form mapping from that surface onto scalar SSE/SSE2 machine
  forms, with one named obligation per machine fact the model reads but
  never proves: rounding control, NaN class (relaxation OPEN until
  proved, §4.3), signed zero, denormals, traps plus reserved status
  flags, contraction/FMA, expression order, excess precision, fast-math
  (§4). Later SIMD is admission-gated, never implicit (§5).
- (c) A three-level separation for time — model steps, checker/certificate
  costs, hardware timing — with the exact Ziel conclusions quoted and
  preserved, and the transfer obligations of every starter optimisation
  stated without inventing scheduler, OS or fairness premises (§§6–7).
- (d) A proposal for checked target cost summaries and concrete
  hardware-profile data, every cycle bound marked unproved (§8).
- (e) The generic phase-B definitions/lemmas and the blockers (§§9–10).

NOT claimed: no decoder, no encoder round-trip, no per-access TSO float
lemma, no final-image theorem, no cycle bound, no new `Spec.lean` premise.
Where a premise would be needed, it is named as a gap, not smuggled in.

---

## 1. Source float inventory (exact)

Model computations are binary64 throughout: `GFloat` is
`Gleitkomma.GBits Gleitkomma.f64` (`Typen.lean:82`). `Ty.fl` carries no
width; an `f32` program's model value is its binary64 value — the named
width cut (`Typen.lean:79-82`, `Semantik.lean:399`, `GLEITKOMMA.md` §7.2).

| Source form | Lean name | File |
|---|---|---|
| `f32` / `f64` types, `rounded`, `finite` | `Ty.fl`, `GleitOp` (`add \| sub \| mul \| div`) | `Syntax.lean:50,447` |
| float comparisons (total, finite by type) | `Expr.fllt`, `Expr.flle` | `Syntax.lean:407-408` |
| float op with result range | `Block.gleit op a b lo hi rest` | `Syntax.lean:590` |
| float literal | `Block.gleitLit q lo hi rest` | `Syntax.lean` («F» block) |
| integer to float | `Block.gleitVon e lo hi rest` | `Syntax.lean` («F» block) |
| float narrow / finite check with else | `Block.gleitNarrow e lo hi sonst rest` | `Syntax.lean:599` |
| machine arithmetic | `gleitRechne : GleitOp → GFloat → GFloat → GFloat` (`add/sub/mul/div f64`) | `Semantik.lean:649-654` |
| literal / bounds as float | `bruch : Int × Int → GFloat` (one rounding, `rundeBruch f64`) | `Typen.lean:88` |
| integer as float | `gleitAusInt = ofInt f64` (C's `(double)n`) | `Typen.lean:92`, `Semantik.lean` §7.2 |
| finiteness | `gleitEndlich` (not inf, not NaN; C's `isfinite`) | `Typen.lean:95` |
| comparisons | `gleitLe = fle f64`, `gleitLt = flt f64` (NaN unordered, ±0 equal) | `Typen.lean:102-105` |
| range gate | `gleitPasst lo hi x : Option (Gleit lo hi)` (finite and inside) | `Semantik.lean:351-352` |
| float as raw integer | `gleitRoh` (truncation toward zero, saturated to `Int64`; none → 0) | `Semantik.lean:625-633` |
| range-carrying value | `Gleit lo hi` (`x`, `endlich`, `lo_le`, `le_hi`) | `Typen.lean:111-114` |

Refused today, relevant to the target: mixed `float`/`double` arithmetic
(`CForm doubleTyp`, `emit.rs:3795-3802,10643-10719`); `f16`/`f80`/`f128`/
`long double` by name (`namen.rs:2646-2669`, `F006`); transcendentals
(`sin`, `exp`, `pow`) — no language form, each would need its own
correctly-rounded implementation or named assumption (`PLAN-BITS.md` §5.5).

Emitter lowering today (`emit.rs`, `CFormenF.lean:8-22` header):

- `f32 → float`, `f64 → double`; float literals get the `f` suffix exactly
  where the node computes in `float` (else C lifts to `double` and rounds
  twice); float locals are `double c = …`.
- Arithmetic `a + b`, `a - b`, `a * b`, `a / b` bare, operands of one
  float type; comparisons `a < b`, `a <= b`, `a > b`, `a >= b` bare
  (`ecorr` covers `>`/`>=` via operand swap, `ecorr_geSwap`).
- Literals as shortest round-trip decimal of the `f64` bits
  (`gleitkommatext`); `narrow x to lo .. hi else` as
  `if (!(x >= LO && x <= HI))`; `narrow x to finite else` as
  `if (!isfinite(x))`.
- Unit prelude `KOPF_GLEITKOMMA` (`emit.rs:917-938`): `-ffast-math`
  FORBIDDEN in prose, build with `-ffp-contract=off`,
  `#include <float.h>` / `<math.h>`,
  `_Static_assert(FLT_EVAL_METHOD == 0, …)` on every unit.
- Manifest (`manifest.rs:78-136`): two generated assumptions per float
  unit — `gleitkomma_rundungsmodus_ist_rne` (probe `sonde_mxcsr_rne`) and
  `gleitkomma_x86_rechnet_mit_sse2` (probe `sonde_keine_ueberbreite`);
  profile key `fp_contract off` binds `-ffp-contract=off`
  (`manifest.rs:538-547`, `PLAN-BITS.md` §5.2). Review repair: the
  manifest's "GLOBAL state (MXCSR/FPCR)" wording is superseded for x86
  by the per-execution-context reading with checked
  establishes/preserves (§4.2.1/7).

---

## 2. The IEEE model (what the target must match)

`grammatik/Grammatik/Gleitkomma.lean` (kernel-computable; replaces opaque
`Float` since 2026-09-14):

- Formats as data: `Format` (`p`, `emax`), `f32 = (24,127)`,
  `f64 = (53,1023)`; values as bit triples `GBits` (sign, biased
  exponent, significand) with five classes `Klasse`
  (`null/subnormal/normal/unendlich/nan`) and `wf`; `zuBits`/`ebits`
  (`bitlen`, structural, not `Nat.log2`).
- Exact values: `Exakt` (dyadic — every finite float and every exact
  `add`/`sub`/`mul` result) and `Bruch` (general rational — division
  needs it); `wertExakt` (`none` for inf/NaN).
- Rounding: `rundeBruch` (round-to-nearest-ties-to-even from an exact
  rational) via `findeExp` and the isolated significand decision
  `rundeInt`; structural/fuel recursion only (kernel-reducible).
- Ops as "exact result, then round": `add/sub/mul/div/ofInt/ofRat/neg`,
  `flt/fle` (NaN unordered → `false`; infinities by sign; finite by exact
  cross-multiplication; signed zeros equal), with the IEEE special-case
  tables (`inf + -inf`, `0 * inf`, `0 / 0` are NaN; xor signs).
- Signed zeros follow IEEE 754-2019 §6.3: `add` of two zeros is `-0`
  exactly for `(-0) + (-0)` (`add_null_null`); every other exact zero sum
  is `+0` (`rundeExakt_null`); `x - x = +0` for every finite `x`
  (`sub_selbst`); `mul`/`div` carry xor of signs; underflow keeps the sign
  of the exact result (witness `zeuge_unterlaufNeg64`).
- NaN policy: computed NaNs are canonical `nanQ`; propagated NaNs keep
  input bits; **no quiet-bit discipline** (open by standard).
- Proved: `rundeInt_fall/steig/tie/monoton`, `bitlenAux_obere/untere`,
  `findeExp_unten`, `rundeBruch_finite`, per-op finite-in-range
  (`add/mul/div/ofInt/ofRat_finite`, `sub` via `neg`), `klasse_neg`,
  `wertExakt_neg_some`; well-formedness of every result
  (`GleitkommaBits.lean`: `add_wf … rundeBruch_wf`, inverse
  `ausBits_zuBits` under `dicht`, bound `zuBits_lt`); `decide` witnesses
  incl. `0.1 + 0.2 = 0x3FD3333333333334`, ties both directions, min
  subnormals both widths, overflow to `+inf`, `0/0` NaN, `1/0` inf.
  Axioms of the model theorems: `propext`, `Quot.sound`
  (plus `Classical.choice` where the statement needs it).
- CUTS (model file): no single "nearest float" theorem over all `GBits`;
  `findeExp` upper bound unproved; overflow-boundary exactness and the
  deep-underflow shortcut rest on algorithm + witnesses + differential
  check; only RNE mode; binary32/binary64 only; differential check
  (21128 vectors, 0 mismatches) is evidence, not a theorem.

The C correspondence reads this model through bit patterns
(`CFormen.lean`: `cFloatBin/cFloatCmp/cFloatVonInt/cFloatEndlich`;
`CFormenF.lean`: `gleitkomma_ieee` premise over `FloatUnit` with `annexF`
witness; machine lemmas `maschine_fbin/fcmp/fvon/fin`; per-form lemmas
F1–F7 `gsem_gleit/gsem_gleitLit/gsem_gleitVon`,
`ecorr_fllt/flle/flgt/flge`, `gsem_gleitNarrow + narrowCondF_ge_le /
narrowCondF_endlich`). **The correspondence is for `double`** (model
computes `Ty.fl` in binary64). Uncovered there, hence uncovered for x86
until closed: binary32 correspondence (width cut), floats stored in
tables/globals, NaN payloads, decimal literal conversion beyond
"correctly rounded".

---

## 3. Stop outcomes (exact Ziel reading — do not weaken, do not extend)

- Since verdict F1 (2026-09-15), an out-of-range float is **`Logik.bereich`**
  in the sequential semantics (`Semantik.lean:29,288-302,862-876`;
  `SperreSem.lean:351-365`): `Block.gleit/gleitLit/gleitVon` with
  `gleitPasst … = none` yield `.logik .bereich`. The `Hardware.ieee`
  constructor stays only for the C-side vocabulary; nothing produces it
  any more. Rationale (`Spec.lean:1249-1251,1311-1312`): the kernel IEEE
  model decides the range from the program's values, so it is the user's
  logic, not a hardware stop; `gleitkomma_ieee` stays the C-side
  assumption.
- `FortschrittG` (`Spec.lean:1828-1831`) lists **no float stop**: every
  thread is finished, lock-waiting, at a named `flagge`/`budget`/
  `hardware`/`nieZurueck` stop, or can step. Float range checks are
  proof-side: `BereichG` (`Fortschritt.lean:517-538`) requires the
  `gleit*` head's result to pass `gleitPasst`; `fadenS_bereich` carries it
  from the user's body obligation (`KoerperGutS`, which excludes `logik`
  outcomes incl. `bereich`) to every thread of every reachable machine
  (`bereichG_erreichbarL/mehrfaden`); `fort_dann/fort_ende` take `hB :
  BereichG` as a premise. Consequence for x86: **a float range failure
  must lower to user-logic refusal, never to a new hardware-stop
  disjunct**; adding a float stop to `FortschrittG` would be a reviewed
  `Spec.lean` diff, out of scope for this lane.
- `gleitNarrow` with `none` takes the `else` branch (a normal step), not a
  stop (`Semantik.lean:874-876`, `Fortschritt.lean:909-913`).
- `KeinLogikHaltG` (no thread stuck at a `logik` check) therefore covers
  float ranges too; the target must preserve it: an optimisation that
  turns a passing range check into a failing one (or removes the check
  the `narrow` form carries) breaks the conclusion, not just performance.

---

## 4. Hardware mapping: scalar SSE/SSE2 (proposal, gaps named)

Target profile: 64-bit execution, SSE/SSE2 baseline only (per
`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §2: "scalar SSE/SSE2 for f32/f64; bind
rounding, exceptions, NaNs and floating-point control state to the
existing IEEE model"). The pilot `Befehl` type has no float constructor
today — each row below names the machine form AND the missing Lean piece.

### 4.1 Per-form mapping

**Every `SS`/`float` half of the table below is refused pending the §4.3
f32 bridge; only the `SD`/`double` halves carry a correspondence proposal.**

| Model / source form | Machine form (proposal) | Correspondence obligation |
|---|---|---|
| `GleitOp.add` on f32 / f64 | `ADDSS` / `ADDSD` (xmm, xmm/m32/m64) | one source op = one instruction; RNE; class-level result equality incl. ±0 (no `-0 → +0` canonicalisation; payload per the §4.3 relaxation, OPEN until proved) |
| `GleitOp.sub` | `SUBSS` / `SUBSD` | as above; `x - x = +0` must survive (no `x-x → +0` folding that also fires on `-0 - -0`, which must stay `+0` — equal here, but the fold must not drop the invalid flag on signalling inputs; simplest rule: no folding of float ops at all, §7) |
| `GleitOp.mul` | `MULSS` / `MULSD` | as above; `0 * inf = NaN` (invalid flag) preserved — DCE/CSE must treat float ops as faulting (§7) |
| `GleitOp.div` | `DIVSS` / `DIVSD` | as above; `0/0` NaN, `1/0` ±inf, `finite/inf` ±0 with xor signs |
| `Block.gleitLit` (`bruch q`, one rounding) | correctly-rounded decimal→binary at image build + `MOVSS`/`MOVSD` (or RIP-relative load) | build-time conversion proved correctly rounded once; NO double-rounding via `double` for `f32` literals (the emitter `f`-suffix rule becomes a validator check on the encoded constant); `den = 0` is NaN by definition |
| `Block.gleitVon` (`gleitAusInt`) | `CVTSI2SS` / `CVTSI2SD` | operand-width obligation: the source integer width (32 vs 64 bit) selects the form; GLEITKOMMA §8's `Ty.fl`-in-binary64 cut applies |
| `Expr.fllt/fllle` (+ `flgt/flge` via swap) | `UCOMISS` / `UCOMISD` + `SETcc`/`Jcc` | NaN unordered: `UCOMI` sets ZF,PF,CF on NaN/QNaN — the lowering must answer `false` for both `<` and `<=` on any NaN operand (model `flt/fle` return `false`); ordered-vs-unordered branch selection (`JP` handling) is part of the correspondence, not peephole folklore |
| `Block.gleitNarrow` range (`x >= LO && x <= HI`) | two `UCOMISS/D` + integer `AND` of the `SETcc` results (`narrowCondF_ge_le` shape) | the check STAYS (W6 inverted in C: `if (!(…))`); removing it breaks `KeinLogikHaltG` transfer |
| `Block.gleitNarrow` finite (`isfinite`) | bit-test on the loaded word (exponent field all-ones → not finite; `cFloatEndlich` shape), NOT a trapping compare | must agree with `gleitEndlich` on inf AND NaN (both non-finite) |
| `gleitRoh` (float→int for the machine) | `CVTTSS2SI` / `CVTTSD2SI` + explicit saturation wrapper | hardware returns the "integer indefinite" value (`0x8000…`) on invalid (NaN, out of range); the wrapper proving saturation to `Int64` is the correspondence — a bare `CVTT*` instruction alone does NOT implement `gleitRoh` |

Explicitly NOT mapped: x87 opcodes (`D8–DF`, `FLD/FSTP/FADD…`) — refused
syntactically; MMX — out of scope; `ROUNDSS/ROUNDSD`, `CVTSS2SI` (RNE
mode, non-truncating) — only if a source form needs them, with their own
MXCSR-dependence lemma.

### 4.2 Control state (one obligation per machine fact)

The model reads seven machine facts and proves none
(`GLEITKOMMA.md` §4). For x86 each becomes a validator premise or a
syntactic refusal; the current pin status (measured 2026-09-14, C
backend) is noted so phase B does not assume it carries over:

1. **RNE mode.** Every `ADD/SUB/MUL/DIVSS/SD`, every conversion, computes
   in round-to-nearest-ties-to-even. Machine fact (silicon): each
   instruction rounds per the MXCSR value it executes under, bits 13–14
   (RC) `= 00` required. MXCSR is architectural state per execution
   context (logical CPU), NOT process-global: continuity across thread
   context switches is established by software save/restore — user/binding
   logic with contracts, never a hardware guarantee. The validator
   obligation is checked establishes/preserves, not a bare stability
   assumption: image entry ESTABLISHES the required MXCSR value (checked),
   and every enumerated `LDMXCSR` site PRESERVES it (re-establishes the
   required value or is refused); unlisted writers are refused. C pin
   today: `sonde_mxcsr_rne` (MXCSR + x87 control word read + tie
   witnesses) — reads one process value at probe time and proves nothing
   about per-context continuity; the x86 mechanism replaces it.
2. **SSE2, no x87 / no excess precision.** Machine fact: computation at
   the named width, single rounding. Validator: refuse all x87 encodings;
   refuse 80-bit temporaries; the `FLT_EVAL_METHOD == 0` static assert has
   no direct-x86 analogue — the property is proved per instruction form
   instead. C pin today: `sonde_keine_ueberbreite` + per-unit assert.
3. **No contraction.** Each source-level op rounds separately: one
   `Block.gleit` = exactly one scalar op instruction. Encoded fused forms
   (`VFMADD*SS/SD`) are refused unless a contracted source form with its
   own model/checker/certificate is admitted (none exists today).
   Micro-op fusion or decomposition of separately encoded scalar
   instructions inside the core does not change architecturally visible
   rounding: only exact instruction-level semantics is modelled, and no
   hidden-fusion premise is carried. What is refused is an *encoded*
   fusion — an FMA opcode standing for two source ops. Measured
   background: without `-mfma`
   the x86-64 baseline has no FMA; with `-mfma`/`-march=` both GCC and
   Clang contract, Clang even within one statement (`PLAN-BITS.md` §5).
   C pin today: build-time `sonde-fma.c` triple + `-ffp-contract=off`.
   x86 gap: the flag is gone; refusal of fused encodings is the mechanism.
4. **`FLT_EVAL_METHOD == 0` content.** Covered per form by (2); no separate
   premise. (In C it was a per-unit assert; it failed under
   `-mfpmath=387`/`-m32` — the x86 validator has no flags to set, only
   encodings to refuse.)
5. **No fast-math.** No reassociation, no value-changing optimisation of
   float code. For x86 this is a *validator + optimiser-certificate*
   rule, not a build flag: any IR/opt step touching float code must
   carry a bit-exactness certificate (§7); reassociation
   (`(a+b)+c → a+(b+c)`), distribution, `x-x → 0`, `0*x → 0`,
   `x/…` reciprocal approximation (`RCPSS/RCPPS`, `RSQRTSS` — never a
   substitute for `DIVSS`), and excess-precision promotion (`float` node
   computed in `double`) are refused. Note `schablonen.rs:935-941`:
   over `f64`, `add` is not associative and `max` with NaN is no lattice
   — generic merge/optimiser rules that assume associativity must exclude
   float lanes syntactically. C pin today: prelude prose + manifest flag
   binding only (NOT probed) — x86 must do better: syntactic refusal.
6. **Subnormals preserved (no FTZ/DAZ).** Machine fact: MXCSR.FTZ (bit 15)
   `= 0`, MXCSR.DAZ (bit 6) `= 0`; gradual underflow per the model's
   `subQ` path (min-subnormal witnesses `zeuge_subnormal32/64`,
   `zeuge_subnormalAdd`, `zeuge_unterlaufNeg64`). C pin today: NOTHING
   (cheapest missing probe). x86 gap: validator premise + hardware-profile
   datum (§8) + a subnormal round-trip falsifier.
7. **Control-state continuity (not a stability assumption).** There is
   no bare "nobody changes MXCSR" premise: entry ESTABLISHES the required
   value and every writer PRESERVES it, both validator-checked (item 1);
   `STMXCSR` readers are enumerated alongside the writers (a reader makes
   the value observable — the §4.2-traps status-flag reservation applies).
   C pin today: NOT covered (probe reads at probe time). Software
   save/restore across context switches (OS, runtime) is user/binding
   logic with contracts; libraries that write MXCSR must re-establish
   RNE/FTZ/DAZ/masks or be refused; interrupt handlers must save/restore
   the MXCSR+XMM state they touch (§7 interrupts).

Traps (no model outcome — hence a refusal, not a premise to tune):
**all FP exception masks set** (MXCSR bits 7–12 IM/DM/ZM/OM/UM/PM `= 1`,
i.e. traps off). An unmasked exception (invalid/divide-by-zero/overflow/
underflow/inexact/denormal trap) is outside the model; the validator
requires masked exceptions in the hardware profile and refuses images
whose entry path unmasks them. Denormal-operand and inexact traps on
newer CPUs (if exposed) fall under the same refusal.

The MXCSR sticky status flags (IE/DE/ZE/OE/UE/PE, bits 0–5) are part of
the machine state in the relation and are RESERVED, not matched: the
correspondence either carries them as unobserved (no `STMXCSR` or other
reader in the validated image observes them; handlers do not read them —
proved per image) or matches them exactly. The concrete case is SNaN
quieting: hardware raises invalid and returns QNaN where the model
propagates input bits — bit identity is already relaxed (§4.3), and the
raised flag is covered only by this reservation. A correspondence that
ignores the sticky flags while a reader exists is false and refused.

### 4.3 Ordering obligations that survive lowering

- **The f32 bridge is missing: binary32 validation is REFUSED until it
  is proved.** The model computes every `Ty.fl` node in binary64
  (`Typen.lean:79-82`); genuine `f32` arithmetic (single rounding at 24
  bits) DIFFERS numerically from binary64-then-narrow in general — no
  lowering convention ("compute in the node's width") and no
  innocuous-double-rounding paragraph (`53 ≥ 2·24 + 2`, cf.
  `emit.rs:17381-17390`) makes the binary64 correspondence true. Two ways
  to close, both phase-B work with a reviewed statement diff where marked:
  (a) a source-width model extension (the model computes `f32` nodes in
  `f32`, the width threaded through `Ty.fl`/`GFloat` — a reviewed
  `Spec.lean` diff, since the goal statement's float definitions move); or
  (b) a proved representation/refinement for an explicitly defined
  supported fragment (e.g. a characterised set of node shapes on which
  binary64 evaluation followed by one `float` rounding provably equals
  single-`f32` rounding — the double-rounding condition as a *proved
  lemma over stated shapes*, not a paragraph). Until (a) or (b) is proved,
  the validator refuses every `float` (`f32`) node at exactly this bridge;
  `f64` nodes alone are validatable. The per-form table (§4.1) marks each
  `SS`/`float` half accordingly: proposal only, no correspondence claimed.
  The decimal-literal path is refused with the rest: the `f`-suffix rule
  becomes an encoding check only after the bridge exists.
- **Comparisons are total in the source, partial in silicon.**
  `fllt/flle` never see NaN (finite by type) — but the lowering still
  implements the NaN row (`false`) because `gleitPasst` admits only
  finite values while the *machine* words can carry NaN after a fault the
  model files as `logik bereich`. The `false`-on-NaN row is load-bearing
  for `fle`-based range gates.
- **NaN payloads/quiet bit: relaxation only via proved
  non-observability.** The claimed relation is class-level (nan vs not),
  never payload-level — but this relaxation is OPEN until proved, not
  asserted: phase B proves a non-observability lemma over
  source-observable behaviour and goal contracts, namely (i) no NaN
  inhabits `Gleit lo hi` (every value-producing form gates on
  `gleitEndlich`/`gleitPasst`; NaN takes `logik bereich` or the `else`,
  never a value), (ii) `flt/fle` answer `false` on any NaN operand, so a
  payload never decides a branch. The model itself propagates input bits
  (`add`: `| .nan, _ => a`), so the permission is conditional on the
  current refusal of every bit-observing form (floats in memory read as
  integers — refused/uncovered, §10 item 1); admitting such a form
  re-opens the lemma. A certificate that pins a payload claims more than
  the relation permits and is refused; a test that distinguishes payloads
  is a harness probe, not a corpus file. The quiet-bit case (an SNaN input
  quieted by hardware with the invalid flag raised) is covered jointly by
  this lemma (bits) and the sticky-flag reservation (§4.2 traps): neither
  half alone suffices.
- **Signed zero is observable:** `+0 = -0` for `fle`, distinct results for
  `add/mul/div` per §6.3 table. Constant folding, CSE and spill/reload
  must be sign-exact (`-0` reloads as `-0`).

---

## 5. Later SIMD: admission-gated, never implicit

Default: scalar only. Each of the following is a separate extension with
(i) a CPUID availability premise in the hardware profile (§8),
(ii) a `Typen.lean`-pilot extension (new `Befehl` constructors — the
coordinator owns `Typen.lean`; this lane proposes, does not add),
(iii) a per-lane correspondence, and (iv) a TSO/tearing treatment:

- **Packed SSE (`ADDPS/ADDPD`, …).** Only with a proved lane-separation
  lemma: packed-lane `i` behaves as the scalar form on lane `i` with no
  cross-lane exception/flag interference, plus alignment/tearing rules
  (128-bit accesses are NOT single-copy atomic under the TSO bridge —
  ordinary 32/64-bit `MOVSS/MOVSD` aligned loads/stores are; packed
  spill/reload across a lock or publication boundary needs its own
  linearisation or is refused).
- **AVX/AVX2 (VEX-encoded scalar `VADDSS/VADDSD`, 256-bit packed).**
  Exact instruction-level semantics governs: VEX scalar forms zero the
  upper lanes (architectural — stated in the correspondence because
  caller/callee XMM sharing across calls makes it observable), legacy SSE
  forms preserve them. AVX–SSE transition penalties are performance only.
  `VZEROUPPER` placement carries NO correctness obligation absent a
  specifically demonstrated ABI upper-lane contract — it is ordinarily
  performance only and is not booked as a correctness premise here.
  Explicit AVX state obligations: the upper YMM/XMM bits are part of the
  machine state in the relation, established at entry and preserved across
  calls per a proved ABI discipline (reference: `IMAGE-ABI.md`, lane
  276); without that discipline AVX forms are refused.
- **FMA (`VFMADD132/213/231SS/SD`).** Single rounding — *different* from
  `mul`+`add`. Admit only as its own source form (new `Block` former +
  model op + checker cost + certificate); **never as a peephole
  substitution** for a `mul`+`add` pair (that would be the tightening
  lane 184 was rejected for, in a new costume).
- **`ROUNDSS/ROUNDSD`, `CVT*` with non-RNE modes, `RCPSS/RSQRTSS`.**
  The first two need an MXCSR/mode premise per use; reciprocal
  approximations are never a substitute for division (different
  rounding, no exact-result theorem).
- **BMI (`PDEP/PEXT`, `TZCNT/LZCNT`)** for bit work: orthogonal to
  floats; listed only to fix the boundary — float lanes may not silently
  widen into a BMI profile.

Refusal posture: an image containing a packed/AVX/FMA encoding while the
hardware profile admits scalar-SSE2 only is refused. `F006`-style: unknown
float widths/encodings are named refusals, not silent `double`s
(`emit.rs:6682-6693` precedent).

---

## 6. Time: three levels, exact Ziel reading

### 6.1 Level 1 — model steps (what `ZeitAb` says, no more)

Exact conclusion (`Spec.lean:1894-1900`):

> `ZeitAb P O passes M`: for every thread `f`, function `g`, depth `n`,
> environment `rho`, entry world `s0` and stack depth `k`, if
> `rufTief P (n+1) g = true` and `Eintritt P f g rho s0 k M`, then on every
> run `run : SegLauf P O passes M M2` with `aktivVor f k run`,
> `segZaehle run f ≤ kostenTief P passes (n+1) g`.

Over GX (`Spec.lean:2210-2215`): `ZeitAbX` is the same with
`SegLaufX`/`aktivVorX`/`segZaehleX` (weak memory answering the shared
atomics). `ZielX.zeit` (`Spec.lean:2238`) carries it.

What it counts (`KostenG.lean`): firings of `RufSchrittG P O passes M f M'`
with the frame's thread `f` as actor, while the frame is on `f`'s stack
(`segZaehle`: other threads' steps contribute 0). The bound is proved by a
potential argument (`potRest`, `schrittArt` over all 72 rules: head move
drops ≥1; push hands the callee at most the counted `c g`; pop drops a
frame of potential ≥1; `eintritt_start/push`, `kinv_*`, `rahmen_schritte`).

WEAK by header design (`Spec.lean:1233-1237`): holds for every program of
G with no premise (`frame_schritte_beschraenkt`); says nothing about
waiting, recursion, indirect calls or `forever`; not the declared `costs`.
Sibling targets: `frame_schritte_beschraenkt_tief` (via `Tief`),
`kosten_passt_deklaration` (declared table over a closed list,
`kostenPasst` Bool), `frame_schritte_pruefer` (checker number + remainder
`zusatz`), `fremd_budget_erhalten` (`kostenTiefF`, foreign edges count
`1 + fa`, no zero slip — drop-in right-hand side for `ZeitAb`;
`FortschrittG` untouched since foreign edges are `blatt` steps,
`schrittArt` case A).

Deliberately NOT in the bound (do not invent premises):

- **Waiting.** A step that cannot fire is no step (`dannLocks` needs the
  lock free at every other thread; `dannAwaits` needs the oracle's
  `sichtbar`). Waiting time is a SCHEDULER ASSUMPTION — fair scheduling
  plus bounded lock hold — proved nowhere; `Deklaration` has no hold
  field (the surface `held <= N ops` / `K002` never entered the model),
  so no waiting bound is stated (TARGET 4 not done). The x86 plan must
  not "close" this with an OS/fairness assumption smuggled into a
  template: any waiting bound needs a reviewed `Spec.lean` diff first.
- **Termination.** The theorems bound steps *until* the return; they do
  not say the frame returns (unfreed lock, invisible payload, exhausted
  `passes`, `logik`/`hardware` leaf, `leave`/`next` end).
- **Recursion / indirect calls.** Recursion is bounded only if admitted
  (`rufTief` depth or `kostenPasst` over a closed list — a direct cycle
  fails the check); indirect calls (`callInd`, `bindCallInd`) are
  EXCLUDED (`rufeS` false; Lean signature carries no cost — F8).
- **`forever`.** Bound relative to the machine budget `passes`, which the
  surface language never names (`per_pass` bounds one pass;
  `K003`/`Unbekannt`).

### 6.2 Level 2 — checker/certificate costs (ops, not steps, not cycles)

`kosten.rs`: `1 op = one Gabbro primitive` (assignment, arithmetic op,
load/store; §7 SPRACHE.md); a call counts the callee's declared `costs`;
branches take the maximum; `traverse` counts body × domain bound; `retry
… bounded N ops` costs `N` with `K006` checking one pass (F2 gap: `N` does
not bound the loop unless the lowering enforces the ops budget at run
time); `forever` has no total (`Unbekannt`, `per_pass` only — F3).
`KostenG.lean` §11 relates the two units the honest direction:
`kostenStmt ≤ kostenKS + zusatzS` (`spiegel_*`), with findings F1–F9
(target-place indices, `LetSonst` predicates, `narrow` subjects,
`traverse` invariants, `decreases` self-calls, indirect calls, constant
folding). Float rows exist on the Lean side (`kostenBlock`:
`.gleit 2+a+b`, `.gleitLit 2`, `.gleitVon 2+e`, `.gleitNarrow
2+e+max(…)`; `kostenKB` mirror `2/1/2/1`; `zusatzB` `0/1/0/3+e+…`;
`rufeB` passes through; `spiegelB` includes all four; `fremdBlock`
passes through).

For x86: the certificate carries the *machine* cost per source form; the
validator checks it the way `korrOk` checks rows (decidable Bool,
soundness theorem to `segZaehleX`). The checker number is an input to
that certificate, never a cycle bound.

### 6.3 Level 3 — hardware timing (processor-dependent, unproved here)

Instruction counts — model steps and certificate costs alike — are NOT
execution-time bounds (`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3: "Preserve
the model's declared costs with validated machine costs and named
hardware bounds; instruction counts alone are not execution-time
bounds"). A wall-time claim needs, per hardware profile (§8): a validated
per-instruction (or per-sequence) cycle summary, cache/TLB/branch-
predictor treatment (or explicit exclusion with refusal of the
unmodelled case), frequency/TSC discipline, SMM/NMI/hypervisor exclusion
or bound, and contention treatment for shared resources. **None exists
today; §8 marks every such bound UNPROVED.**

### 6.4 Progress (exact, preserved as is)

- `FortschrittG` (`Spec.lean:1828-1831`), `FortschrittF` (thread machine),
  `FortschrittFX` (over GX): every stop named; float failures are user
  logic (`bereich`), not a stop (§3).
- `KeinWarteZyklus` (`Spec.lean:1840-1842`): no lock-wait cycle whatever
  other threads do (verdict F2).
- `KernHaltE` (`Spec.lean:1887-1891`, carried by (a)): no same-core
  interrupt deadlock under `KernPlan` for declared handlers.
- `FortschrittG` needs no new stop kind for foreign edges (they are
  `blatt` steps) — and none for float ops either: every `Block.gleit*`
  head either steps (`w_gleit*`), takes the `else`, or is a user-logic
  `bereich` refusal. `FortschrittG` is ENABLEDNESS, not eventual progress
  (revised lane-274 reading, adopted here): a thread that can step
  satisfies it, however many steps occur — arbitrarily many enabled retry
  iterations do not violate it, and even a forever-spinning retry loop
  satisfies it. The exact source conclusion is preserved as stated; no
  termination proof is demanded by `FortschrittG`. What a
  lowering-introduced machine loop (e.g. a CAS retry, §7) DOES need is
  separate: (i) finite-expansion correspondence — machine steps project
  onto model steps, and stuttering/internal steps carry a proved progress
  argument (they cannot vanish in projection); (ii) machine-work/time
  bounds as their own obligations (§8.1) — unbounded retries cannot hide
  behind a constant per-op cost. Divergence beyond enabledness is a matter
  for those separate obligations, never smuggled into `FortschrittG` and
  never discharged by an invented fairness/OS premise.

---

## 7. Cost/progress transfer under optimisation (starter package)

Shared rule (wave contract): preserve faults, IEEE behaviour, concurrent
observations, progress and cost guarantees. For floats specifically: a
float op is **faulting** (invalid/divide-by-zero/overflow/underflow/
inexact flags; `logik bereich` at the model level) and **order-sensitive**
(non-associative, rounding at every op). Optimiser legality must treat
float code accordingly. Per family (lowering, register allocation and the
chosen processor profile are untrusted; certificates carry the proof):

- **Constant/copy propagation.** Into/through float code only if
  bit-exact (incl. ±0; NaN class per the §4.3 relaxation, OPEN until
  proved) AND flag-identical (no new invalid,
  no dropped overflow that changes a `bereich` outcome). Propagating a
  narrower/wider constant (`float` vs `double` bits) is a width change,
  refused. `bruch` constants are correctly-rounded literals — folding
  must reproduce `rundeBruch`, not the host's `strtod`.
- **Dead-code elimination.** A float op is dead only if its result,
  its flags AND its `bereich` outcome are all unobservable. Removing a
  faulting op (e.g. `0.0/0.0` whose NaN is "unused" but whose
  `logik bereich` fires) is unsound. Same for `isfinite`/`narrow` checks.
- **Common subexpressions.** `a+b` computed once and reused is sound only
  if the shared evaluation has exactly the source rounding/flags at both
  use sites (same widths, same MXCSR premise, no intervening mode change)
  AND the `bereich` fate at both sites coincides (a shared value inside
  one site's range but outside the other's changes the second site's
  outcome — CSE across different `lo..hi` gates is refused).
- **Selective inlining.** Re-runs the potential argument: the caller's
  counted `c g` is replaced by the callee body's cost at the call site;
  `rufTief` depth, `kostenPasst` closure and the certificate's cost
  summary are recomputed and re-checked. Inlining is never cost-free;
  recursion admitted by depth may become inadmissible after inlining
  (and vice versa) — the check decides, not the optimiser.
- **Register allocation / spills.** Spill loads/stores are thread-private
  (fresh frame slots): prove no new races/footprints (they never change
  another thread's state — the `rufSchrittG_fremd` shape). Cost: spills
  ADD steps (potential must cover them — the certificate's per-site spill
  count). Float spills must be bit-exact: spill via integer moves
  (`MOVQ`/`MOVSS` store + reload) preserves all bits; spill via
  conversion (`CVT*`) or via a wider/narrower slot re-rounds and is
  refused. XMM pressure may not leak values across calls (ABI doc owns
  caller/callee-saved XMM discipline).
- **Peephole / instruction selection.** One source op = one machine op
  (§4.1 table). Forbidden peepholes (refused by the validator, not
  "unprofitable"): fusion to FMA; `x-x → 0`; `0*x → 0`; reciprocal/
  `RSQRT` for division; `float↔double` width change; `UCOMI`→ordered-
  compare swap that mishandles NaN; `CVTT` without the saturation wrapper
  for `gleitRoh`.
- **Loop-invariant motion.** Moving a float op out of a `traverse`/`retry`
  body changes the number of roundings/flags raised (0 or 1 vs N) and may
  hoist a `bereich` failure out of a loop that never reaches it (or sink
  one into it). Allowed only with a motion certificate: loop-invariant in
  the exact-value sense (not just the rounded-value sense — `a+b` with
  loop-varying rounding contribution is not invariant), fault-equivalent,
  and cost-covered (moved cost counted at the hoisted site, loop body
  cost recomputed).
- **Bounded unrolling.** Unrolling multiplies body cost by the unroll
  factor in the certificate; the `traverse` domain bound
  (`(D.count t).toNat`, `alleIndizes_length`) still governs trip count;
  remainder handling must preserve the last-iteration `bereich`/flag
  behaviour (unrolled tail is not "the same ops" if it drops the final
  range gate).
- **Selective SIMD (§5).** Scalar→packed vectorisation of float loops is
  a semantic extension (lane separation + alignment/tearing + flag
  treatment), never a pure optimisation; certificate per loop.
- **Calls.** As §6.1 push/pop accounting; indirect calls stay excluded
  until a cost-carrying pointer-type discipline with a reviewed statement
  diff exists (F8). Foreign/syscall edges count `1 + fa` (`fremd_*`;
  `fa` is a Lean parameter — the `costs`-on-`syscalldecl` grammar gap,
  lane-114, stays open and is NOT closed by assuming a number).
- **Retry loops (atomics, `cmpxchg` lowering).** Success/failure have
  distinct effects; x86 `CMPXCHG` has no spurious failure — the lowering
  must not import LL/SC-style spurious-failure semantics. A retry loop is
  a new machine-level loop with no source-level trip bound. Enabledness
  (`FortschrittG`, §6.4) holds per iteration and needs nothing more; the
  real obligations are separate: (i) finite expansion — each attempt
  projects onto model behaviour, stuttering steps carry a progress
  argument; (ii) work accounting — the certificate counts cost per attempt
  times a PROVED attempt bound, or claims no work/time bound for that
  site. An unbounded retry behind a constant per-op cost is unsound and
  refused. Per-attempt cost times a proved attempt bound earns a WORK
  bound; turning work into a stop/runtime claim (the machine stops
  because the source budget exhausts) needs the separate
  budget-simulation obligation (§8.1), not a `FortschrittG` argument.
  Expected-case cost is not a bound (§8 marks all such bounds unproved).
  No fairness or OS premise is invented to bound contention.
- **Fences (`MFENCE`, locked ops, `pause`).** Cost counted (they are steps);
  they constrain ordering only as the TSO bridge proves (lane 274 owns the
  bridge — this lane books the float interaction: a fence placement may
  not be moved across a float observation that the source orders, and
  `pause` in a spin is waiting, i.e. outside `ZeitAb` by §6.1).
- **Interrupts / handlers.** `KernPlan`/`HandlerVon`/`KernHaltE` are
  preserved as stated. New float-specific obligation: handlers must
  save/restore the full float state they touch (XMM registers used +
  MXCSR) — the interrupted thread's rounding mode, FTZ/DAZ, masks and
  in-flight values are otherwise clobbered, which is a silent mode change
  violating §4.2(1,6,7). Lazy FPU/XSAVE state switching by the runtime is
  user/binding logic with contracts, not a hardware assumption.

Transfer obligations in one sentence: every machine loop the lowering
introduces (retry, unrolled-tail fixup; spill-fill sequencing is
straight-line) carries finite-expansion correspondence plus honest work
accounting in the certificate (§8.1) — `FortschrittG` enabledness is
preserved exactly as stated and demands no termination proof; infinite
executions are reviewed as infinite executions (order item 6 of the
validation plan), never projected away by a finite-step simulation alone,
and no fairness/OS assumption is invented to bound them.

---

## 8. Checked target cost summaries + hardware-profile data (proposal)

### 8.1 Cost summary certificate (checked, generic)

Proposed shape (phase B; names provisional, generic over every source
text — no per-program rules). All names below are SCHEMAS, unimplemented
and OPEN; the schema error of the previous revision (bounding source
`segZaehleX` and calling it machine work) is withdrawn.

Three quantities, never conflated:

- `srcSteps` — source GX steps of thread `f` while the frame is active
  (`segZaehleX run f`), already bounded model-side by `kostenTiefF`
  (`fremd_budget_erhalten`, §6.1). This bounds source steps only.
- `targetWork` — explicit count of retired target instructions of the
  validated image executed by `f`'s context in the corresponding segment
  (schema `targetWork`, OPEN: defined with the target execution
  semantics, counting retired instructions per context, minus
  exactly-corresponding waiting — see below). This is the quantity the
  certificate bounds.
- `cycles` — hardware timing (§8.2). No relation to either count is
  claimed here.

- Per function, the untrusted backend emits a cost summary alongside the
  image: per source step class (leaf, branch, lock take/release, call
  push/pop, `traverse` iteration, `retry` try, `forever` pass, float op
  class, fence, spill slot access, CAS-retry attempt) the maximum number
  of validated target instructions one source step of that class expands
  to, plus the spill/fence counts actually used and, for retry sites, a
  proved attempt bound — no constant absorbs an unbounded retry; a site
  without a proved attempt bound carries no work bound (§7).
- Lean checks the summary against the source body (schema Bool
  `kostenSummeOk EL summary P fs`, OPEN) and proves the soundness schema
  (OPEN): if the check holds, then for every GX run `run`, every target
  execution `xrun` with `XCorr run xrun` (the target refinement relation —
  decoder + per-access bridge + layout, owned by the decoder/bridge
  lanes, OPEN here), and every active frame segment of `f`,
  `targetWork (segment xrun f) ≤ expandBound summary (kostenTiefF …)` —
  i.e. the summary bounds lowered MACHINE work via the validated
  expansion over the source budget, not source steps by re-summing.
- Waiting/spinning exclusions need exact source correspondence, proved per
  site in the certificate: machine waiting counts as excluded from
  `targetWork` ONLY where it corresponds exactly to source-level
  non-firing (`dannLocks` with the lock held elsewhere, `dannAwaits`
  with an invisible payload — waiting is not steps in G either, §6.1). A
  lowering-introduced spin with NO source counterpart (CAS retry loop,
  backoff/`pause` loop) is never waiting-excluded: every attempt counts
  in full, hence the attempt bound. The CAS retry bound cannot disappear
  into an exclusion or a constant.
- Source-budget accounting is a SEPARATE open obligation (schema
  `budget_simulation`, OPEN): relating machine work to the model's
  `passes`-budget consumption so that budget exhaustion on the machine
  simulates the source `budget` stop. Re-summing the expansion over
  `kostenTiefF` proves a work bound, never a runtime/stop claim — the
  machine has no `passes` counter, and no runtime bound is claimed from
  re-summing.
- Status: **proposed, not built, not proved** — the Bool, the refinement
  relation instance, `targetWork`, `expandBound`, the per-form maxima,
  the per-site exclusion proofs, the attempt bounds and
  `budget_simulation` are all phase-B work (§10).

### 8.2 Hardware-profile data (concrete, bounds unproved)

Concrete data the profile must carry before any cycle claim (all cycle/
time bounds **UNPROVED** — proposal only):

- CPU identity and mode: 64-bit execution; CPUID vendor/family/model/
  stepping; required feature bits (SSE, SSE2 baseline; AVX/FMA only if
  §5 extensions admitted, with their availability bits named);
  microcode version if the platform exposes it (else the bound is
  explicitly microcode-conditional — still unproved).
- FP control: MXCSR value ESTABLISHED at image entry (checked,
  §4.2.1); `RC = 00` (RNE), `FTZ = 0`, `DAZ = 0`, all exception masks
  `= 1`; enumerated `LDMXCSR`/`STMXCSR` sites with checked preserves
  (§4.2.1/7); sticky status flags reserved as unobserved-or-matched
  (§4.2 traps); XMM + upper-YMM save/restore discipline across
  calls/handlers (reference: `IMAGE-ABI.md`, lane 276). Per-context
  reading throughout: entry/context-switch save/restore is binding logic,
  silicon behaviour under the entry value is hardware.
- Memory/timing: cache hierarchy, TLB, prefetcher and branch-predictor
  treatment — either modelled with a validated bound or explicitly
  excluded (with refusal of images that depend on the excluded case);
  TSC/APIC-timer frequency source and its trust basis; SMM/NMI/
  hypervisor/DMA interference either bounded or excluded by a named
  hardware premise. **Every entry in this bullet is UNPROVED.**
- Existing anchors to reuse (C backend, regression only): the two
  manifest assumptions (`gleitkomma_rundungsmodus_ist_rne`,
  `gleitkomma_x86_rechnet_mit_sse2`), the `FLT_EVAL_METHOD == 0` assert
  ancestry, the `fp_contract off` profile key (`ProfilSchluessel.
  fpKontraktion = aus`, `Profil.lean:21-30`, witness
  `zeugeKontraktionAus = 0`). For x86 the key binds validator refusal of
  fused encodings, not a compiler flag.

---

## 9. Phase-B definitions/lemmas (generic, provisional names)

All quantify over arbitrary supported programs/layouts; per-program
instances are witnesses only. The coordinator owns `Typen.lean` central
integration; this lane proposes.

- Float machine state + per-op correspondence: `Befehl` constructors for
  `ADD/SUB/MUL/DIVSD`, `UCOMISD`, `CVTSI2SD`, `CVTTSD2SI`, `MOVSD`
  (`SS`/`float` constructors PROPOSED ONLY — refused pending the §4.3 f32
  bridge); XMM file + MXCSR word with RC/FTZ/DAZ/mask projections AND
  reserved sticky status flags; `float_op_corr` per `GleitOp` under the
  x86 `gleitkomma_ieee` analogue + `wf` premises, f64 only;
  `narrow_corr` for both `gleitNarrow` shapes; `roh_corr` for the
  saturation wrapper; `nan_payload_unbeobachtbar` (payload relaxation from
  source-observable non-observability — OPEN, §4.3) with the sticky-flag
  reservation as joint premise.
- Decoder refusals: x87, FMA, packed/AVX-unless-admitted encodings;
  `LDMXCSR`/`STMXCSR` enumeration with unlisted writers refused.
- Control-state chain: `establish_mxcsr_entry` (entry establishes the
  required value, checked) + `preserve_ldmxcsr` (every enumerated writer
  re-establishes it, checked) — per execution context, save/restore as
  binding logic.
- TSO float instances (with lane 274's bridge): single-copy atomicity of
  aligned 32/64-bit `MOVSS`/`MOVSD` vs non-atomicity of 128-bit packed
  accesses; spill-slot privateness (frame slots never change another
  thread's state).
- Cost summary (all schemas, OPEN): `kostenSummeOk` Bool + soundness
  schema bounding `targetWork` of a corresponding `xrun` segment by
  `expandBound` over `kostenTiefF` — retry sites carry proved attempt
  bounds, never a constant for the unbounded; waiting exclusions carry
  exact source correspondence per site; `budget_simulation` (machine work
  to source-budget exhaustion) is a further separate schema, never a
  re-summing corollary (§8.1).
- Handlers/entries: XMM+MXCSR save/restore as binding-logic contracts;
  lazy XSAVE correspondence; entry-state + upper-YMM obligations (§5 AVX).
- Witnesses: concrete operand/memory witnesses for every helper; a
  jointly inhabited non-degenerate source-program witness for every
  source-syntax theorem (wave rules).

## 10. Blockers (each OPEN)

1. **f32 bridge — REFUSAL until proved.** Needs path (a) (source-width
   model + reviewed `Spec.lean` diff) or (b) (proved fragment
   refinement); until then every `float` node is refused (§4.3).
2. **NaN relation.** `nan_payload_unbeobachtbar` + sticky-flag reservation
   unproved; any bit-observing form re-opens the lemma (§4.3).
3. **Control-state dynamics.** Checked establishes/preserves unbuilt;
   FTZ/DAZ, fast-math and the writer/reader enumeration have no falsifier
   (GLEITKOMMA.md §5 items 5–7).
4. **Concurrency edges.** Per-access TSO float atomicity/tearing, fence
   placement vs float observations, finite expansion of retries, spill
   privateness — phase-B proofs. (`FortschrittG` enabledness is NOT the
   gap; work bounds are.)
5. **`kosten.rs` vs `kostenK`.** The gleit rows of the §11 reading were not
   re-verified against the Rust arms by name (first-pass finding, kept).
6. **Timing.** No validated cycle bound; all §8.2 profile data unproved.
7. **Pilot.** `X86/Typen.lean` has no float instruction (coordinator owns).
8. **Budget simulation.** `XCorr`, `targetWork`, `expandBound` and
   `budget_simulation` are unbuilt schemas; no runtime bound follows from
   re-summing (§8.1).

## 11. Verification log

| Check | Result |
|---|---|
| Isolation (`pwd`, toplevel, `muse/278`) | pass, before any edit |
| Owned files only (`FLOAT-ZEIT.md`, report) | pass — nothing else touched |
| `X86/Typen.lean:53-68` — no float `Befehl` | confirmed by direct read |
| `ZeitAb`/`ZeitAbX` statements + zeit-weak note (`Spec.lean:1894-1900, 2210-2215, 1233-1237`) | quoted exactly |
| `FortschrittG` enabledness shape (`Spec.lean:1828-1831`) | disjuncts incl. `∃ M', RufSchrittG …` — enabledness, no liveness claim |
| `Gleit lo hi` gates NaN out (`Typen.lean:111-114`, `Semantik.lean:351-352`) | basis of the §4.3 lemma shape (lemma itself OPEN) |
| Model NaN-bit propagation (`Gleitkomma.lean:226-237` add arms) | confirmed — hence the conditional permission |
| Review findings 1–5 | each addressed in §§4.2.1/3/7, 4.1 table note, 4.3, 5, 6.4, 7, 8.1/8.2, 9, 10 |
| Cost-summary schema repair | §8.1 soundness rewritten to `targetWork (segment xrun f) ≤ expandBound summary (kostenTiefF …)` over `XCorr`; source steps / machine work / cycles separated; exclusions need exact source correspondence; `budget_simulation` separate and OPEN |
| Lean / cargo / emission runs | none — docs-only task, file/claim checks per wave rules |

What this lane did NOT do: no Lean code, no build, no baseline
measurement; line numbers as-read at write time and may drift; every
proof obligation above stays OPEN until phase B proves it.
