# Float payload and exception observability in real source

*Owner: lane 604. Owns only this file plus `MUSE-REPORT-604.md`.
Status: read-only semantic audit, not a proof and not a design change.
No Lean module, checker, Spec, goal, Rust, emitter, Typen/execution/codec or
friend path is touched here. Full source-to-final-byte validation remains OPEN.*

Scope: which channels in the REAL source pipeline can distinguish
model-equivalent FP results — NaN payload, signed zero, sNaN quieting,
MXCSR/sticky observation — read against the actual typed source
syntax/checker/exporter, the GabbroV Body bridge, `X86/ScalarFloat`,
`X86/Gleitprofil`, `X86/FloatExceptions`, and the emitted C forms.
Prior float reviews (`AUDIT-FLOAT-SIMD.md` lane 412, `FLOAT-ZEIT.md`,
`dokumente/GLEITKOMMA.md` §§4-7, `CFormenF.lean`) are cited, not repeated:
every section below names file/theorem/line evidence in current code and
the concrete closure obligation it leaves. No guessed absence of language
forms: every "no channel" claim carries the code reference that closes it.

## 0. What "model-equivalent" means here

The source model (`Typen.lean:77-114`, `Semantik.lean:347-354,621-653`)
observes a float ONLY through:

- `fllt`/`flle` (`gleitLt`/`gleitLe`, `Syntax.lean:407-408`) — no other
  comparison exists in the model;
- `gleitNarrow … to finite` / range narrow (`gleitPasst`, finite + inside);
- `Block.gleit` ops held against a range (`gleitPasst`, NaN/inf = `Logik.bereich`);
- `gleitRoh` (truncation toward zero, saturated; NaN/inf give `0`).

Two float values are *model-equivalent* when all four agree on them while
their bit patterns differ. Concretely that is exactly two cases:

1. **signed zero** (`-0` vs `+0`): both finite, `flt`/`fle` agree in all
   four directions, `gleitRoh` gives `0` on both, `zuBits` differs.
2. **NaN payloads**: all `flt`/`fle` answer `false`, `gleitRoh` gives `0`.
   (sNaN vs qNaN: the model has no quiet-bit field at all —
   `Gleitkomma.lean:GBits = (sign, bexp, frac)`, `klasse` answers `.nan`
   for any nonzero fraction at max exponent.)

The audit question per case: does any REAL source channel observe the
difference — memory read as integer, Lean export, gate/binding answer,
pointer/bit reinterpretation, MXCSR/sticky read? Findings:

- **NaN payload: no value to observe.** `Val (.fl lo hi) = Gleit lo hi`
  (`Typen.lean:110-114,126`) requires `gleitEndlich x = true` — a NaN
  inhabits NO accepted value. Literals are finite decimals only (§1),
  computed NaN/inf is `Logik.bereich` (proof duty, program refused unless
  discharged), gate/oracle answers are fitted through `gleitPasst`
  (`EinpassenVoll.lean:20-21`, `gleitWortPasst`: word is binary64 bits,
  held against the range like a computed float). Non-observability holds
  by construction — provided no bit-exposing form is added (§2) and
  float `==`/`!=` is closed (§3).
- **Signed zero: observable NOWHERE in real source, one hole in the
  legacy C chain.** `-0` is finite, so it DOES inhabit accepted values;
  every model observation agrees on `-0`/`+0`. The only forms that could
  disagree are float `==`/`!=` — which have no model meaning at all (§3).
- **sNaN: unreachable in accepted programs, divergence conditional.**
  No spelling (§1), no computation (finite-only), no gate entry
  (`gleitWortPasst`). Target `fpSchritt` arithmetic wraps the model op,
  and the model propagates input NaN bits (`Gleitkomma.lean:226-229`)
  while silicon quietens sNaN on arithmetic — a bit-level divergence
  that fires ONLY on an sNaN operand, which no accepted run produces.
  The validator obligation is to keep it that way (§5).
- **MXCSR/sticky: no source channel reads or writes it.** No syntax form,
  no emitted C form, no gate template (§4). Observation would require a
  NEW form, and every new emitted form needs a machine-checked template
  (template register) — the structural block, not a proof.

## 1. Value entry: only finite values can arrive

- **Literals** (`crates/gabbro-syntax/src/lex.rs:133-139,532-611`,
  `ast.rs:585-599`): `ExprArt::Gleitkomma { bits: u64, … }` with bits
  from parsing DECIMAL text (`wert.to_bits()`). Out-of-range refused
  (`lex.rs:587` "floating point literal is out of range"). No NaN, no
  sNaN, no ±inf spelling exists — hexfloat/`NAN`/`INFINITY` have no lexer
  form (verified by read; no such arm). `dyadisch`/`gerundet` track
  exactness, not payload.
- **Literal meaning** (`Typen.lean:84-89`): `bruch q = rundeBruch f64`
  — correctly rounded ONCE. `den = 0` would be NaN, but `q` comes from
  a parsed literal or decimal range bound, never zero-denominator.
- **Computation** (`Syntax.lean:586-600`): `Block.gleit` has NO else
  branch — NaN/inf result is `Logik.bereich` (`Semantik.lean:347-350`),
  a user proof duty. `Block.gleitNarrow … to finite … else` IS the
  isnan/isinf channel (`ast.rs:1593`: "there is no `isnan` in the
  language; `narrow … to finite else { … }` IS it").
- **Gate/oracle answers**: fitted by `gleitWortPasst` through
  `gleitPasst` (finite + in range); NaN answer = `none` = refused at
  `einpassen` (`EinpassenVoll.lean:132-148`, `gleitWortPasst_voll/_wf`).
- **Consequence**: every `Gleit lo hi` in every accepted run is finite.
  NaN-payload non-observability needs no simulation — there is no NaN
  value to simulate. The lemma to write (`nan_payload_unbeobachtbar`,
  owner §6 P1) quantifies over an empty case on the source side and
  pins the TARGET side to class agreement (`fpRechne_klasse`,
  `ScalarFloat.lean:1021-1038`), which already exists.

## 2. Bit reinterpretation: refused by name, in three places

- **F005** (`crates/gabbro-check/src/m1.rs:3658-3676`): bitwise ops,
  shifts and remainder on floats are refused — "a floating-point number
  is not [a bit pattern]" (checker’s own words). Gift
  `beispiele/gift/90-gleitkomma-bitweise.gab` pins it.
- **F005 mixed** (`m1.rs:3680-3694`): float/int in one operation refused —
  "there is no conversion form". No `as` cast, no transmute, no union on
  floats exists in the grammar (verified: `ast.rs` has no such form;
  `emit.rs` `memcpy` appears only in string helpers, `emit.rs:7093-7100`).
- **Memory is typed**: slots/fields/globals carry their declared type;
  no int-alias read of a float location exists in any pass. (Float
  table fields/statics/locals exist in the CHECKER — e.g. `const TAU :
  f64`, `beispiele/26-gleitkomma.gab` — and emit as C `double`; they are
  never read as integers.)
- **Float→int conversion does not exist as a source form.**
  `gleitRoh` (`Semantik.lean:625-632`) is reachable only through `roh`
  (`Semantik.lean:635-645`), whose only float consumer is the oracle
  register-write path (`CFormenH.lean:680`, `O.regSchreib r (roh v)`).
  On finite values it is truncation+saturation — `-0` and `+0` both give
  `0`. Not bit-exposing. (NaN→`0` arm unreachable: fitted finite first.)
- **Obligation**: any future bit-observing form (float-in-memory read as
  integer, byte-blob to float, `STMXCSR` reader) re-opens the §0 lemmas
  BY NAME. This is the same acceptance criterion as `AUDIT-FLOAT-SIMD`
  §3/P1; it still holds and is now anchored in three refusal codes.

## 3. FINDING F-EQ: float `==` / `!=` is checked and emitted with no model meaning

This is the one NEW finding of this lane (code-read, needs a 5-minute
empirical confirmation by the owning lane — exact probe in §6 P0).

- **Checker accepts**: `m1.rs:3698-3700` — `if op.ist_vergleich() {
  return Typ::Wahrheit; }` with no float distinction. All six
  comparisons typecheck on floats.
- **Model has four**: `Syntax.lean` offers only `fllt`/`flle`
  (`Expr.eq` takes `.int` args, `Syntax.lean:404`). `==`/`!=` on floats
  have NO Lean term — untranslatable, not merely uncovered.
- **Emitter writes C `==`/`!=`**: `op_text` (`emit.rs:18382-18383`)
  with no float guard on the `Binaer` path; only mixed-width ARITHMETIC
  is refused (`emit.rs:18028-18042`, `BinOp::Plus|Minus|Mal|Geteilt`
  only). `x == y` on two `f64`s emits `(x == y)`.
- **No correspondence row**: `CFormenF.lean` F4 covers `<,<=,>,>=`
  only (`cFloatCmp_lt/le/gt/ge_ein`, lines 88-106). No `eq` row exists.
  `pruefe-cformen.py` classifies emitted forms; float `==` has no lemma
  to be classified under.
- **GabbroV refuses wholesale**: any duty with float binders/literals
  fails export (`lean_g.rs:Float` reason on literals, line 1306; float
  types have no `VTy` form, `g_ty`, line 625 — refused at the site that
  asked). So the bridge never sees float `==` — it is blocked there by
  accident of total refusal, not by a targeted rule.
- **Why it matters for observability**: C `==` on finite doubles is
  IEEE equality (`-0.0 == +0.0` → true). That verdict AGREES with
  model-equivalence (no model observation distinguishes them), so F-EQ
  is not an observability hole today — it is a MEANING hole: a checked,
  emitted form whose semantics exists in NEITHER model. The danger is
  downstream: any future proof that reasons about an emitted `==` on
  floats (e.g. a test oracle, a `counterexample` witness, a target
  `UCOMISD`-plus-`SETE` lowering) would reason about a form the source
  model cannot state. And the checker's own bound extraction assumes
  trichotomy under negation (`m1.rs:5600-5614`: "Gleitkomma waere ihr
  erster Verletzer" — NaN would break `!(x<y)` → `x>=y`); that
  reasoning is sound ONLY while NaN stays unreachable (§1).
- **Recommended close**: refuse float `==`/`!=` at the checker (widen
  F005 — "this operation does not exist for floating point" already
  says exactly this for the bitwise family), matching the documented
  design ("no NaN four-way compare", `GLEITKOMMA.md:19`). The
  alternative — model `fleq` + six-row correspondence + UCOMISD+SETE
  lowering proof — costs a new model constructor for a form that is
  almost always a bug at the source. Owner §6 P0. Corpus impact: zero
  of 146 `beispiele/` files use float `==` (verified by grep; only
  `03-format` and `26-gleitkomma` mention floats at all, neither with
  `==`).

## 4. MXCSR and sticky flags: no channel in either direction

- **Source**: no form reads, writes, or names MXCSR, rounding mode, or
  exception flags. `FPKontext.mxcsr` (`Gleitprofil.lean:60-63`) exists
  only on the TARGET side.
- **Emitted C**: no `fenv.h`, no `fegetenv`/`fesetenv`, no
  `_mm_getcsr/_mm_setcsr`, no inline `stmxcsr/ldmxcsr` (verified by
  grep over `emit.rs`: only the prelude comment, `_Static_assert
  (FLT_EVAL_METHOD == 0)`, and the manifest `-ffp-contract=off`
  binding). Mode assumptions are documented (`GLEITKOMMA.md` §4, seven
  named facts) with measured pins (§5 table: RNE double-pinned by
  `sonde_mxcsr_rne`, SSE2/no-over-width pinned, contraction pinned at
  build time; fast-math declared-not-probed, FTZ/DAZ NOTHING, mode
  stability NOT covered).
- **Probes read MXCSR but ship nothing**: `sonden/sonde_mxcsr_rne.c`
  reads the word at test time; `laufzeit/metall/start.S:146-150`
  (`stmxcsr`/`ldmxcsr` in `metall_schalte`) is context-switch
  save/restore — pure data movement, the machine half of
  `sichere`/`stelleHer` (`Gleitprofil.lean:68-80`). It establishes NO
  value; initial-word establishment on metal entry is an OPEN owner
  question (§6 P2).
- **Sticky flags** (bits 0–5): `mxcsrGueltig` ignores them BOTH ways
  (`mxcsr_sticky_egal_*`, `Gleitprofil.lean:98-104`); accumulation,
  clearing and reads are unmodelled (CUTS). No source form can observe a
  sticky flag — the only exception-channel is `narrow … to finite`,
  which observes the VALUE class (via `isfinite` in C, `gleitEndlich`
  in the model), never the flag. Silicon raising invalid on sNaN input
  while masking it is therefore unobservable from source — consistent
  with the profile demanding all six masks set.
- **Gates cannot smuggle MXCSR**: a gate’s observable behaviour is its
  declared contract over model values (which have no MXCSR), fitted
  through `einpassen`; any NEW gate lowering needs a machine-checked
  template (register rule). No fenv template exists. Structural block.

## 5. Target-side residue (accepted modules, for the consumer owners)

All verified by direct read; no new proof claimed here.

- **ScalarFloat** (`X86/ScalarFloat.lean`): 16 DOUBLE forms
  (`addsd/subsd/mulsd/divsd` RR+RM, `ucomisd` RR+RM, `cvtsi2sd`,
  `cvttsd2si`, three `movsd`) on the extension interface (`FpZustand`,
  old step lifted untouched). Source link is class-level:
  `fpRechne_gleitRechne` + `fpRechne_klasse`; payload equality
  explicitly OPEN (§4 header, §6 CUTS cross-filed). `cvttPaket`
  mirrors `gleitRoh` shape (invalid→0, saturate). `ucomiFlags` table
  proved incl. unordered rows (`ucomiFlags_ungeordnet_*`).
- **FloatExceptions** (`X86/FloatExceptions.lean`): guarded `fdiv64`
  under `floatGuard`; masked invalid/divide-by-zero are VALUES
  (`divEinsNull_modell`, `divNullNull_modell`); refused context refuses
  the SLOT (`none`), never a trap. Payload again class-only (CUTS).
- **Gleitprofil**: admission check + per-context state + exact
  bit-pattern round-trips (`muster64_bites64`, `zuBits_ausBits64`) +
  signed-zero/subnormal theorems + the f32-vs-f64 counterexample
  (`quelle_gegen_f32`). `SSEAdd32Entspricht` named, unproved — the
  executed-byte gap, unchanged.
- **No decoder connection**: `Codec.lean`/`DecodingCoverage.lean`
  contain zero references to `FpBefehl`/`fpSchritt`/XMM/SSE opcodes
  (verified by grep). No byte sequence decodes to a float form today;
  owner 575’s path is fully open, nothing to reconcile against.
- **sNaN quieting divergence** (conditional, unreachable): model `add`
  propagates input NaN BITS (`Gleitkomma.lean:226-229`); silicon
  `ADDSD` on sNaN raises masked-invalid AND quietens. Bit-level
  predictions differ; class predictions agree (`.nan`). Reachability
  requires an sNaN operand — excluded by §1. Validator must keep float
  image data finite IF a float-data lowering is ever added (none exists:
  float consts emit as decimal text via `gleitkommatext`, `emit.rs:
  17393-17402`, never as data words).
- **Latent emitter robustness note (not soundness)**: `gleitkommatext`
  renders `f64::from_bits` via Rust `{:?}` — a NaN/inf payload would
  emit bare `NaN`/`inf`, which is not valid C. Unreachable (literals
  finite-only, §1; `auswerten` gives `None` for float const-exprs per
  `saetze.rs:2472`), but a defensive refusal at the emitter would turn
  an invariant into a checked gate. Cheap; owner §6 P3.
- **TSO/tearing**: `movsd` goes through canonical `read64`/`write64`;
  8-byte atomicity is the SHARED per-access-bridge question
  (`WordAtomicity.lean` exists; full target-to-W/GX simulation OPEN per
  handoff). Floats add no new channel beyond 8-byte integer exposure —
  same bridge, same owner, not a float task.

## 6. Actionable ownership plan (closure of scalar source→decoded-byte)

Ordered; each item is one lane with exact acceptance. No item weakens a
guarantee; a proved obstruction must be labelled blocked, never closure.

- **P0 — Refuse float `==`/`!=` (checker lane; F-EQ, §3).**
  Widen F005 (or a new code if the register prefers) to equality on
  float operands. Acceptance: poison probe (`==` and `!=` on two
  `f64`s refused by name), corpus diff zero (no `beispiele/` file uses
  it — verified), `./cargo-pruef` green. Until P0 lands, the
  `nan_payload_unbeobachtbar` lemma (P1) must EXCLUDE `==`/`!=` by
  premise, and no target lowering may introduce `UCOMISD`+`SETE`.
  Empirical confirmation of §3 (5 min, owning lane): the two-line probe
  through `gabbro pruefe` + `gabbro emit`, expecting 0 checker errors
  today and C `==` in the output — then the refusal after the fix.
- **P1 — Source non-observability lemma (model lane; needs P0 or the
  exclusion premise).** `gleit_beobachtbar_nur_klasse`: any two finite
  `GFloat`s that agree on `flt`/`fle` in all four directions agree on
  every source observation (`fllt`, `flle`, `gleitNarrow` finite+range,
  `gleit` range-holding, `gleitRoh`). Witness: `-0`/`+0` joint with a
  memory-changing run (inhabitation rule). NaN side is vacuous
  (no `Gleit` inhabitant) — state it as a corollary, not a premise.
  Acceptance: standard axioms, `_zeuge` with a written table, CUTS
  naming F-EQ and any future bit-form as re-openers.
- **P2 — Entry establishes MXCSR; enumerate control-state forms
  (EntryState FeatureProfile owners).** Entry-establishes-`0x1F80`
  (or proven-valid word) for hosted AND metal entry (metal currently
  only saves/restores across `metall_schalte`; initial establishment
  unowned). `LDMXCSR`/`STMXCSR` refused syntactically until enumerated
  with preserve lemmas. FTZ/DAZ-setting words refused (cheapest new
  probe per `GLEITKOMMA.md` §5 row 6 — still NOTHING). Mode-stability
  across calls: state the assumption, pin what `sonde_mxcsr_rne`
  already pins, record the rest as named assumption, never as proof.
- **P3 — Emitter hardening (could ride with P0).** Refuse NaN/inf bits
  in `gleitkommatext` by name (unreachable today, §5 note); keep the
  shortest-round-trip decimal + `f`-suffix rule byte-identical
  otherwise. Acceptance: existing emission counters unchanged
  (`MARKE_EMIT*` re-measured by merger), `./cargo-pruef` green.
- **P4 — Decoder→`FpBefehl` path (owner 575’s wave item).**
  F2/F3/0F-prefix decoding to the 16 accepted forms; every other
  FP/SIMD encoding refused syntactically (x87, FMA, packed, AVX).
  Premise every op correspondence on `mxcsrGueltig`
  (establishes/preserves per P2). One source op = one machine op; the
  optimiser-reserved files stay untouched. Acceptance: exact-candidate
  review + `DecodeFault`-consistent refusal lemmas.
- **P5 — Per-op target correspondence (needs P2, P4).** Lift
  `fpRechne_klasse` to the fetched/executed bytes: finite source
  result ⇒ finite target result with equal CLASS; `ucomisd` flag rows
  ⇒ source `flt`/`fle`; `cvttsd2si` ⇒ `gleitRoh`; `movsd` ⇒ bit
  round-trip (already `muster64_bites64`). Payload equality is NOT
  claimed — P1 makes it unnecessary. sNaN-quieting divergence
  discharged by the §1 unreachability + validator finiteness of float
  image data (to be stated when a float-data lowering exists).
- **Explicit non-tasks**: hardware verification of MXCSR bit positions
  or silicon rounding; cycle bounds; `Ty.fl` width extension (separate
  reviewed Spec diff); c.NullableFloat — none exists; libm
  transcendentals (out of scope, `GLEITKOMMA.md` §4); proving
  `SSEAdd32Entspricht` from these parts alone (needs P4+P5).

## 7. Verification log

| Check | Result |
|---|---|
| Isolation (`pwd`, toplevel, `muse/604`) | pass, before any edit |
| Owned files only (this doc + report) | pass — no Lean/Rust/checker/Spec/emitter/friend file touched |
| `ScalarFloat.lean` (full read, 1154+ lines) + `FloatExceptions.lean` (213) + `Gleitprofil.lean` (653) | done, CUTS cross-checked |
| Source surface (`Typen.lean:77-134`, `Semantik.lean:340-354,615-653`, `Syntax.lean:395-411,445-449,575-600`) | confirmed by direct read |
| No NaN/inf literal spelling (`lex.rs`, `ast.rs:585-599`) | confirmed by read |
| F005 refusals (`m1.rs:3658-3694`), vergleich acceptance (`m1.rs:3698-3700`), `op_text` + Binaer path (`emit.rs:18028-18112,18382-18383`), `gleitkommatext` (`emit.rs:17393-17402`), `isfinite` narrow (`emit.rs:11020-11033`) | confirmed by direct read |
| GabbroV total float refusal (`lean_g.rs:132,276,339,625,1306`, `g_ty`) | confirmed by read + grep |
| No FP in decoder (`Codec.lean`, `DecodingCoverage.lean` zero FP refs) | confirmed by grep |
| No MXCSR/fenv in emitted C (`emit.rs` grep) ; probes test-only (`sonden/`); metal save/restore (`start.S:146-150`) | confirmed by read |
| `CFormenF.lean` F1–F7 rows (no `==` row) | confirmed by read |
| Corpus float-`==` absence (grep over `beispiele/`) | zero uses |
| Lean build / cargo / emission runs | none — docs-only audit; no code changed, nothing to rebuild |

*CUTS of this audit: F-EQ (§3) is code-read with exact lines, not
empirically executed — P0 carries the 5-minute confirmation. Line
numbers are as-read at write time; theorem/sentence names are the stable
reference. MXCSR bit positions and silicon behaviour are profile inputs,
never verified here. No hardware claim is made.*
