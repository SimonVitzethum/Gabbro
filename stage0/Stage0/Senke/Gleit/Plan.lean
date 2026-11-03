/-
Design note: software IEEE-754 binary64 add/sub for `Block.float`.

Status. `lowB` routes addition and subtraction through `floatAddSubBlockL`.
The existing integer-only adder has `softAddRoutine_ok`; subtraction
flips bit 63 of the right operand with one xor before reusing that adder.
`Normal/Sub.lean` supplies `softSub_model` from `softAddComposed_model`
and the kernel's definitional `sub = add (neg right)` identity, including
NaN payloads/signs and signed zeros. `blockFloatAddSub_case` connects both
operations to `lowB_ok` with the shared rounded-result range guard and
stop 107. The subtraction extension and witnesses await the lead's Lean
checks and runner measurement. Multiplication and division remain refused.
No float opcode, runner extension or hardware assumption is introduced.

1. Kernel specification (grammatik).
   `Grammatik/Bausteine/Gleitkomma/Gleitkomma/T1/Teil1.lean`:
   `Format` (`p` significand bits, `emax`), `f64 := ⟨53, 1023⟩`,
   `GBits` (sign, biased exponent, fraction), `klasse`
   (null/subnormal/normal/unendlich/nan), `wertExakt` (finite values as
   dyadic `Exakt`), `exaktAdd`, `rundeExakt` (via `rundeBruch`, ties to
   even by `rundeInt`), `add` (NaN priority, `inf + -inf = NaN`,
   signed-zero rule), `sub` (negation + `add`), `nanQ`.
   `GleitkommaBits.lean`: the bit view `zuBits`/`ausBits`, `dicht`
   (true for f64), `ausBits_zuBits`, `zuBits_lt`, `add_wf`.
   G machine (`Kern/Semantik/Semantik/T2/Teil1.lean`):
   `gleitRechne .add a b = Gleitkomma.add f64 a b`, range-checked by
   `gleitPasst`. Already proved (`Senke/Ausdruck/Arithmetik/AddSub.lean`):
   `floatAddSpecial_model` splits `add` into the special-case dispatcher
   and the finite path `rundeExakt F (exaktAdd u v)`; `floatAdd_align`
   is the exact alignment identity both paths share.

2. Integer IR building blocks (runner/Runner/IR/Step.lean, no floats).
   Opcodes: 1 const, 2 mov, 3 add, 4 sub, 5 mul, 6 sdiv, 7 srem,
   8 and, 9 or, 10 xor, 11 shl, 12 shr (logical), 13 slt, 14 eq,
   15 ld, 16 st, 18 jmp, 19 brz, 25 udiv, 26 urem, 27 ult
   (0 and 28-255 fault). Emitters (`Senke/Ausdruck/Aggregat/Hilfena.lean`):
   `wordL`/`wordK`/`bin2` (one word op), `wennL` (branch with checked
   `2^31` displacement), `konstWL` (arbitrary words from immediates).
   Wide kernels (`BitBuiltin`, `intBuiltin2L`): multi-limb add/sub/mul,
   shifts, masks, comparisons. Existing float fragments, all with
   `WordCode` lemmas and `FloatEmission` size/ceiling bounds
   (`Senke/Ausdruck/Gleit/`): `floatMagnitudeL`, `floatExponentL`,
   `floatShiftJamL` (shift with sticky bit), `floatRoundShiftL`,
   `floatRoundL`, and the `floatRoundUp`/`rundeInt` bridge
   (`Gleit/Runden.lean`) which avoids doubling a word.

3. Decomposition of the add routine (one `WordCode` per step).
   Unpack: sign (`slt`), biased exponent (`shr` + mask `2047`),
   fraction (`and` mask `2^52 - 1`); hidden-one insertion and
   subnormal/zero handling by `wennL` over `eq` tests. Special cases:
   the `floatAddSpecial` dispatcher as nested `wennL` (NaN payload kept,
   infinity conflict to `nanQ`, signed-zero rule). Align: shift the
   smaller operand right by the exponent gap with sticky-bit jam
   (`floatShiftJamL` pattern; gaps beyond the significand width jam to
   sticky only). Add: 106-bit exact signed sum from two word ops
   (magnitude add/sub selected by the sign xor, as in `floatOfInt`
   scaling). Round: `floatRoundUp` decision on (quotient, remainder,
   denominator), proved against `rundeInt`. Normalize: exponent adjust
   with carry/overflow to infinity and underflow to subnormal/zero,
   following the `rundeBruchKern` case split. Pack: `shl`/`or` of sign,
   biased exponent and fraction into one word.

4. Proof strategy (no `sorry`/`axiom`/`native_decide`, nothing weakened).
   (a) Pure-Lean `softAdd : UInt64 → UInt64 → UInt64`
   (`Senke/Gleit/Add.lean`): decode with `ausBits`, run the kernel
   `Gleitkomma.add f64`, encode with `zuBits`; `softAdd_model` proves it
   equals the kernel operation on ALL inputs via `ausBits_zuBits`,
   `add_wf` and the `2^64` word bound, plus one kernel lemma per
   decomposition step (`softAdd_special` reuses `floatAddSpecial_model`).
   (b) The IR routine is proved to compute `softAdd` by `WordCode`
   composition (`WordCode.bin`/`const`, the `Eng` lemmas), reusing the
   `floatOfInt` emitter pattern and `FloatEmission` ceilings.
   (c) `lowB` selects the shared `Block.float` add/sub template,
   reusing `floatNarrowC` with `stop 107` on a nonfinite result or a
   range miss. Subtraction adapts only the right producer before operand
   retention; the finite arithmetic and Block proof are shared. Each layer
   carries its `_zeuge` witness and `#print axioms` check. Multiplication
   and division remain refused.
-/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
@[expose] public section
