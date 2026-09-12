# Bits, widths, shifts, intrinsics, floats -- decisions before the build

*Written 2026-09-12 after a review by the folder owner. Design decisions; nothing is built.
Companion to `dokumente/PLAN-SYSCALL.md`.*

## 0. The rule for every new error class

"The grammar does not admit the error" carries cleanly for error classes with finitely many
forms (a missing match arm, use after free, shift width, uninitialised use). Properties that
depend on run-time values -- `i < len`, a zero divisor, recursion depth -- leave three ways,
and each class needs a deliberate choice:

1. **a run-time check with an error value** -- `narrow … else`: solver-free, visible in the
   control flow;
2. **constructions that make the check structurally unnecessary** -- iteration instead of
   indices, non-zero types, capacity-indexed containers, intrinsics with a result range;
3. **values in the type** -- index types bound to a concrete length (`index into T`).

**Order of search, binding for every new construct:** first a formulation in which the error
is not expressible; then a construction (2); then a value in the type (3); only then a check
(1). The choice is recorded per error class. `index into T` plus `narrow` at entry is 1 and 3
mixed; the intrinsics below are 2.

## 1. `uN` / `iN` -- first, because two later items hang on it

`u13` is SUGAR for `u16 in 0 .. 2^13 - 1`, `i37` for `i64 in -2^36 .. 2^36 - 1` (the next
standard width stores it). In Lean it needs no new core notion (`Ty.int 0 (2^N - 1)`). Packed
layout in tables and formats places exactly N bits; the emitter already reads fields by shift
and mask (`emit.rs`:4243). The emitted C uses no `_BitInt` (CompCert has none): the next
standard width, masked where wrapping is asked for.

## 2. Shifts

* **The shift amount is typed** `0 ..< w` -- a premise of the constructor, exactly like
  `Expr.div`'s `1 ≤ l2`. This aligns the Lean grammar with the Rust checker, which already
  refuses a width outside the range (`typen.rs`:784) and on which the UB inventory row "shift
  by ≥ width" (`BEWEIS.md` §2) rests. Today `Zahl.shl`/`shr` (`Typen.lean`:284/302) admit any
  non-negative amount; `0 << 40` is derivable in the grammar and undefined in C.
* **Dynamic left shift is the hard case.** With `s : 0 ..< 32` the range of `x << s` is
  `0 .. hi · 2^31`, which exceeds any storage width at once. Under "overflow is impossible by
  construction" a dynamic left shift is usable only as `<<%` on `uN` (mod 2^N, §4). A static
  amount keeps the exact range.
* **Right shift: two operations.** `>>` stays the logical shift on non-negative operands (as
  today). An arithmetic shift is a separate, explicit operation on signed operands (`sar`),
  never implied by the signedness of the operand.

## 3. Intrinsics -- the zero case lives in the argument type

No convention like `clz 0 = w`: with `clz : 0 .. 32`, `31 - clz(x)` has range `-1 .. 31`, and
the index derivation breaks exactly on the case the convention introduced.

| operation | signature (per width w) | note |
|---|---|---|
| `clz`, `ctz` | `(x : 1 .. 2^w - 1) -> 0 .. w - 1` | argument non-zero, like a divisor |
| `log2_floor` | `(x : 1 .. 2^w - 1) -> 0 .. w - 1` | offered directly, so callers do not rebuild it from `clz` |
| `popcount` | `(x : uN) -> 0 .. w` | defined on every value |
| `rotl`, `rotr` | `(x : uN, s : 0 ..< w) -> uN` | need a width, hence `uN` only |
| `bswap` | `u16`, `u32`, `u64` | |
| bit reverse, extract/deposit | later | |

The lowering reaches `__builtin_clz` only with a provably non-zero argument, so its undefined
zero case is unreachable. **The Lean definitions are parametric in `w` from the start**
(`Zahl.clz (w : Nat) (x : Zahl 1 (2^(w+1) - 1)) : Zahl 0 w` -- the width is carried as `w + 1`, so no `Nat` truncation can turn `w - 1` into a silently wrong bound at `w = 0`): the surface spells them per
width until generics exist, and later parametrisation is a substitution, not a rewrite.

## 4. Overflow forms

* `+%`, `-%`, `*%`, `<<%` exist **only on exact `uN` ranges** (`0 .. 2^N - 1`): mod 2^N is free
  in hardware. On a range like `0 .. 5` wrapping would be ambiguous (mod 6 costs a division
  per operation), so it is not derivable there. The existing field attribute `wrapping` is
  already width-based (`SYNTAX.md`:993) and stays.
* `+|` (saturating) is well defined on **every** range -- clamp to `lo .. hi` -- and does not
  need `uN`.
* Default unchanged: an operation without a suffix must fit its range by construction.

## 5. Floats -- four parts, measured on this machine (GCC 16.2.1, Clang 22.1.8, 2026-09-12)

| | GCC 16 | Clang 22 |
|---|---|---|
| `#pragma STDC FP_CONTRACT OFF` under `-std=c11 -Wall -Wextra -Werror` | **breaks the build** (`-Wunknown-pragmas` is in `-Wall`) | accepted |
| contraction inside one expression (`a*b+c`), ISO mode, `-mfma` | off | **on by default** |
| contraction across statements (`p = a*b; return p+c;`), `-mfma` | only under `-std=gnu17` | only under `-ffp-contract=fast` |
| the pragma takes effect | not implemented | yes, except under `-ffp-contract=fast` |

Without `-mfma` the x86_64 baseline has no FMA instruction at all; with it (or `-march` of any
recent CPU) both compilers contract. The lowering "one effect per statement" does NOT protect:
GCC in GNU mode contracts across exactly that form, and Clang contracts within one statement.

1. **Prelude: no pragma at all** (revised 2026-09-12 after the build). The first plan put it
   under `#if defined(__clang__)`; measured afterwards, that added `#pragma` -- a form on the
   NEVER list of the C-form census (`instrumente/zaehle-c-formen.py`) -- and it carries nothing
   items 2 and 3 do not already carry.
2. **Manifest, binding:** `-std=c11` (ISO, never `gnu*`) **and** `-ffp-contract=off`, for every
   compiler. `-std=c11` is already the emission check line.
3. **Evidence, not intention -- a build-time probe:** a triple where the fused and the separately
   rounded result differ, in the emitted two-statement shape, with `volatile` inputs so nothing is
   folded: `a = 1 + 2^-27`, `b = 1 - 2^-27`, `c = -1` gives `a*b = 1 - 2^-54`, which rounds to
   `1.0` (tie to even), so separate rounding yields `0` and a fused multiply-add `-2^-54`. The
   probe is compiled with the manifest's flags and run at build time; any result but `0` fails
   the build. This, not the pragma, carries the claim.
4. **Excess precision, unconditional:** `_Static_assert(FLT_EVAL_METHOD == 0, ...)` on EVERY
   target, x86_64 included -- measured: `__FLT_EVAL_METHOD__` is `0` by default and `2` under
   `-mfpmath=387` and under `-m32`, flags someone may set for unrelated reasons. `== 0` also
   excludes `-1` (indeterminable). This replaces the prose assumption "SSE2 instead of x87".
5. **libm:** not in the language today. If `sin`, `exp`, `pow` ... are ever admitted, each is either
   a shipped correctly-rounded implementation, or a named assumption whose manifest entry records
   the libm and its version.

## 5b. Signed operations in C -- pin implementation-defined behaviour, never rely on it silently

* **`sar`:** a right shift of a negative value is implementation-defined in C11/C17 (and, as far
  as this folder knows, still in C23, which mandated only two's complement representation; C++20
  is the standard that defined the arithmetic shift). Implementation-defined -- unlike undefined
  -- is fixed per implementation, so the prelude pins it:
  `_Static_assert((-1 >> 1) == -1, "arithmetic right shift");`
  and the conversion back from unsigned:
  `_Static_assert((int)0xFFFFFFFFu == -1, "modular conversion");`
  Both compile under GCC 16 and Clang 22 with `-Werror`. The standard stays C11.
* **`+%`, `-%`, `*%` exist only on `uN` (§4), and that is the reason, not a coincidence:** signed
  overflow is undefined in C, and the conversion back from unsigned is implementation-defined.
  Wrapping on unsigned C types is defined behaviour.
* Same mechanism as the `clz` zero case: the C level has an undefined or implementation-defined
  edge, and Gabbro either makes it unreachable or pins it at build time.

## 6. Compile-time evaluation -- measure the certificate before building

The plan is right: the checker evaluates the total, effect-free fragment, prints the result as
a certificate, and Lean re-checks it. The cliff: `decide`/`rfl` over a large table runs
through kernel reduction and becomes unusably slow; page-table walks are the size where it
tips. `native_decide` would add the Lean compiler to the trusted base and is excluded.

Certificates are therefore **lists of explicit entries checked entry by entry** (`List.all`
over entries with a `Decidable` instance, arithmetic on `Nat` literals, which the kernel
evaluates efficiently), never a definitional comparison of whole tables. **Before item 6 is
built, one measurement lane** checks a table of realistic size (a four-level walk with 512
entries per level). It compares two encodings -- the certificate predicate on bare `Nat`
literals with the range proofs attached afterwards, versus entries as `Zahl` values carrying
their proofs (which leaves the kernel's fast `Nat` path through projections) -- and records,
separately, elaboration time and memory, kernel-check time and memory, and the size of the
proof term. **Fallback, planned now:** cut the certificate into blocks checked one by one; it
bounds memory even where total time stays the same. The measurement decides whether it is
needed.

## 7. Order

One wave for the small, connected items, in this order: **§1 `uN` → §2 shift typing → §3
intrinsics → §4 overflow forms**, plus the float prelude (§5). §6 starts as a single
measurement lane. Generics get a plan document later; the intrinsic signatures of §3 are
already written so that parametrisation over `w` is a substitution.
