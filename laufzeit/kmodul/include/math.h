/* laufzeit/metall/include/math.h -- the <math.h> of the bare-metal image
 * (Opus agent J, 2026-09-26).
 *
 * WHY THIS FILE EXISTS. Every emitted unit includes <math.h> (the prelude in
 * `emit.rs`, `KOPF`), and <math.h> is NOT one of C11's freestanding headers:
 * a freestanding toolchain without a C library has none. `gcc -ffreestanding`
 * on a hosted machine still finds glibc's copy -- a hidden libc, in headers.
 * The freestanding stage (`instrumente/pruefe-freistehend.sh`) therefore
 * compiles with `-nostdinc`: the compiler's own headers (<stdint.h>,
 * <stdbool.h>, <stdatomic.h>, <float.h>, <stddef.h>) plus THIS directory.
 *
 * WHAT IT PROVIDES: exactly the <math.h> names the emitter lowers to, and
 * nothing else -- measured over all 313 emitting units on 2026-09-26: ONE,
 * `isfinite` (the lowering of `narrow x to finite`, `CFormen.lean`). A unit
 * that needs another name fails the stage at compile time, loudly, instead of
 * finding it in a host library. `__builtin_isfinite` is a compiler builtin,
 * not a library call: no symbol reaches the linker (the stage links every
 * unit, and `ld` refuses an undefined symbol). A program's
 * `extern fn sqrt(...)` is its own foreign body and needs no header.
 */
#ifndef GABBRO_KMOD_MATH_H
#define GABBRO_KMOD_MATH_H

#define isfinite(x) __builtin_isfinite(x)

#endif
