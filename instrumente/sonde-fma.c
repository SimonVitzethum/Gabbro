/* The FMA probe -- PLAN-BITS.md section 5, item 3.
 *
 * Claim: no fused multiply-add hides in the two-statement shape the emitter
 * writes (`p = a*b; r = p + c;`). This file IS the shape, with inputs where
 * the fused and the separately rounded result differ:
 *
 *     a = 1 + 2^-27, b = 1 - 2^-27, c = -1
 *     a*b = 1 - 2^-54, which rounds to 1.0 (tie to even),
 *     so separate rounding yields r == 0 and a fused multiply-add r == -2^-54.
 *
 * The build fails unless r == 0. `volatile` keeps the compiler from folding
 * the inputs at compile time; WITHOUT it the probe answers about constant
 * folding and not about contraction. Compiled with the manifest's flags
 * (`-std=c11 -ffp-contract=off`) plus `-O2 -mfma`, and run at build time.
 *
 * Without `-mfma` the x86_64 baseline has no FMA instruction at all, so the
 * flag is what makes the question sharp: with it, both compilers contract
 * unless told not to (measured 2026-09-12, GCC 13.3.0 and Clang 18.1.3 here;
 * PLAN-BITS.md names GCC 16 and Clang 22 on Simon's machine).
 */
#include <stdio.h>

int main(void) {
    volatile double a = 1 + 0x1p-27, b = 1 - 0x1p-27, c = -1;
    double p = a * b;
    double r = p + c;
    if (r == 0) {
        printf("FMA probe: ok (separate rounding, r == 0)\n");
        return 0;
    }
    printf("FMA probe: FUSED -- r == %.17g, expected 0\n", r);
    return 1;
}
