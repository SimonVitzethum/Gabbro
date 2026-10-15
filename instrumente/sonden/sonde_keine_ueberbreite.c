/* sonde_keine_ueberbreite -- the falsifier for `gleitkomma_x86_rechnet_mit_sse2`.
 *
 * THE ASSUMPTION, as `manifest.rs` GENERATES it -- and it stands in no `.gab` at all
 * (`crates/gabbro-check/src/manifest.rs`:121, an entry built whenever a float type appears):
 *
 *   "On x86 the generated code computes with SSE2 and not on the x87 stack. The x87 computes
 *    with 80 bits and ROUNDS TWICE; every bound the checker computed then fails to hold. The
 *    probe evaluates an expression whose result differs between 64 and 80 bits."
 *
 * `dokumente/SONDENDECKUNG.md` names the probe in the same words. This program is that
 * sentence, driven.
 *
 * THE EXPRESSION, AND WHY IT IS THAT ONE
 * --------------------------------------
 *     a = 1        b = 2^-53        c = 2^-53        d = (a + b) + c
 *
 * In 64-bit arithmetic each addition rounds: `a + b` is exactly halfway between 1 and
 * 1+2^-52, so round-to-nearest-EVEN gives 1; then `1 + c` is the same tie again and gives 1.
 * **d = 1.**
 *
 * In 80-bit arithmetic neither addition rounds at all -- 1+2^-53 and 1+2^-52 both fit in a
 * 64-bit mantissa -- and the single rounding on the way out to `double` is exact.
 * **d = 1 + 2^-52.**
 *
 * So one expression, two answers, and the difference is exactly the double rounding the
 * assumption is about. *No tolerance, no threshold, no statistics: the two results are not
 * near each other, they are different doubles.*
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT
 * --------------------------------------
 * It measures the **bench's C compiler on double arithmetic**, which is the environment fact
 * underneath the assumption: `instrumente/pruefe-emission.sh` compiles the emitted C with
 * exactly this `cc`, and if that compiler put double arithmetic on the x87 stack, the
 * emitted program would round twice no matter what the emitter wrote.
 *
 * It does NOT run `gabbro emit` and it does not read generated code -- `sonden/README.md`
 * forbids a probe that runs the checker, and the question of whether the EMITTER ever asks
 * for x87 belongs to the emitter's own tests. *What the probe can say is that the machine and
 * the toolchain underneath do not force over-width on it; what it cannot say is that no
 * translation unit ever turns it back on with a flag.*
 *
 * THE ARM THAT MAKES THE OTHER ONE READABLE
 * -----------------------------------------
 * A probe that finds nothing has two possible reasons: nothing was there, or it cannot see.
 * Here the second is the likely one -- an expression that came out the same on both widths
 * would look exactly like a machine that never uses 80 bits.
 *
 * Arm 1 is therefore the positive control and it runs FIRST: **the same expression, forced
 * onto the x87 stack by hand** (`fldl`/`faddp`/`fstpl`), which is the violated condition
 * itself and not an analogy. It MUST come out different from the 64-bit answer. *If it does
 * not, the expression cannot separate 64 bits from 80 on this machine, the detector is
 * blind, and the probe ends with 1 over itself* -- and it prints the x87 control word, so
 * the reader can see whether the precision field was the reason.
 *
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no x87, so there is nothing to be over-wide with
 */
#include <float.h>
#include <stdio.h>
#include <stdlib.h>

#if !defined(__x86_64__) && !defined(__i386__)
int main(void)
{
    printf("sonde sonde_keine_ueberbreite :: gleitkomma_x86_rechnet_mit_sse2\n");
    printf("      this is not an x86 -- the assumption names one, and there is no x87\n");
    printf("      stack here to be over-wide on. Not runnable here.\n");
    return 77;
}
#else

/* The expression as the compiler builds it. **`noinline` and `volatile` together**: without
 * the second the compiler folds it at translation time (and folds it in 64 bits, so the
 * probe would report the constant folder); without the first the loop below could hoist it. */
__attribute__((noinline)) static double summe_wie_gebaut(void)
{
    volatile double a = 1.0, b = 0x1p-53, c = 0x1p-53;
    return (a + b) + c;
}

/* **The same expression FORCED onto the x87 stack.** This is the violated condition itself:
 * two additions at the stack's precision, one store out to `double` at the end. */
__attribute__((noinline)) static double summe_auf_x87(void)
{
    volatile double a = 1.0, b = 0x1p-53, c = 0x1p-53;
    double r;
    __asm__ __volatile__("fldl %1\n\t"
                         "fldl %2\n\t"
                         "faddp %%st, %%st(1)\n\t"
                         "fldl %3\n\t"
                         "faddp %%st, %%st(1)\n\t"
                         "fstpl %0\n\t"
                         : "=m"(r)
                         : "m"(a), "m"(b), "m"(c)
                         : "st", "st(1)", "st(2)", "memory");
    return r;
}

static unsigned short x87_cw(void)
{
    unsigned short cw = 0;
    __asm__ __volatile__("fnstcw %0" : "=m"(cw));
    return cw;
}

/* Precision field of the x87 control word, bits 9:8. 0 = 24 bit, 2 = 53 bit, 3 = 64 bit. */
#define X87_PC(c) (((unsigned)(c) >> 8) & 3u)
static const char *pc_name[4] = { "24 bit", "reserved", "53 bit", "64 bit (extended)" };

int main(int argc, char **argv)
{
    printf("sonde sonde_keine_ueberbreite :: gleitkomma_x86_rechnet_mit_sse2 "
           "(manifest.rs:121, GENERATED -- it stands in no .gab)\n");

    /* **The round count is CAPPED and the cap stands in the output.** The runner hands down
     * the data-race probe's 2 000 000; a round here is two three-term sums. */
    long gewuenscht = (argc > 1) ? strtol(argv[1], NULL, 10) : 200000;
    if (gewuenscht < 1) {
        gewuenscht = 1;
    }
    const long DECKEL = 200000;
    long runden = (gewuenscht > DECKEL) ? DECKEL : gewuenscht;

    const double schmal = 1.0;              /* what 64-bit arithmetic must give */
    const double breit = 1.0 + 0x1p-52;     /* what 80-bit arithmetic gives */

    /* ---- Arm 1: the POSITIVE CONTROL. It runs first and it must differ EVERY round. ---- */
    long kontrolle_gefahren = 0, kontrolle_gefallen = 0, kontrolle_blind = 0;
    double x87_zeuge = 0.0;
    for (long r = 0; r < runden; r++) {
        double x = summe_auf_x87();
        kontrolle_gefahren++;
        if (x != schmal) {
            kontrolle_gefallen++;
            if (kontrolle_gefallen == 1) {
                x87_zeuge = x;
            }
        } else {
            kontrolle_blind++;
        }
    }

    /* ---- Arm 2: the expression as the toolchain builds it. ---- */
    long arm2 = 0, ueberbreit = 0, ganz_anders = 0;
    double zeuge = 0.0;
    for (long r = 0; r < runden; r++) {
        double d = summe_wie_gebaut();
        if (d == schmal) {
            arm2++;
        } else if (d == breit) {
            ueberbreit++;
            if (ueberbreit == 1) {
                zeuge = d;
                printf("      REFUTED: round %ld gave (1 + 2^-53) + 2^-53 = %.20g, which is\n",
                       r, d);
                printf("      the 80-bit answer. The arithmetic rounds TWICE.\n");
            }
        } else {
            ganz_anders++;
            if (ganz_anders == 1) {
                zeuge = d;
            }
        }
    }

    /* **The work set beside the verdict (W17).** A green run without a number beside it is
     * indistinguishable from an empty one. */
    printf("      rounds %ld (asked %ld, cap %ld)\n", runden, gewuenscht, DECKEL);
    printf("      FLT_EVAL_METHOD %d   x87 CW 0x%04x, PC %u (%s)\n", FLT_EVAL_METHOD,
           x87_cw(), X87_PC(x87_cw()), pc_name[X87_PC(x87_cw())]);
    printf("      64-bit answer %.20g   80-bit answer %.20g\n", schmal, breit);
    printf("      arm 1  forced onto the x87 stack, MUST differ -- ran %ld, differed %ld, "
           "agreed %ld\n", kontrolle_gefahren, kontrolle_gefallen, kontrolle_blind);
    if (kontrolle_gefallen > 0) {
        printf("             first x87 witness %.20g\n", x87_zeuge);
    }
    printf("      arm 2  as the toolchain builds it -- narrow %ld, over-wide %ld, neither "
           "%ld\n", arm2, ueberbreit, ganz_anders);
    if (ganz_anders > 0) {
        printf("             first witness that is neither: %.20g\n", zeuge);
    }

    if (kontrolle_blind > 0) {
        printf("      BLIND: the x87 arm agreed with the 64-bit answer %ld time(s). This\n",
               kontrolle_blind);
        printf("      expression cannot separate 64 bits from 80 on this machine -- see the\n");
        printf("      PC field above -- so arm 2 measured nothing and a green line there\n");
        printf("      would be indistinguishable from an empty run.\n");
        return 1;
    }
    if (ueberbreit > 0 || ganz_anders > 0) {
        printf("      REFUTED in %ld case(s). The generated code computes wider than 64\n",
               ueberbreit + ganz_anders);
        printf("      bits and rounds twice; every float bound the checker computed fails\n");
        printf("      to hold, and everything that stands on those bounds falls with them.\n");
        return 1;
    }
    printf("      not refuted -- and that is ALL it means. The control differed %ld times,\n",
           kontrolle_gefallen);
    printf("      so the expression does separate the two widths here; arm 2 stayed narrow,\n");
    printf("      so THIS toolchain does not put double arithmetic on the x87 stack. A\n");
    printf("      translation unit built with -mfpmath=387 would still do it.\n");
    return 0;
}
#endif
