/* sonde_mxcsr_rne -- the falsifier for `gleitkomma_rundungsmodus_ist_rne`.
 *
 * THE ASSUMPTION, as `manifest.rs` GENERATES it -- and it stands in no `.gab` at all
 * (`crates/gabbro-check/src/manifest.rs`:107, an entry built whenever a float type appears):
 *
 *   "The rounding mode is round-to-nearest-even. It is GLOBAL state (MXCSR/FPCR) and
 *    therefore an implicit input of every operation -- the probe reads it and falls if it is
 *    a different one."
 *
 * `dokumente/SONDENDECKUNG.md` names the probe in one line: *"read MXCSR, fall if the
 * rounding mode is not round-to-nearest-even."* This program is that line, driven -- and it
 * does a second half as well, because reading the register only answers what the register
 * SAYS. Whether the arithmetic OBEYS it is a different question, and both are here.
 *
 * WHAT IT MEASURES
 * ----------------
 * Two things, and they can disagree:
 *
 *   1. the declared mode -- the RC field of MXCSR (bits 14:13, `stmxcsr`) which governs SSE2,
 *      and the RC field of the x87 control word (bits 11:10, `fnstcw`) which governs the
 *      other unit. **Both**, because the assumption is about the mode an operation reads
 *      implicitly and there are two units that could read a different one;
 *   2. the mode the ARITHMETIC actually rounds in, read off two ties whose results differ
 *      between the four IEEE modes:
 *
 *        t1 = 1 + 2^-53               exactly halfway between 1 and 1+2^-52
 *        t2 = 1 + 2^-52 + 2^-53       exactly halfway between 1+2^-52 and 1+2^-51
 *
 *      Under round-to-nearest-EVEN, t1 = 1 (mantissa 0 is even) and t2 = 1+2^-51 (mantissa 2
 *      is even). Toward +inf moves t1; toward -inf and toward zero both move t2. **So the
 *      PAIR separates round-to-nearest-even from every other mode and neither tie alone
 *      does** -- t1 is blind to downward and to truncation, t2 is blind to upward.
 *
 * The operands are `volatile`. Without that the compiler folds both ties at translation
 * time, in ITS rounding mode, and the probe would report the compiler instead of the
 * machine -- a green line that means nothing (`W16`).
 *
 * WHY NO `<fenv.h>`
 * -----------------
 * `fegetround`/`fesetround` need `-lm`, and `instrumente/pruefe-sonden.sh` builds every probe
 * with one fixed set of flags that does not carry it. Reading the register directly is also
 * the more honest instrument: the assumption names MXCSR, and libc's view of it is one
 * indirection further away than the probe needs to be.
 *
 * WHAT IT DOES NOT MEASURE
 * ------------------------
 * It does not look at emitted Gabbro code. The assumption is about GLOBAL machine state that
 * every operation reads implicitly, and that state belongs to the process, not to a
 * translation unit. *What the probe cannot say is that generated code never sets the mode
 * itself* -- that would be a statement about the emitter and belongs to the checker.
 *
 * THE ARM THAT MAKES THE OTHERS READABLE
 * --------------------------------------
 * A probe that finds nothing has two possible reasons: nothing was there, or it cannot see.
 * Arm 1 is the positive control and it runs FIRST: the mode is deliberately set to each of
 * the three that violate the assumption, and the detector MUST report every single round of
 * every one of them. *If a violating mode goes through unseen, the detector is blind, every
 * green line below it is worthless, and the probe ends with 1 over itself.*
 *
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no MXCSR, or the mode cannot be set, so there is no control
 */
#include <float.h>
#include <stdio.h>
#include <stdlib.h>

#if !defined(__x86_64__) && !defined(__i386__)
int main(void)
{
    printf("sonde sonde_mxcsr_rne :: gleitkomma_rundungsmodus_ist_rne\n");
    printf("      no MXCSR on this architecture -- not runnable here\n");
    return 77;
}
#else

/* The two ties. **`noinline` and `volatile` together**: without the first they get inlined
 * into a loop the optimiser may hoist out of the mode changes, without the second they are
 * folded at translation time. Either way the probe would measure the compiler. */
struct ties {
    double t1;
    double t2;
};

__attribute__((noinline)) static struct ties messe_ties(void)
{
    volatile double eins = 1.0;
    volatile double halbes_ulp = 0x1p-53;         /* tie between 1 and 1+2^-52 */
    volatile double anderthalb_ulp = 0x1.8p-52;   /* tie between 1+2^-52 and 1+2^-51 */
    struct ties t;
    t.t1 = eins + halbes_ulp;
    t.t2 = eins + anderthalb_ulp;
    return t;
}

/* 1 = the arithmetic did NOT round to nearest-even, 0 = it did. */
static int rundet_nicht_rne(struct ties t)
{
    return !(t.t1 == 1.0 && t.t2 == 1.0 + 0x1p-51);
}

static unsigned mxcsr_lesen(void)
{
    unsigned m = 0;
    __asm__ __volatile__("stmxcsr %0" : "=m"(m));
    return m;
}

static void mxcsr_schreiben(unsigned m)
{
    __asm__ __volatile__("ldmxcsr %0" : : "m"(m));
}

static unsigned short x87_cw_lesen(void)
{
    unsigned short cw = 0;
    __asm__ __volatile__("fnstcw %0" : "=m"(cw));
    return cw;
}

static void x87_cw_schreiben(unsigned short cw)
{
    __asm__ __volatile__("fldcw %0" : : "m"(cw));
}

/* RC field of MXCSR, bits 14:13 -- and the identical encoding sits in the x87 control word
 * at bits 11:10. 0 = to nearest (even), 1 = down, 2 = up, 3 = toward zero. */
#define MXCSR_RC(m) (((m) >> 13) & 3u)
#define X87_RC(c) (((unsigned)(c) >> 10) & 3u)

static const char *rc_name[4] = { "to nearest even", "toward -inf", "toward +inf",
                                  "toward zero" };

int main(int argc, char **argv)
{
    printf("sonde sonde_mxcsr_rne :: gleitkomma_rundungsmodus_ist_rne (manifest.rs:107, "
           "GENERATED -- it stands in no .gab)\n");

    /* **The round count is CAPPED and the cap stands in the output.** The runner hands down
     * 2 000 000 -- that is the data-race probe's number, where a round costs two memory
     * accesses. Here a round costs two ties and two register reads, over four arms. */
    long gewuenscht = (argc > 1) ? strtol(argv[1], NULL, 10) : 200000;
    if (gewuenscht < 1) {
        gewuenscht = 1;
    }
    const long DECKEL = 200000;
    long runden = (gewuenscht > DECKEL) ? DECKEL : gewuenscht;

    unsigned mxcsr_start = mxcsr_lesen();
    unsigned short cw_start = x87_cw_lesen();

    /* Without the ability to SET the mode there is no positive control, and a green run
     * without a demonstrated detector is a reassurance and not a measurement. */
    mxcsr_schreiben((mxcsr_start & ~0x6000u) | (2u << 13));
    if (MXCSR_RC(mxcsr_lesen()) != 2u) {
        mxcsr_schreiben(mxcsr_start);
        printf("      MXCSR does not take a new RC field here -- no positive control is\n");
        printf("      possible, and a green run without one would measure nothing\n");
        return 77;
    }
    mxcsr_schreiben(mxcsr_start);

    /* ---- Arm 1: the POSITIVE CONTROL. It runs first and it must fall EVERY round. ---- */
    long kontrolle_gefallen = 0, kontrolle_gefahren = 0;
    long blind_bei[3] = { 0, 0, 0 };
    for (unsigned m = 1; m <= 3; m++) {
        mxcsr_schreiben((mxcsr_start & ~0x6000u) | (m << 13));
        for (long r = 0; r < runden; r++) {
            struct ties t = messe_ties();
            kontrolle_gefahren++;
            if (rundet_nicht_rne(t)) {
                kontrolle_gefallen++;
            } else {
                blind_bei[m - 1]++;
            }
        }
        mxcsr_schreiben(mxcsr_start);
    }

    /* ---- Arm 1b: the same control over the OTHER register. The x87 reading is a second
     * detector, and an unchecked second detector is an ornament. ---- */
    long x87_kontrolle = 0;
    for (unsigned m = 1; m <= 3; m++) {
        x87_cw_schreiben((unsigned short)((cw_start & (unsigned short)~0x0c00u)
                                          | (unsigned short)(m << 10)));
        if (X87_RC(x87_cw_lesen()) == m) {
            x87_kontrolle++;
        }
        x87_cw_schreiben(cw_start);
    }

    /* ---- Arm 2: the assumption itself. ---- */
    long arm2 = 0, verletzt_arithmetik = 0, verletzt_mxcsr = 0, verletzt_x87 = 0;
    for (long r = 0; r < runden; r++) {
        struct ties t = messe_ties();
        if (MXCSR_RC(mxcsr_lesen()) != 0u) {
            verletzt_mxcsr++;
        }
        if (X87_RC(x87_cw_lesen()) != 0u) {
            verletzt_x87++;
        }
        if (rundet_nicht_rne(t)) {
            verletzt_arithmetik++;
            if (verletzt_arithmetik == 1) {
                printf("      REFUTED: round %ld rounded 1+2^-53 to %.20g and "
                       "1+2^-52+2^-53 to %.20g\n", r, t.t1, t.t2);
            }
        } else {
            arm2++;
        }
    }

    /* **The work set beside the verdict (W17).** A green run without a number beside it is
     * indistinguishable from an empty one. */
    unsigned mxcsr_ende = mxcsr_lesen();
    unsigned short cw_ende = x87_cw_lesen();
    printf("      rounds %ld (asked %ld, cap %ld)\n", runden, gewuenscht, DECKEL);
    printf("      FLT_EVAL_METHOD %d\n", FLT_EVAL_METHOD);
    printf("      MXCSR 0x%04x, RC %u (%s)\n", mxcsr_ende, MXCSR_RC(mxcsr_ende),
           rc_name[MXCSR_RC(mxcsr_ende)]);
    printf("      x87 CW 0x%04x, RC %u (%s)\n", cw_ende, X87_RC(cw_ende),
           rc_name[X87_RC(cw_ende)]);
    printf("      arm 1  three violating modes, MUST fall -- ran %ld, fell %ld\n",
           kontrolle_gefahren, kontrolle_gefallen);
    for (unsigned m = 1; m <= 3; m++) {
        printf("             %-16s unseen in %ld of %ld rounds\n", rc_name[m],
               blind_bei[m - 1], runden);
    }
    printf("      arm 1b x87 control word takes all three modes -- %ld of 3\n", x87_kontrolle);
    printf("      arm 2  the mode as it stands  -- held %ld, MXCSR said no %ld, x87 said no "
           "%ld, arithmetic said no %ld\n", arm2, verletzt_mxcsr, verletzt_x87,
           verletzt_arithmetik);

    if (kontrolle_gefallen != kontrolle_gefahren || x87_kontrolle != 3) {
        printf("      BLIND: the positive control went unseen %ld time(s) on MXCSR and the\n",
               kontrolle_gefahren - kontrolle_gefallen);
        printf("      x87 word took %ld of 3 modes. A violating mode passed the detector,\n",
               x87_kontrolle);
        printf("      so every green line above is worthless -- the probe is not reading\n");
        printf("      the state it claims to read.\n");
        return 1;
    }
    if (verletzt_mxcsr > 0 || verletzt_x87 > 0 || verletzt_arithmetik > 0) {
        printf("      REFUTED: %ld MXCSR and %ld x87 reading(s), and %ld arithmetic\n",
               verletzt_mxcsr, verletzt_x87, verletzt_arithmetik);
        printf("      result(s), say the mode is not round-to-nearest-even. Every float\n");
        printf("      bound the checker computed rests on this assumption and falls with it.\n");
        return 1;
    }
    printf("      not refuted -- and that is ALL it means. The control fell %ld times, so\n",
           kontrolle_gefallen);
    printf("      the detector has sensitivity; the mode held HERE, THIS TIME, in THIS\n");
    printf("      process. A library loaded later may still set it.\n");
    return 0;
}
#endif
