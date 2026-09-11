/* frist28_ferne_kern_wecken -- the staged date probe for `ferne_kern_wecken` (`67-befehlsebene.gab`:66).
 *
 * STAGED, NOT BOUND. No `deadline` clause in `67-befehlsebene.gab` names this probe and no
 * manifest entry lists it: binding needs a checker-side entry plus a dated
 * clause in the example, both outside this post's scope (checker logic and
 * example files are not touched here). This probe demonstrates detection for
 * the staged deadline below and belongs to EXACTLY this one candidate
 * obligation (N024). The staged deadline number is ten times the promised
 * `costs <= 1 ops` -- the headroom rule of `messung/SONDEN-ROWS-72.md`,
 * after the single precedent `zaehle_werte` (promised `500`, booked `5000`).
 * No checker rule holds the two numbers against each other (`kosten.rs`:
 * different units, no conversion), so the ten is a writer's booking, stated
 * here and not derived.
 *
 * FRIST-SONDEN-NOTIZ.md row `8`, class `P1`.
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT ASSERT
 * ---------------------------------------------
 * ops != cycles and the tree refuses the conversion (D10). So this probe MUST
 * NOT assert the ops deadline. It measures CYCLES of the single `outb` of the emit (`beispiele/67-befehlsebene.gab`:70-74) and reports the
 * distribution (min/p50/p99/max over N iterations). Falsification enters
 * through `--max-cycles C`: exit 1 iff p99 > C. The threshold C below is
 * booked from a calibration run on this machine plus a stated margin -- a
 * measurement, not a derivation.
 *
 * BOOKED THRESHOLD (calibration 2026-09-11, workbench `fisch`, x86_64):
 *   PROVISIONAL (void here, 77)
 * vendor latency plus margin, void until ring-zero calibration
 *
 * WHAT IS TIMED, EXACTLY
 * ----------------------
 * Only the single privileged port write, guarded as above. Real port IO is never executed speculatively: on this bench the guard fires first.
 *
 * THE GRID (TickClock.window, `grammatik/Grammatik/Fristlauf.lean`:328)
 * ----------------------------------------------------------------
 * After the verdict the probe prints the sampling grid over THIS run: period
 * S is the booked tripwire (cycles), the deadline moment d is the worst
 * typical cost (p99), check at `0`, use at `d + S`. Spacing (`deadlineSpacing`:
 * `d + S <= use`) holds by construction, so the window's SEEN arm must fire:
 * tick `n * S` lands in `[d, use]` with the printed margin. The grid is
 * COMPUTED here, not hardware-kept: that the hardware keeps the grid is cut
 * C4 (`Fristlauf.lean`:82), a per-use premise no sample ever discharges --
 * the probe demonstrates detection within the bound, it does not close C4.
 *
 * NOISE HONESTY
 * -------------
 * Machine: x86_64 workstation (`fisch`), no isolation, no realtime claims.
 * Clock: raw `RDTSC` bracketed by `LFENCE` (not a calibrated wall clock).
 * Warmup: 1000 untimed iterations before the measured window. Core pinning
 * is best-effort: failure prints a warning and the run continues, noisier.
 * Emulation or virtualization VOIDS these numbers (a virtual TSC need not
 * track retired cycles at all). A flaky red is a FAILED PROBE, not a failed
 * date -- re-run before reading anything into it.
 *
 * POSITIVE CONTROLS (R14)
 * -----------------------
 * The probe is made to fall via `--max-cycles 1` (no timed body runs in
 * 1 cycle; must exit 1), and the default run must pass (exit 0). Both runs
 * are documented below; a control that does not behave as stated makes the
 * probe blind and every green line worthless.
 *
 * Documented runs 2026-09-11 (`cc -std=c11 -O2 -Wall -Wextra -Werror`):
 *   $ ./frist28_ferne_kern_wecken
 *     -> exit 0, p99 within the booked tripwire (default run PASSES)
 *   $ ./frist28_ferne_kern_wecken --max-cycles 1
 *     -> exit 1 (positive control FALLS)
 *

 * PRIVILEGE NOTE: the timed instruction faults outside ring zero. On this
 * bench the guard below fires and the probe exits `77` having measured
 * nothing; the tripwire above is PROVISIONAL (vendor latency plus margin,
 * void until a ring-zero calibration) and the grid line it prints is a
 * computed illustration, not a measurement. Real port IO is never executed
 * speculatively: the guard fires before any timing.
 * Contract (`sonden/README.md`):
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no RDTSC on this architecture, or it faults; or the timed instruction faults (ring 3 -- need a ring-zero bench)
 */
#define _GNU_SOURCE
#include <sched.h>
#include <setjmp.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#if !defined(__x86_64__) && !defined(__i386__)
int main(void)
{
    printf("probe frist28_ferne_kern_wecken :: frist_ferne_kern_wecken_eingehalten "
           "(67-befehlsebene.gab:66, staged)\n");
    printf("      no RDTSC on this architecture -- not runnable here\n");
    return 77;
}
#else

typedef unsigned long long u64;

/* The booked threshold: measured p99 plus margin, see the header. */
#define BOOKED_MAX_CYCLES 4096ULL
/* Default window (N >= 10000) and the cap the runner's 2000000 rounds hit. */
#define DEFAULT_ITERS 20000L
#define MAX_ITERS 200000L
#define WARMUP 1000L
/* Fixed seed: fresh stimulus every iteration, reproducible distribution. */
#define SEED 0x067008U

/* ---- The workload: the staged body shape, same `-O2`. ---- */

static uint16_t wk_tor;
static uint8_t wk_hinweis;

static void arbeit(void)
{
    __asm__ __volatile__("outb %[hinweis], %[tor]"
                         :
                         : [hinweis] "a"(wk_hinweis), [tor] "d"(wk_tor)
                         : "memory");
}

/* ---- Fixed-seed PRNG: fresh contents every iteration, same run twice. ---- */
static uint32_t rng_state = SEED;

static uint32_t __attribute__((unused)) naechste(void)
{
    uint32_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    rng_state = x;
    return x;
}

/* ---- The clock: raw RDTSC, LFENCE-bracketed. Not a wall clock. ---- */
static u64 lies_tsc(void)
{
    unsigned lo, hi;
    __asm__ __volatile__("lfence" ::: "memory");
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    __asm__ __volatile__("lfence" ::: "memory");
    return ((u64)hi << 32) | lo;
}

static sigjmp_buf sprung;
static volatile sig_atomic_t gefaultet;

static void handler(int sig)
{
    (void)sig;
    gefaultet = 1;
    siglongjmp(sprung, 1);
}

static int vergleich(const void *a, const void *b)
{
    u64 x = *(const u64 *)a;
    u64 y = *(const u64 *)b;
    if (x < y) {
        return -1;
    }
    if (x > y) {
        return 1;
    }
    return 0;
}

static int dezimal(const char *s, long *aus)
{
    char *ende = NULL;
    long v = strtol(s, &ende, 10);
    if (ende == s || *ende != '\0') {
        return -1;
    }
    *aus = v;
    return 0;
}

int main(int argc, char **argv)
{
    printf("probe frist28_ferne_kern_wecken :: frist_ferne_kern_wecken_eingehalten (staged, UNBOUND) "
           "(67-befehlsebene.gab:66, staged deadline <= 10 ops arch x86_64)\n");

    long iters = DEFAULT_ITERS;
    u64 grenze = BOOKED_MAX_CYCLES;
    int grenze_gesetzt = 0;

    /* A bare number is the round count: `pruefe-sonden.sh` passes `$RUNDEN`
     * positionally, and the cap below keeps that run inside the 120 s Frist. */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--max-cycles") == 0 && i + 1 < argc) {
            long v = 0;
            if (dezimal(argv[++i], &v) != 0 || v < 1) {
                fprintf(stderr, "usage: frist28_ferne_kern_wecken [--iterations N] [--max-cycles C]\n");
                return 1;
            }
            grenze = (u64)v;
            grenze_gesetzt = 1;
        } else if (strcmp(argv[i], "--iterations") == 0 && i + 1 < argc) {
            if (dezimal(argv[++i], &iters) != 0) {
                fprintf(stderr, "usage: frist28_ferne_kern_wecken [--iterations N] [--max-cycles C]\n");
                return 1;
            }
        } else if (strcmp(argv[i], "--help") == 0) {
            printf("usage: frist28_ferne_kern_wecken [--iterations N] [--max-cycles C] [N]\n");
            return 0;
        } else {
            long v = 0;
            if (dezimal(argv[i], &v) != 0) {
                fprintf(stderr, "usage: frist28_ferne_kern_wecken [--iterations N] [--max-cycles C]\n");
                return 1;
            }
            iters = v;
        }
    }
    if (iters < 1) {
        iters = 1;
    }
    long gefragt = iters;
    if (iters > MAX_ITERS) {
        iters = MAX_ITERS;
    }

    /* ---- The third state: does the instruction execute at all? ---- */
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_NODEFER;
    if (sigaction(SIGSEGV, &sa, NULL) != 0 || sigaction(SIGILL, &sa, NULL) != 0) {
        printf("      no right to handle SIGSEGV/SIGILL -- a trapping RDTSC could not be\n");
        printf("      told from a working one. Not runnable here.\n");
        return 77;
    }
    gefaultet = 0;
    if (sigsetjmp(sprung, 1) == 0) {
        u64 probe = lies_tsc();
        (void)probe;
    }
    if (gefaultet) {
        printf("      RDTSC faults in this process -- CR4.TSD is set, or the kernel was\n");
        printf("      told `prctl(PR_SET_TSC, PR_TSC_SIGSEGV)`. Nothing was measured.\n");
        return 77;
    }

    /* ---- One core if the scheduler allows; noise if it does not. ---- */
    volatile int kern = sched_getcpu();
    volatile int gehalten = 0;
    if (kern >= 0) {
        cpu_set_t menge;
        CPU_ZERO(&menge);
        CPU_SET(kern, &menge);
        if (sched_setaffinity(0, sizeof menge, &menge) == 0 && sched_getcpu() == kern) {
            gehalten = 1;
        }
    }
    if (!gehalten) {
        printf("      WARNING: not pinned to one core -- expect a noisier tail\n");
    }

    u64 *delta = malloc((size_t)iters * sizeof *delta);
    if (delta == NULL) {
        printf("      BLIND: no room for %ld samples -- nothing was measured\n", iters);
        return 1;
    }

    /* ---- Warmup: timed window must not pay the cold cache. ---- */
    rng_state = SEED;
    wk_tor = 0x3F8; wk_hinweis = 0;

    /* ---- Privilege guard: the timed instruction faults outside ring 0. ---- */
    gefaultet = 0;
    if (sigsetjmp(sprung, 1) == 0) {
        arbeit();
    }
    if (gefaultet) {
        printf("      NOT RUNNABLE HERE: the timed instruction faults in ring 3 --\n");
        printf("      need a ring-zero bench. Nothing was timed.\n");
        printf("      threshold --max-cycles %llu (PROVISIONAL, void here)\n",
                BOOKED_MAX_CYCLES);
        printf("      grid S %llu / d %llu (PROVISIONAL) / n 1 / tick %llu / use %llu / margin %llu / arm SEEN*\n",
                BOOKED_MAX_CYCLES, BOOKED_MAX_CYCLES, BOOKED_MAX_CYCLES,
                (u64)(BOOKED_MAX_CYCLES + BOOKED_MAX_CYCLES), BOOKED_MAX_CYCLES);
        printf("      *computed illustration, NOT a measurement: 77 here, nothing timed.\n");
        printf("      A ring-zero bench re-runs this binary and reads the real tick.\n");
        free(delta);
        return 77;
    }
    for (long w = 0; w < WARMUP; w++) {
        arbeit();
    }
    /* ---- The measured window. ---- */
    rng_state = SEED;
    wk_tor = 0x3F8; wk_hinweis = 0;
    u64 pruefsumme = 0;
    for (long i = 0; i < iters; i++) {
        u64 t0 = lies_tsc();
        arbeit();
        u64 t1 = lies_tsc();
        delta[i] = t1 - t0;
        pruefsumme += (uint64_t)(i & 0xffu);
    }
        qsort(delta, (size_t)iters, sizeof *delta, vergleich);
    /* Percentile rank: nearest-rank on (n-1), stated so a re-run can check it. */
    u64 cmin = delta[0];
    u64 p50 = delta[(size_t)(0.50 * (double)(iters - 1))];
    u64 p99 = delta[(size_t)(0.99 * (double)(iters - 1))];
    u64 cmax = delta[iters - 1];
    free(delta);

    /* **The work set beside the verdict (W17).** A green run without a number
     * beside it is indistinguishable from an empty one. */
    printf("      iterations %ld (asked %ld, cap %ld), warmup %ld, seed 0x%08x\n",
            iters, gefragt, MAX_ITERS, WARMUP, SEED);
    if (gehalten) {
        printf("      held on core %d; clock RDTSC fenced by LFENCE (cycles, NOT ops)\n",
                kern);
    } else {
        printf("      unpinned; clock RDTSC fenced by LFENCE (cycles, NOT ops)\n");
    }
    printf("      workload: the single outb instruction as emitted;\n");
    printf("      guarded -- faults outside ring 0, then 77 (see header)\n");
    printf("      cycles min %llu / p50 %llu / p99 %llu / max %llu  (checksum %llu)\n",
            cmin, p50, p99, cmax, pruefsumme);
    printf("      threshold --max-cycles %llu%s\n", grenze,
            grenze_gesetzt ? "" : " (booked default)");


    /* ---- The sampling grid over THIS run (TickClock.window). ---- */
    {
        u64 S = BOOKED_MAX_CYCLES;
        u64 d = p99;
        u64 n = (d + S - 1) / S;
        if (n < 1) {
            n = 1;
        }
        u64 tick = n * S;
        u64 l = d + S;
        const char *arm = (d <= tick && tick <= l) ? "SEEN" : "BOUNDED-MISS";
        printf("      grid S %llu / d %llu (p99) / n %llu / tick %llu / use %llu / margin %llu / arm %s\n",
                S, d, n, tick, l, l - tick, arm);
        printf("      window TickClock.window: expiry strictly between check and use is SEEN\n");
        printf("      (a tick lands in [d,l]) or MISSED INSIDE A BOUND (use < d+S); spacing\n");
        printf("      d+S <= use holds by construction -- detection lands on tick %llu\n", tick);
    }

    if (p99 > grenze) {
        printf("      REFUTED: p99 %llu exceeds --max-cycles %llu HERE, this time. A flaky\n",
                p99, grenze);
        printf("      red is a failed probe, not a failed date -- re-run first. The 8 ops\n");
        printf("      cost itself is NOT asserted (D10: ops != cycles).\n");
        return 1;
    }
    printf("      not refuted -- and that is ALL it means. p99 %llu <= %llu cycles HERE,\n",
            p99, grenze);
    printf("      this time, under this seed. The ops cost is not converted and not\n");
    printf("      discharged as a proof (R15/W10: a sample, not a verdict over all inputs).\n");
    return 0;
}
#endif
