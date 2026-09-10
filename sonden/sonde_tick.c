/* sonde_tick -- the falsifier for `frist_zaehle_werte_eingehalten`.
 *
 * THE OBLIGATION, as the checker declares it in the generated header
 * (`gabbro emit beispiele/71-frist-und-zaehlung.gab`):
 *
 *     frist_zaehle_werte_eingehalten (assume): falsifier sonde_tick
 *
 * and in the source (`beispiele/71-frist-und-zaehlung.gab`:29):
 *
 *     deadline <= 5000 ops arch x86_64 falsifier sonde_tick
 *
 * on `zaehle_werte`. This probe belongs to EXACTLY this one obligation (N024).
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT ASSERT
 * ---------------------------------------------
 * ops != cycles and the tree refuses the conversion (D10). So this probe MUST
 * NOT assert the ops deadline. It measures CYCLES of the generated counter
 * (`zaehle_1193` in the emit: the 16-slot traversal with the predicate
 * `benutzt && wert >= schwelle`, replicated here in the same shape and under
 * the same `-O2`) and reports the distribution (min/p50/p99/max over N
 * iterations). Falsification enters through `--max-cycles C`: exit 1 iff
 * p99 > C. The threshold C below is booked from a calibration run on this
 * machine plus a stated margin -- a measurement, not a derivation.
 *
 * BOOKED THRESHOLD (calibration 2026-09-10, workbench `fisch`, x86_64):
 *   N=20000, min~115, p50~252, p99~338, max noisy (12k-619k across runs,
 *   scheduling tail -- which is why the verdict reads p99 and not max);
 *   five runs, p99 in {337,337,338,339,339}, checksum 2627689 every run.
 *   C=512 booked.
 * Margin rationale: C sits ~50% above the measured p99 (~340 -> 512), clear
 * of the bulk (p50~252) and of routine jitter, but an order of magnitude
 * below anything a broken traversal could hide in (a 10x slowdown lands near
 * 2500). C is a tripwire over THIS machine's distribution, not a conversion
 * of the 5000 ops date.
 *
 * WHAT IS TIMED, EXACTLY
 * ----------------------
 * Only the counting traversal. The lock acquire/release (`P_nimm`/`P_gib`)
 * is EXCLUDED: the bench provides no `P` implementation, and timing a local
 * stub would be an analogy (forbidden by `sonden/README.md`). A green run
 * therefore says nothing about lock cost; it says the counter body holds
 * its cycle budget here, this time.
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
 * The probe is made to fall via `--max-cycles 1` (no 16-slot traversal runs
 * in 1 cycle; must exit 1), and the default run must pass (exit 0). Both
 * runs are documented below; a control that does not behave as stated makes
 * the probe blind and every green line worthless.
 *
 * Documented runs 2026-09-10 (`cc -std=c11 -O2 -Wall -Wextra -Werror`):
 *   $ ./sonde_tick
 *     -> exit 0, p99~338 <= 512 (default run PASSES)
 *   $ ./sonde_tick --max-cycles 1
 *     -> exit 1, p99~338 > 1 (positive control FALLS)
 *
 * Contract (`sonden/README.md`):
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no RDTSC on this architecture, or it faults
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
    printf("sonde sonde_tick :: frist_zaehle_werte_eingehalten "
           "(beispiele/71-frist-und-zaehlung.gab:29)\n");
    printf("      no RDTSC on this architecture -- not runnable here\n");
    return 77;
}
#else

typedef unsigned long long u64;

/* The booked threshold: measured p99 plus margin, see the header. */
#define BOOKED_MAX_CYCLES 512ULL
/* Default window (N >= 10000) and the cap the runner's 2000000 rounds hit. */
#define DEFAULT_ITERS 20000L
#define MAX_ITERS 200000L
#define WARMUP 1000L
/* Fixed seed: randomized contents, reproducible distribution. */
#define SEED 0x71f8157dU

/* ---- The workload: the emitted counter's shape, same `-O2`. ---- */
#define NSLOTS 16u

typedef struct {
    bool benutzt;
    uint32_t wert;
} slot_t;

static slot_t plaetze[NSLOTS];

/* Mirrors `zaehle_1193`: predicate is the writer's logic, traversal the
 * template's. Locking is outside the bracket by design (see header). */
static uint32_t zaehle(uint32_t schwelle)
{
    uint32_t acc = 0;
    for (uint32_t k = 0;
         k < (uint32_t)(sizeof plaetze / sizeof plaetze[0]); k++) {
        if (plaetze[k].benutzt && plaetze[k].wert >= schwelle) {
            acc += 1;
        }
    }
    return acc;
}

/* ---- Fixed-seed PRNG: fresh contents every iteration, same run twice. ---- */
static uint32_t rng_state = SEED;

static uint32_t naechste(void)
{
    uint32_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    rng_state = x;
    return x;
}

static void fuelle(void)
{
    for (uint32_t k = 0; k < NSLOTS; k++) {
        uint32_t r = naechste();
        plaetze[k].benutzt = (r & 1u) != 0;
        plaetze[k].wert = (r >> 1) % 101u;
    }
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
    printf("sonde sonde_tick :: frist_zaehle_werte_eingehalten "
           "(beispiele/71-frist-und-zaehlung.gab:29, deadline <= 5000 ops arch x86_64)\n");

    long iters = DEFAULT_ITERS;
    u64 grenze = BOOKED_MAX_CYCLES;
    int grenze_gesetzt = 0;

    /* A bare number is the round count: `pruefe-sonden.sh` passes `$RUNDEN`
     * positionally, and the cap below keeps that run inside the 120 s Frist. */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--max-cycles") == 0 && i + 1 < argc) {
            long v = 0;
            if (dezimal(argv[++i], &v) != 0 || v < 1) {
                fprintf(stderr, "usage: sonde_tick [--iterations N] [--max-cycles C]\n");
                return 1;
            }
            grenze = (u64)v;
            grenze_gesetzt = 1;
        } else if (strcmp(argv[i], "--iterations") == 0 && i + 1 < argc) {
            if (dezimal(argv[++i], &iters) != 0) {
                fprintf(stderr, "usage: sonde_tick [--iterations N] [--max-cycles C]\n");
                return 1;
            }
        } else if (strcmp(argv[i], "--help") == 0) {
            printf("usage: sonde_tick [--iterations N] [--max-cycles C] [N]\n");
            return 0;
        } else {
            long v = 0;
            if (dezimal(argv[i], &v) != 0) {
                fprintf(stderr, "usage: sonde_tick [--iterations N] [--max-cycles C]\n");
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
    int kern = sched_getcpu();
    int gehalten = 0;
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
    for (long w = 0; w < WARMUP; w++) {
        fuelle();
        uint32_t schwelle = naechste() % 101u;
        volatile uint32_t senke = zaehle(schwelle);
        (void)senke;
    }

    /* ---- The measured window. ---- */
    rng_state = SEED;
    u64 pruefsumme = 0;
    for (long i = 0; i < iters; i++) {
        /* Stimulus stays OUTSIDE the bracket: refill and threshold choice are
         * the harness, not the date. Only the counter body is timed. */
        fuelle();
        uint32_t schwelle = naechste() % 101u;
        u64 t0 = lies_tsc();
        uint32_t n = zaehle(schwelle);
        u64 t1 = lies_tsc();
        delta[i] = t1 - t0;
        /* Kept observable: without the sum the loop is dead code under -O2. */
        pruefsumme += n + (uint32_t)(i & 0xffu);
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
    printf("      workload: 16-slot count `benutzt && wert >= schwelle`, refilled per\n");
    printf("      iteration from a fixed-seed xorshift; locks EXCLUDED (see header)\n");
    printf("      cycles min %llu / p50 %llu / p99 %llu / max %llu  (checksum %llu)\n",
            cmin, p50, p99, cmax, pruefsumme);
    printf("      threshold --max-cycles %llu%s\n", grenze,
            grenze_gesetzt ? "" : " (booked default)");

    if (p99 > grenze) {
        printf("      REFUTED: p99 %llu exceeds --max-cycles %llu HERE, this time. A flaky\n",
                p99, grenze);
        printf("      red is a failed probe, not a failed date -- re-run first. The 5000 ops\n");
        printf("      deadline itself is NOT asserted (D10: ops != cycles).\n");
        return 1;
    }
    printf("      not refuted -- and that is ALL it means. p99 %llu <= %llu cycles HERE,\n",
            p99, grenze);
    printf("      this time, under this seed. The ops deadline is not converted and not\n");
    printf("      discharged as a proof (R15/W10: a sample, not a verdict over all inputs).\n");
    return 0;
}
#endif
