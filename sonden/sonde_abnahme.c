/* sonde_abnahme -- the date probe for the gate read `abnahme`.
 *
 * THE OBLIGATION (to be declared -- this probe stands AHEAD of it):
 *
 *     frist_abnahme_eingehalten (assume): falsifier sonde_abnahme
 *
 * for `abnahme` (`beispiele/06-annahmen.gab`:97):
 *
 *     impl fn abnahme()
 *         effects { reads kerne_gemessen }
 *         costs   <= 4 ops
 *
 * No `deadline` clause names this probe yet, so no falsifiable assumption
 * exists for it and `dokumente/SONDENDECKUNG.md` books it as an orphan until
 * the lane that dates the function arrives. This probe belongs to EXACTLY
 * that one future obligation (N024) and to no other.
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT ASSERT
 * ---------------------------------------------
 * ops != cycles and the tree refuses the conversion (D10). So this probe MUST
 * NOT assert the ops cost. It measures CYCLES of the emitted gate read (the
 * single load of the `kerne_gemessen` cell, replicated here in the same shape
 * and under the same `-O2`) and reports the distribution (min/p50/p99/max
 * over N iterations). Falsification enters through `--max-cycles C`: exit 1
 * iff p99 > C. The threshold C below is booked from a calibration run on this
 * machine plus a stated margin -- a measurement, not a derivation.
 *
 * BOOKED THRESHOLD (calibration 2026-09-10, workbench `Tux`, x86_64):
 *   N=20000, min 29 or 57, p50 31 or 61, p99 in {39,41,41,43,63} across five
 *   runs, max noisy (264-21570, scheduling tail -- which is why the verdict
 *   reads p99 and not max); checksum 2556394 every run. C=96 booked.
 * Margin rationale: C sits about half again above the worst measured p99
 * (63 -> 96). The bulk itself steps between two modes (min 29/57 -- core
 * frequency states, not cache effects), so the margin is read against the
 * SLOW mode (p50 61), not the fast one. A broken gate read at 10x lands near
 * 600, six times above C. C is a tripwire over THIS machine's distribution,
 * not a conversion of the 4 ops cost.
 *
 * WHAT IS TIMED, EXACTLY
 * ----------------------
 * Only the single global read. The fresh value written before each iteration
 * is the HARNESS (stimulus, outside the bracket), the way the refill is in
 * `sonde_tick`: the cell stays L1-resident, which is exactly the shape the
 * emitted gate read runs in -- the duty gate reads a live counter, not cold
 * memory.
 *
 * NOISE HONESTY
 * -------------
 * Machine: x86_64 workstation (`Tux`), no isolation, no realtime claims.
 * Clock: raw `RDTSC` bracketed by `LFENCE` (not a calibrated wall clock).
 * Warmup: 1000 untimed iterations before the measured window. Core pinning
 * is best-effort: failure prints a warning and the run continues, noisier.
 * Emulation or virtualization VOIDS these numbers (a virtual TSC need not
 * track retired cycles at all). A flaky red is a FAILED PROBE, not a failed
 * date -- re-run before reading anything into it.
 *
 * POSITIVE CONTROLS (R14)
 * -----------------------
 * The probe is made to fall via `--max-cycles 1` (no bracketed read runs in
 * 1 cycle; must exit 1), and the default run must pass (exit 0). Both runs
 * are documented below; a control that does not behave as stated makes the
 * probe blind and every green line worthless.
 *
 * Documented runs 2026-09-10 (`cc -std=c11 -O2 -Wall -Wextra -Werror`):
 *   $ ./sonde_abnahme
 *     -> exit 0, p99 in 39..63 <= 96 (default run PASSES)
 *   $ ./sonde_abnahme --max-cycles 1
 *     -> exit 1, p99 in 39..63 > 1 (positive control FALLS)
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
    printf("sonde sonde_abnahme :: frist_abnahme_eingehalten "
           "(UNBOUND -- beispiele/06 carries no deadline yet, see header)\n");
    printf("      no RDTSC on this architecture -- not runnable here\n");
    return 77;
}
#else

typedef unsigned long long u64;

/* The booked threshold: measured p99 plus margin, see the header. */
#define BOOKED_MAX_CYCLES 96ULL
/* Default window (N >= 10000) and the cap the runner's 2000000 rounds hit. */
#define DEFAULT_ITERS 20000L
#define MAX_ITERS 200000L
#define WARMUP 1000L
/* Fixed seed: fresh stimulus every iteration, reproducible distribution. */
#define SEED 0xab6abe06U

/* ---- The workload: the emitted gate read's shape, same `-O2`. ---- */

/* Mirrors `static mut kerne_gemessen : u32` (`beispiele/06-annahmen.gab`:123). */
static uint32_t kerne_gemessen;

static uint32_t lies_abnahme(void)
{
    return kerne_gemessen;
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
    printf("sonde sonde_abnahme :: frist_abnahme_eingehalten "
           "(UNBOUND -- beispiele/06 carries no deadline yet, see header; "
           "gate read costs <= 4 ops arch none)\n");

    long iters = DEFAULT_ITERS;
    u64 grenze = BOOKED_MAX_CYCLES;
    int grenze_gesetzt = 0;

    /* A bare number is the round count: `pruefe-sonden.sh` passes `$RUNDEN`
     * positionally, and the cap below keeps that run inside the 120 s Frist. */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--max-cycles") == 0 && i + 1 < argc) {
            long v = 0;
            if (dezimal(argv[++i], &v) != 0 || v < 1) {
                fprintf(stderr, "usage: sonde_abnahme [--iterations N] [--max-cycles C]\n");
                return 1;
            }
            grenze = (u64)v;
            grenze_gesetzt = 1;
        } else if (strcmp(argv[i], "--iterations") == 0 && i + 1 < argc) {
            if (dezimal(argv[++i], &iters) != 0) {
                fprintf(stderr, "usage: sonde_abnahme [--iterations N] [--max-cycles C]\n");
                return 1;
            }
        } else if (strcmp(argv[i], "--help") == 0) {
            printf("usage: sonde_abnahme [--iterations N] [--max-cycles C] [N]\n");
            return 0;
        } else {
            long v = 0;
            if (dezimal(argv[i], &v) != 0) {
                fprintf(stderr, "usage: sonde_abnahme [--iterations N] [--max-cycles C]\n");
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
        kerne_gemessen = naechste() & 1u;
        volatile uint32_t senke = lies_abnahme();
        (void)senke;
    }

    /* ---- The measured window. ---- */
    rng_state = SEED;
    u64 pruefsumme = 0;
    for (long i = 0; i < iters; i++) {
        /* Stimulus stays OUTSIDE the bracket: the fresh value is the harness,
         * not the date. Only the gate read itself is timed. */
        kerne_gemessen = naechste() & 1u;
        u64 t0 = lies_tsc();
        uint32_t v = lies_abnahme();
        u64 t1 = lies_tsc();
        delta[i] = t1 - t0;
        /* Kept observable: without the sum the loop is dead code under -O2. */
        pruefsumme += v + (uint32_t)(i & 0xffu);
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
    printf("      workload: single global read of `kerne_gemessen` (u32), fresh value\n");
    printf("      per iteration from a fixed-seed xorshift (harness, outside bracket)\n");
    printf("      cycles min %llu / p50 %llu / p99 %llu / max %llu  (checksum %llu)\n",
            cmin, p50, p99, cmax, pruefsumme);
    printf("      threshold --max-cycles %llu%s\n", grenze,
            grenze_gesetzt ? "" : " (booked default)");

    if (p99 > grenze) {
        printf("      REFUTED: p99 %llu exceeds --max-cycles %llu HERE, this time. A flaky\n",
                p99, grenze);
        printf("      red is a failed probe, not a failed date -- re-run first. The 4 ops\n");
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
