/* sonde_tsc -- the falsifier for the axiom `rdtsc`.
 *
 * THE ASSUMPTION, as the corpus declares it in one line
 * (`beispiele/06-annahmen.gab`:82):
 *
 *     axiom rdtsc()           effects { reads zeitzaehler }                falsifier sonde_tsc;
 *
 * The effect clause is the whole content: `rdtsc` READS A TIME COUNTER. A counter that
 * stands still is not one, and a counter that runs backwards is not one either -- so those
 * are the two shapes this probe looks for, and they are the two its controls force.
 *
 * `dokumente/SONDENDECKUNG.md` names the probe in one line: *"read the counter twice and
 * fall if it does not advance; 77 if `CR4.TSD` forbids it."* This program is that line,
 * driven, with the second failure shape added because a monotone check that only looks
 * forward cannot see a step back.
 *
 * WHAT IT MEASURES, AND WHY IT PINS A CORE FIRST
 * ----------------------------------------------
 * It measures ONE core's counter. `sched_setaffinity` holds the probe on the CPU it started
 * on, and **if that fails the probe returns 77 rather than running**: on a machine whose
 * per-core counters are not synchronised, a thread migrating between reads sees a step
 * backwards that says nothing about `rdtsc` and everything about the scheduler. *A red line
 * that could mean either is not a finding, and a probe that cannot exclude the second
 * reading has not measured the first.*
 *
 * It does NOT measure whether the counter tracks wall time at a constant rate -- the axiom
 * says `reads zeitzaehler` and not `reads a constant-rate clock`. The observed rate against
 * `CLOCK_MONOTONIC` is printed as data, not as a verdict.
 *
 * THE THIRD STATE, AND IT IS REAL HERE
 * ------------------------------------
 * `CR4.TSD` makes `RDTSC` privileged; Linux exposes the same switch to userland as
 * `prctl(PR_SET_TSC, PR_TSC_SIGSEGV)`. Where it is set, the instruction faults, and this
 * probe returns **77** -- *not runnable here*, which `sonden/README.md` makes a full member
 * of the contract. **A probe that returned 0 there would be reporting a green run over an
 * instruction it never executed.**
 *
 * THE ARMS THAT MAKE THE THIRD ONE READABLE
 * -----------------------------------------
 * A probe that finds nothing has two possible reasons: nothing was there, or it cannot see.
 * The counter is read through a FUNCTION POINTER, and arms 1 and 2 run the identical
 * detector over two sources that violate the assumption by construction: one frozen, one
 * running backwards. **Both must be caught in every round.** *If either goes through, the
 * detector is blind, every green line below it is worthless, and the probe ends with 1 over
 * itself.*
 *
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no rdtsc, no core to hold, or CR4.TSD forbids it
 */
#define _GNU_SOURCE
#include <sched.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#if !defined(__x86_64__) && !defined(__i386__)
int main(void)
{
    printf("sonde sonde_tsc :: rdtsc (beispiele/06-annahmen.gab:82)\n");
    printf("      no RDTSC on this architecture -- not runnable here\n");
    return 77;
}
#else

typedef unsigned long long u64;

static sigjmp_buf sprung;
static volatile sig_atomic_t gefaultet;

static void handler(int sig)
{
    (void)sig;
    gefaultet = 1;
    siglongjmp(sprung, 1);
}

static u64 q_rdtsc(void)
{
    unsigned lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((u64)hi << 32) | lo;
}

/* **The two sources that violate the assumption by construction.** They are not analogies of
 * a broken counter, they ARE one -- the program itself promises the failure, so the detector
 * has nothing to be lucky about. */
static u64 q_eingefroren(void)
{
    static volatile u64 fest = 0x0123456789abcdefULL;
    return fest;
}

static u64 q_rueckwaerts(void)
{
    static volatile u64 zaehler = 0xffffffffffffff00ULL;
    zaehler -= 16u;
    return zaehler;
}

/* How many reads one round may spend waiting for the counter to move. A real counter needs
 * one; a frozen one never gets there however long the limit is. */
#define GRENZE 64

struct befund {
    long stillstand;   /* the counter never moved within GRENZE reads */
    long rueckwaerts;  /* a read came out BELOW the one before it */
    long vorgerueckt;  /* it advanced, as the axiom says it must */
    long max_lesungen; /* the worst round's read count -- the work set of the wait */
};

static void pruefe_quelle(u64 (*quelle)(void), long runden, struct befund *b)
{
    memset(b, 0, sizeof *b);
    for (long r = 0; r < runden; r++) {
        u64 v0 = quelle();
        long n = 1;
        int rueck = 0, vor = 0;
        for (; n <= GRENZE; n++) {
            u64 v = quelle();
            if (v < v0) {
                rueck = 1;
                break;
            }
            if (v > v0) {
                vor = 1;
                break;
            }
        }
        if (n > b->max_lesungen) {
            b->max_lesungen = n;
        }
        if (rueck) {
            b->rueckwaerts++;
        } else if (vor) {
            b->vorgerueckt++;
        } else {
            b->stillstand++;
        }
    }
}

int main(int argc, char **argv)
{
    printf("sonde sonde_tsc :: rdtsc -- effects { reads zeitzaehler } "
           "(beispiele/06-annahmen.gab:82)\n");

    /* **The round count is CAPPED and the cap stands in the output.** A control round costs
     * up to GRENZE reads, so the runner's 2 000 000 would be 128 million of them. */
    long gewuenscht = (argc > 1) ? strtol(argv[1], NULL, 10) : 200000;
    if (gewuenscht < 1) {
        gewuenscht = 1;
    }
    const long DECKEL = 200000;
    long runden = (gewuenscht > DECKEL) ? DECKEL : gewuenscht;

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
        u64 probe = q_rdtsc();
        (void)probe;
    }
    if (gefaultet) {
        printf("      RDTSC faults in this process -- CR4.TSD is set, or the kernel was\n");
        printf("      told `prctl(PR_SET_TSC, PR_TSC_SIGSEGV)`. The instruction cannot be\n");
        printf("      executed here, so nothing about the counter was measured.\n");
        return 77;
    }

    /* ---- One core, or nothing. See the head of this file. ---- */
    int kern = sched_getcpu();
    cpu_set_t menge;
    CPU_ZERO(&menge);
    if (kern < 0) {
        printf("      the running core cannot be named -- a step backwards could not be\n");
        printf("      told from a migration. Not runnable here.\n");
        return 77;
    }
    CPU_SET(kern, &menge);
    if (sched_setaffinity(0, sizeof menge, &menge) != 0 || sched_getcpu() != kern) {
        printf("      this thread cannot be held on core %d -- a step backwards could not\n",
               kern);
        printf("      be told from a migration between two unsynchronised counters.\n");
        printf("      Not runnable here.\n");
        return 77;
    }

    /* ---- Arms 1 and 2: the POSITIVE CONTROLS. They run first and must be caught. ---- */
    struct befund frost, rueck;
    pruefe_quelle(q_eingefroren, runden, &frost);
    pruefe_quelle(q_rueckwaerts, runden, &rueck);

    /* ---- Arm 3: the axiom itself. ---- */
    struct timespec t0, t1;
    int uhr_da = (clock_gettime(CLOCK_MONOTONIC, &t0) == 0);
    u64 vor = q_rdtsc();
    struct befund echt;
    pruefe_quelle(q_rdtsc, runden, &echt);
    u64 nach = q_rdtsc();
    uhr_da = uhr_da && (clock_gettime(CLOCK_MONOTONIC, &t1) == 0);

    /* **The work set beside the verdict (W17).** A green run without a number beside it is
     * indistinguishable from an empty one. */
    printf("      rounds %ld per arm (asked %ld, cap %ld), up to %d reads per round\n",
           runden, gewuenscht, DECKEL, GRENZE);
    printf("      held on core %d\n", kern);
    printf("      arm 1  FROZEN source, MUST be caught     -- standstill %ld, backwards %ld, "
           "advanced %ld\n", frost.stillstand, frost.rueckwaerts, frost.vorgerueckt);
    printf("      arm 2  BACKWARD source, MUST be caught   -- standstill %ld, backwards %ld, "
           "advanced %ld\n", rueck.stillstand, rueck.rueckwaerts, rueck.vorgerueckt);
    printf("      arm 3  rdtsc                             -- standstill %ld, backwards %ld, "
           "advanced %ld (worst wait %ld reads)\n", echt.stillstand, echt.rueckwaerts,
           echt.vorgerueckt, echt.max_lesungen);
    if (uhr_da) {
        double s = (double)(t1.tv_sec - t0.tv_sec)
                   + 1e-9 * (double)(t1.tv_nsec - t0.tv_nsec);
        printf("      the counter moved %llu ticks in %.6f s against CLOCK_MONOTONIC "
               "(%.3f MHz) -- reported, not judged\n", nach - vor, s,
               s > 0.0 ? (double)(nach - vor) / s / 1e6 : 0.0);
    }

    if (frost.stillstand != runden || rueck.rueckwaerts != runden) {
        printf("      BLIND: the frozen source was caught in %ld of %ld rounds and the\n",
               frost.stillstand, runden);
        printf("      backward one in %ld of %ld. A counter that violates the axiom by\n",
               rueck.rueckwaerts, runden);
        printf("      construction got past this detector, so arm 3 measured nothing and\n");
        printf("      its green line is worthless.\n");
        return 1;
    }
    if (echt.stillstand > 0 || echt.rueckwaerts > 0) {
        printf("      REFUTED: rdtsc stood still in %ld round(s) and went backwards in %ld.\n",
               echt.stillstand, echt.rueckwaerts);
        printf("      `effects { reads zeitzaehler }` is not what this instruction does on\n");
        printf("      this machine, and every duty measured against it falls with it.\n");
        return 1;
    }
    printf("      not refuted -- and that is ALL it means. The controls were caught %ld and\n",
           frost.stillstand);
    printf("      %ld times, so the detector has sensitivity; rdtsc advanced in all %ld\n",
           rueck.rueckwaerts, echt.vorgerueckt);
    printf("      rounds HERE, on core %d, THIS time. Another core's counter is another\n",
           kern);
    printf("      measurement, and this probe did not make it.\n");
    return 0;
}
#endif
